import V185TrunkScan23Chunk1265

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7499968 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2]
def baseStart_7499968 : Nat := 118140960795 + 7499968 * 2 ^ 59
def prefixEnd_7499968 : Nat := 4983230072969 + 3 ^ 40 * 7499968 * 2
def baseEnd_7499968 : Nat := 3851088477339817574408281

theorem tailTrace_7499968 : CollatzResearch.WordTrace tailWord_7499968 prefixEnd_7499968 3851088477339817574408281 := by
  unfold tailWord_7499968
  simp only [CollatzResearch.WordTrace]
  refine ⟨136773152846452151701222279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182364203795269535601629705 136773152846452151701222279)
  ·
    refine ⟨205159729269678227551833419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136773152846452151701222279 205159729269678227551833419)
    ·
      refine ⟨307739593904517341327750129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205159729269678227551833419 307739593904517341327750129)
      ·
        refine ⟨230804695428388005995812597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307739593904517341327750129 230804695428388005995812597)
        ·
          refine ⟨21637940196411375562107431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230804695428388005995812597 21637940196411375562107431)
          ·
            refine ⟨32456910294617063343161147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21637940196411375562107431 32456910294617063343161147)
            ·
              refine ⟨48685365441925595014741721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32456910294617063343161147 48685365441925595014741721)
              ·
                refine ⟨36514024081444196261056291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48685365441925595014741721 36514024081444196261056291)
                ·
                  refine ⟨54771036122166294391584437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36514024081444196261056291 54771036122166294391584437)
                  ·
                    refine ⟨5134784636453090099211041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54771036122166294391584437 5134784636453090099211041)
                    ·
                      refine ⟨3851088477339817574408281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134784636453090099211041 3851088477339817574408281)
                      ·
                        rfl

theorem cell23_7499968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_7499968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499968 prefixEnd_7499968 := by exact prefixLift 7499968
  have htrace : WordTrace (prefixWord ++ tailWord_7499968) baseStart_7499968 baseEnd_7499968 := by
    simpa [prefixWord, tailWord_7499968, baseEnd_7499968] using wordTrace_append hprefix tailTrace_7499968
  have hstable : (prefixWord ++ tailWord_7499968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499968).length < 2 ^ (prefixWord ++ tailWord_7499968).sum := by decide
  have hdescent : baseEnd_7499968 < baseStart_7499968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499978 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_7499978 : Nat := 118140960795 + 7499978 * 2 ^ 59
def prefixEnd_7499978 : Nat := 4983230072969 + 3 ^ 40 * 7499978 * 2
def baseEnd_7499978 : Nat := 1283697870715454178427745

theorem tailTrace_7499978 : CollatzResearch.WordTrace tailWord_7499978 prefixEnd_7499978 1283697870715454178427745 := by
  unfold tailWord_7499978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68386667605717018777577147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182364446948578716740205725 68386667605717018777577147)
  ·
    refine ⟨102580001408575528166365721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68386667605717018777577147 102580001408575528166365721)
    ·
      refine ⟨76935001056431646124774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102580001408575528166365721 76935001056431646124774291)
      ·
        refine ⟨115402501584647469187161437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76935001056431646124774291 115402501584647469187161437)
        ·
          refine ⟨43275938094242800945185539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115402501584647469187161437 43275938094242800945185539)
          ·
            refine ⟨64913907141364201417778309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43275938094242800945185539 64913907141364201417778309)
            ·
              refine ⟨12171357589005787765833433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64913907141364201417778309 12171357589005787765833433)
              ·
                refine ⟨9128518191754340824375075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12171357589005787765833433 9128518191754340824375075)
                ·
                  refine ⟨13692777287631511236562613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9128518191754340824375075 13692777287631511236562613)
                  ·
                    refine ⟨1283697870715454178427745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13692777287631511236562613 1283697870715454178427745)
                    ·
                      rfl

theorem cell23_7499978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_7499978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499978 prefixEnd_7499978 := by exact prefixLift 7499978
  have htrace : WordTrace (prefixWord ++ tailWord_7499978) baseStart_7499978 baseEnd_7499978 := by
    simpa [prefixWord, tailWord_7499978, baseEnd_7499978] using wordTrace_append hprefix tailTrace_7499978
  have hstable : (prefixWord ++ tailWord_7499978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499978).length < 2 ^ (prefixWord ++ tailWord_7499978).sum := by decide
  have hdescent : baseEnd_7499978 < baseStart_7499978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7499992 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_7499992 : Nat := 118140960795 + 7499992 * 2 ^ 59
def prefixEnd_7499992 : Nat := 4983230072969 + 3 ^ 40 * 7499992 * 2
def baseEnd_7499992 : Nat := 3851100800875525480508171

theorem tailTrace_7499992 : CollatzResearch.WordTrace tailWord_7499992 prefixEnd_7499992 3851100800875525480508171 := by
  unfold tailWord_7499992
  simp only [CollatzResearch.WordTrace]
  refine ⟨136773590522408677750659115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182364787363211570334212153 136773590522408677750659115)
  ·
    refine ⟨205160385783613016625988673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136773590522408677750659115 205160385783613016625988673)
    ·
      refine ⟨153870289337709762469491505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205160385783613016625988673 153870289337709762469491505)
      ·
        refine ⟨115402717003282321852118629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153870289337709762469491505 115402717003282321852118629)
        ·
          refine ⟨21638009438115435347272243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115402717003282321852118629 21638009438115435347272243)
          ·
            refine ⟨32457014157173153020908365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21638009438115435347272243 32457014157173153020908365)
            ·
              refine ⟨12171380308939932382840637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32457014157173153020908365 12171380308939932382840637)
              ·
                refine ⟨4564267615852474643565239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171380308939932382840637 4564267615852474643565239)
                ·
                  refine ⟨6846401423778711965347859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564267615852474643565239 6846401423778711965347859)
                  ·
                    refine ⟨10269602135668067948021789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846401423778711965347859 10269602135668067948021789)
                    ·
                      refine ⟨3851100800875525480508171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269602135668067948021789 3851100800875525480508171)
                      ·
                        rfl

theorem cell23_7499992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_7499992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7499992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7499992 prefixEnd_7499992 := by exact prefixLift 7499992
  have htrace : WordTrace (prefixWord ++ tailWord_7499992) baseStart_7499992 baseEnd_7499992 := by
    simpa [prefixWord, tailWord_7499992, baseEnd_7499992] using wordTrace_append hprefix tailTrace_7499992
  have hstable : (prefixWord ++ tailWord_7499992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7499992).length < 2 ^ (prefixWord ++ tailWord_7499992).sum := by decide
  have hdescent : baseEnd_7499992 < baseStart_7499992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7499992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500008 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7500008 : Nat := 118140960795 + 7500008 * 2 ^ 59
def prefixEnd_7500008 : Nat := 4983230072969 + 3 ^ 40 * 7500008 * 2
def baseEnd_7500008 : Nat := 1283703005521999139302699

theorem tailTrace_7500008 : CollatzResearch.WordTrace tailWord_7500008 prefixEnd_7500008 1283703005521999139302699 := by
  unfold tailWord_7500008
  simp only [CollatzResearch.WordTrace]
  refine ⟨136773882306379695116950339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182365176408506260155933785 136773882306379695116950339)
  ·
    refine ⟨205160823459569542675425509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136773882306379695116950339 205160823459569542675425509)
    ·
      refine ⟨38467654398669289251642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205160823459569542675425509 38467654398669289251642283)
      ·
        refine ⟨57701481598003933877463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38467654398669289251642283 57701481598003933877463425)
        ·
          refine ⟨43276111198502950408097569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57701481598003933877463425 43276111198502950408097569)
          ·
            refine ⟨32457083398877212806073177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43276111198502950408097569 32457083398877212806073177)
            ·
              refine ⟨24342812549157909604554883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32457083398877212806073177 24342812549157909604554883)
              ·
                refine ⟨36514218823736864406832325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24342812549157909604554883 36514218823736864406832325)
                ·
                  refine ⟨6846416029450662076281061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36514218823736864406832325 6846416029450662076281061)
                  ·
                    refine ⟨1283703005521999139302699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846416029450662076281061 1283703005521999139302699)
                    ·
                      rfl

theorem cell23_7500008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7500008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500008 prefixEnd_7500008 := by exact prefixLift 7500008
  have htrace : WordTrace (prefixWord ++ tailWord_7500008) baseStart_7500008 baseEnd_7500008 := by
    simpa [prefixWord, tailWord_7500008, baseEnd_7500008] using wordTrace_append hprefix tailTrace_7500008
  have hstable : (prefixWord ++ tailWord_7500008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500008).length < 2 ^ (prefixWord ++ tailWord_7500008).sum := by decide
  have hdescent : baseEnd_7500008 < baseStart_7500008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500018 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7500018 : Nat := 118140960795 + 7500018 * 2 ^ 59
def prefixEnd_7500018 : Nat := 4983230072969 + 3 ^ 40 * 7500018 * 2
def baseEnd_7500018 : Nat := 3851114151372542378783051

theorem tailTrace_7500018 : CollatzResearch.WordTrace tailWord_7500018 prefixEnd_7500018 3851114151372542378783051 := by
  unfold tailWord_7500018
  simp only [CollatzResearch.WordTrace]
  refine ⟨68387032335680790485441177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182365419561815441294509805 68387032335680790485441177)
  ·
    refine ⟨51290274251760592864080883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68387032335680790485441177 51290274251760592864080883)
    ·
      refine ⟨76935411377640889296121325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51290274251760592864080883 76935411377640889296121325)
      ·
        refine ⟨28850779266615333486045497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76935411377640889296121325 28850779266615333486045497)
        ·
          refine ⟨21638084449961500114534123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28850779266615333486045497 21638084449961500114534123)
          ·
            refine ⟨32457126674942250171801185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21638084449961500114534123 32457126674942250171801185)
            ·
              refine ⟨24342845006206687628850889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32457126674942250171801185 24342845006206687628850889)
              ·
                refine ⟨18257133754655015721638167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24342845006206687628850889 18257133754655015721638167)
                ·
                  refine ⟨27385700631982523582457251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18257133754655015721638167 27385700631982523582457251)
                  ·
                    refine ⟨41078550947973785373685877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27385700631982523582457251 41078550947973785373685877)
                    ·
                      refine ⟨3851114151372542378783051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41078550947973785373685877 3851114151372542378783051)
                      ·
                        rfl

theorem cell23_7500018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7500018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500018 prefixEnd_7500018 := by exact prefixLift 7500018
  have htrace : WordTrace (prefixWord ++ tailWord_7500018) baseStart_7500018 baseEnd_7500018 := by
    simpa [prefixWord, tailWord_7500018, baseEnd_7500018] using wordTrace_append hprefix tailTrace_7500018
  have hstable : (prefixWord ++ tailWord_7500018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500018).length < 2 ^ (prefixWord ++ tailWord_7500018).sum := by decide
  have hdescent : baseEnd_7500018 < baseStart_7500018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500065 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_7500065 : Nat := 118140960795 + 7500065 * 2 ^ 59
def prefixEnd_7500065 : Nat := 4983230072969 + 3 ^ 40 * 7500065 * 2
def baseEnd_7500065 : Nat := 3851138284963303694895335

theorem tailTrace_7500065 : CollatzResearch.WordTrace tailWord_7500065 prefixEnd_7500065 3851138284963303694895335 := by
  unfold tailWord_7500065
  simp only [CollatzResearch.WordTrace]
  refine ⟨273549843573552888968725649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182366562382368592645817099 273549843573552888968725649)
  ·
    refine ⟨205162382680164666726544237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273549843573552888968725649 205162382680164666726544237)
    ·
      refine ⟨76935893505061750022454089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205162382680164666726544237 76935893505061750022454089)
      ·
        refine ⟨57701920128796312516840567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76935893505061750022454089 57701920128796312516840567)
        ·
          refine ⟨86552880193194468775260851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57701920128796312516840567 86552880193194468775260851)
          ·
            refine ⟨129829320289791703162891277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86552880193194468775260851 129829320289791703162891277)
            ·
              refine ⟨48685995108671888686084229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129829320289791703162891277 48685995108671888686084229)
              ·
                refine ⟨9128624082875979128640793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48685995108671888686084229 9128624082875979128640793)
                ·
                  refine ⟨6846468062156984346480595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128624082875979128640793 6846468062156984346480595)
                  ·
                    refine ⟨10269702093235476519720893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846468062156984346480595 10269702093235476519720893)
                    ·
                      refine ⟨3851138284963303694895335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269702093235476519720893 3851138284963303694895335)
                      ·
                        rfl

theorem cell23_7500065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_7500065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500065 prefixEnd_7500065 := by exact prefixLift 7500065
  have htrace : WordTrace (prefixWord ++ tailWord_7500065) baseStart_7500065 baseEnd_7500065 := by
    simpa [prefixWord, tailWord_7500065, baseEnd_7500065] using wordTrace_append hprefix tailTrace_7500065
  have hstable : (prefixWord ++ tailWord_7500065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500065).length < 2 ^ (prefixWord ++ tailWord_7500065).sum := by decide
  have hdescent : baseEnd_7500065 < baseStart_7500065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500066 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_7500066 : Nat := 118140960795 + 7500066 * 2 ^ 59
def prefixEnd_7500066 : Nat := 4983230072969 + 3 ^ 40 * 7500066 * 2
def baseEnd_7500066 : Nat := 3851138798443958190982831

theorem tailTrace_7500066 : CollatzResearch.WordTrace tailWord_7500066 prefixEnd_7500066 3851138798443958190982831 := by
  unfold tailWord_7500066
  simp only [CollatzResearch.WordTrace]
  refine ⟨68387470011637316534878013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182366586697699510759674701 68387470011637316534878013)
  ·
    refine ⟨25645301254363993700579255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68387470011637316534878013 25645301254363993700579255)
    ·
      refine ⟨38467951881545990550868883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645301254363993700579255 38467951881545990550868883)
      ·
        refine ⟨57701927822318985826303325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38467951881545990550868883 57701927822318985826303325)
        ·
          refine ⟨21638222933369619684863747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57701927822318985826303325 21638222933369619684863747)
          ·
            refine ⟨32457334400054429527295621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21638222933369619684863747 32457334400054429527295621)
            ·
              refine ⟨6085750200010205536367929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32457334400054429527295621 6085750200010205536367929)
              ·
                refine ⟨4564312650007654152275947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6085750200010205536367929 4564312650007654152275947)
                ·
                  refine ⟨6846468975011481228413921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564312650007654152275947 6846468975011481228413921)
                  ·
                    refine ⟨5134851731258610921310441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846468975011481228413921 5134851731258610921310441)
                    ·
                      refine ⟨3851138798443958190982831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134851731258610921310441 3851138798443958190982831)
                      ·
                        rfl

theorem cell23_7500066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_7500066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500066 prefixEnd_7500066 := by exact prefixLift 7500066
  have htrace : WordTrace (prefixWord ++ tailWord_7500066) baseStart_7500066 baseEnd_7500066 := by
    simpa [prefixWord, tailWord_7500066, baseEnd_7500066] using wordTrace_append hprefix tailTrace_7500066
  have hstable : (prefixWord ++ tailWord_7500066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500066).length < 2 ^ (prefixWord ++ tailWord_7500066).sum := by decide
  have hdescent : baseEnd_7500066 < baseStart_7500066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500105 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 4, 2, 2]
def baseStart_7500105 : Nat := 118140960795 + 7500105 * 2 ^ 59
def prefixEnd_7500105 : Nat := 4983230072969 + 3 ^ 40 * 7500105 * 2
def baseEnd_7500105 : Nat := 3851158824189483538395151

theorem tailTrace_7500105 : CollatzResearch.WordTrace tailWord_7500105 prefixEnd_7500105 3851158824189483538395151 := by
  unfold tailWord_7500105
  simp only [CollatzResearch.WordTrace]
  refine ⟨273551302493407975800181769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182367534995605317200121179 273551302493407975800181769)
  ·
    refine ⟨205163476870055981850136327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273551302493407975800181769 205163476870055981850136327)
    ·
      refine ⟨307745215305083972775204491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205163476870055981850136327 307745215305083972775204491)
      ·
        refine ⟨461617822957625959162806737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307745215305083972775204491 461617822957625959162806737)
        ·
          refine ⟨346213367218219469372105053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461617822957625959162806737 346213367218219469372105053)
          ·
            refine ⟨129830012706832301014539395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346213367218219469372105053 129830012706832301014539395)
            ·
              refine ⟨194745019060248451521809093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129830012706832301014539395 194745019060248451521809093)
              ·
                refine ⟨36514691073796584660339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194745019060248451521809093 36514691073796584660339205)
                ·
                  refine ⟨6846504576336859623813601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36514691073796584660339205 6846504576336859623813601)
                  ·
                    refine ⟨5134878432252644717860201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846504576336859623813601 5134878432252644717860201)
                    ·
                      refine ⟨3851158824189483538395151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5134878432252644717860201 3851158824189483538395151)
                      ·
                        rfl

theorem cell23_7500105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2, 2].length) (baseStart_7500105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500105 prefixEnd_7500105 := by exact prefixLift 7500105
  have htrace : WordTrace (prefixWord ++ tailWord_7500105) baseStart_7500105 baseEnd_7500105 := by
    simpa [prefixWord, tailWord_7500105, baseEnd_7500105] using wordTrace_append hprefix tailTrace_7500105
  have hstable : (prefixWord ++ tailWord_7500105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500105).length < 2 ^ (prefixWord ++ tailWord_7500105).sum := by decide
  have hdescent : baseEnd_7500105 < baseStart_7500105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500151 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_7500151 : Nat := 118140960795 + 7500151 * 2 ^ 59
def prefixEnd_7500151 : Nat := 4983230072969 + 3 ^ 40 * 7500151 * 2
def baseEnd_7500151 : Nat := 3851182444299590358419939

theorem tailTrace_7500151 : CollatzResearch.WordTrace tailWord_7500151 prefixEnd_7500151 3851182444299590358419939 := by
  unfold tailWord_7500151
  simp only [CollatzResearch.WordTrace]
  refine ⟨273552980251241325656356307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182368653500827550437570871 273552980251241325656356307)
  ·
    refine ⟨410329470376861988484534461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273552980251241325656356307 410329470376861988484534461)
    ·
      refine ⟨153873551391323245681700423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410329470376861988484534461 153873551391323245681700423)
      ·
        refine ⟨230810327086984868522550635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153873551391323245681700423 230810327086984868522550635)
        ·
          refine ⟨346215490630477302783825953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230810327086984868522550635 346215490630477302783825953)
          ·
            refine ⟨259661617972857977087869465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346215490630477302783825953 259661617972857977087869465)
            ·
              refine ⟨194746213479643482815902099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259661617972857977087869465 194746213479643482815902099)
              ·
                refine ⟨292119320219465224223853149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194746213479643482815902099 292119320219465224223853149)
                ·
                  refine ⟨109544745082299459083944931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292119320219465224223853149 109544745082299459083944931)
                  ·
                    refine ⟨164317117623449188625917397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109544745082299459083944931 164317117623449188625917397)
                    ·
                      refine ⟨3851182444299590358419939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164317117623449188625917397 3851182444299590358419939)
                      ·
                        rfl

theorem cell23_7500151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_7500151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500151 prefixEnd_7500151 := by exact prefixLift 7500151
  have htrace : WordTrace (prefixWord ++ tailWord_7500151) baseStart_7500151 baseEnd_7500151 := by
    simpa [prefixWord, tailWord_7500151, baseEnd_7500151] using wordTrace_append hprefix tailTrace_7500151
  have hstable : (prefixWord ++ tailWord_7500151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500151).length < 2 ^ (prefixWord ++ tailWord_7500151).sum := by decide
  have hdescent : baseEnd_7500151 < baseStart_7500151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500168 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7500168 : Nat := 118140960795 + 7500168 * 2 ^ 59
def prefixEnd_7500168 : Nat := 4983230072969 + 3 ^ 40 * 7500168 * 2
def baseEnd_7500168 : Nat := 3851191173470716791907361

theorem tailTrace_7500168 : CollatzResearch.WordTrace tailWord_7500168 prefixEnd_7500168 3851191173470716791907361 := by
  unfold tailWord_7500168
  simp only [CollatzResearch.WordTrace]
  refine ⟨136776800146089868779862579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182369066861453158373150105 136776800146089868779862579)
  ·
    refine ⟨205165200219134803169793869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136776800146089868779862579 205165200219134803169793869)
    ·
      refine ⟨76936950082175551188672701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205165200219134803169793869 76936950082175551188672701)
      ·
        refine ⟨28851356280815831695752263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76936950082175551188672701 28851356280815831695752263)
        ·
          refine ⟨43277034421223747543628395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28851356280815831695752263 43277034421223747543628395)
          ·
            refine ⟨64915551631835621315442593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43277034421223747543628395 64915551631835621315442593)
            ·
              refine ⟨48686663723876715986581945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64915551631835621315442593 48686663723876715986581945)
              ·
                refine ⟨36514997792907536989936459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48686663723876715986581945 36514997792907536989936459)
                ·
                  refine ⟨54772496689361305484904689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36514997792907536989936459 54772496689361305484904689)
                  ·
                    refine ⟨41079372517020979113678517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54772496689361305484904689 41079372517020979113678517)
                    ·
                      refine ⟨3851191173470716791907361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41079372517020979113678517 3851191173470716791907361)
                      ·
                        rfl

theorem cell23_7500168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7500168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500168 prefixEnd_7500168 := by exact prefixLift 7500168
  have htrace : WordTrace (prefixWord ++ tailWord_7500168) baseStart_7500168 baseEnd_7500168 := by
    simpa [prefixWord, tailWord_7500168, baseEnd_7500168] using wordTrace_append hprefix tailTrace_7500168
  have hstable : (prefixWord ++ tailWord_7500168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500168).length < 2 ^ (prefixWord ++ tailWord_7500168).sum := by decide
  have hdescent : baseEnd_7500168 < baseStart_7500168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500215 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_7500215 : Nat := 118140960795 + 7500215 * 2 ^ 59
def prefixEnd_7500215 : Nat := 4983230072969 + 3 ^ 40 * 7500215 * 2
def baseEnd_7500215 : Nat := 3851215307061478108019645

theorem tailTrace_7500215 : CollatzResearch.WordTrace tailWord_7500215 prefixEnd_7500215 3851215307061478108019645 := by
  unfold tailWord_7500215
  simp only [CollatzResearch.WordTrace]
  refine ⟨273555314523009464586686099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182370209682006309724457399 273555314523009464586686099)
  ·
    refine ⟨410332971784514196880029149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273555314523009464586686099 410332971784514196880029149)
    ·
      refine ⟨153874864419192823830010931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410332971784514196880029149 153874864419192823830010931)
      ·
        refine ⟨230812296628789235745016397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153874864419192823830010931 230812296628789235745016397)
        ·
          refine ⟨86554611235795963404381149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230812296628789235745016397 86554611235795963404381149)
          ·
            refine ⟨32457979213423486276642931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86554611235795963404381149 32457979213423486276642931)
            ·
              refine ⟨48686968820135229414964397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32457979213423486276642931 48686968820135229414964397)
              ·
                refine ⟨18257613307550711030611649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48686968820135229414964397 18257613307550711030611649)
                ·
                  refine ⟨13693209980663033272958737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18257613307550711030611649 13693209980663033272958737)
                  ·
                    refine ⟨10269907485497274954719053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13693209980663033272958737 10269907485497274954719053)
                    ·
                      refine ⟨3851215307061478108019645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10269907485497274954719053 3851215307061478108019645)
                      ·
                        rfl

theorem cell23_7500215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_7500215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500215 prefixEnd_7500215 := by exact prefixLift 7500215
  have htrace : WordTrace (prefixWord ++ tailWord_7500215) baseStart_7500215 baseEnd_7500215 := by
    simpa [prefixWord, tailWord_7500215, baseEnd_7500215] using wordTrace_append hprefix tailTrace_7500215
  have hstable : (prefixWord ++ tailWord_7500215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500215).length < 2 ^ (prefixWord ++ tailWord_7500215).sum := by decide
  have hdescent : baseEnd_7500215 < baseStart_7500215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500238 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7500238 : Nat := 118140960795 + 7500238 * 2 ^ 59
def prefixEnd_7500238 : Nat := 4983230072969 + 3 ^ 40 * 7500238 * 2
def baseEnd_7500238 : Nat := 3851227117116531518032039

theorem tailTrace_7500238 : CollatzResearch.WordTrace tailWord_7500238 prefixEnd_7500238 3851227117116531518032039 := by
  unfold tailWord_7500238
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194519175240767439346671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182370768934617426343182245 34194519175240767439346671)
  ·
    refine ⟨51291778762861151159020007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34194519175240767439346671 51291778762861151159020007)
    ·
      refine ⟨76937668144291726738530011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51291778762861151159020007 76937668144291726738530011)
      ·
        refine ⟨115406502216437590107795017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76937668144291726738530011 115406502216437590107795017)
        ·
          refine ⟨86554876662328192580846263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115406502216437590107795017 86554876662328192580846263)
          ·
            refine ⟨129832314993492288871269395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86554876662328192580846263 129832314993492288871269395)
            ·
              refine ⟨194748472490238433306904093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129832314993492288871269395 194748472490238433306904093)
              ·
                refine ⟨73030677183839412490089035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194748472490238433306904093 73030677183839412490089035)
                ·
                  refine ⟨109546015775759118735133553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73030677183839412490089035 109546015775759118735133553)
                  ·
                    refine ⟨82159511831819339051350165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109546015775759118735133553 82159511831819339051350165)
                    ·
                      refine ⟨3851227117116531518032039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82159511831819339051350165 3851227117116531518032039)
                      ·
                        rfl

theorem cell23_7500238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7500238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500238 prefixEnd_7500238 := by exact prefixLift 7500238
  have htrace : WordTrace (prefixWord ++ tailWord_7500238) baseStart_7500238 baseEnd_7500238 := by
    simpa [prefixWord, tailWord_7500238, baseEnd_7500238] using wordTrace_append hprefix tailTrace_7500238
  have hstable : (prefixWord ++ tailWord_7500238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500238).length < 2 ^ (prefixWord ++ tailWord_7500238).sum := by decide
  have hdescent : baseEnd_7500238 < baseStart_7500238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500288 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_7500288 : Nat := 118140960795 + 7500288 * 2 ^ 59
def prefixEnd_7500288 : Nat := 4983230072969 + 3 ^ 40 * 7500288 * 2
def baseEnd_7500288 : Nat := 3851252791149256322406809

theorem tailTrace_7500288 : CollatzResearch.WordTrace tailWord_7500288 prefixEnd_7500288 3851252791149256322406809 := by
  unfold tailWord_7500288
  simp only [CollatzResearch.WordTrace]
  refine ⟨136778988525872499027046759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182371984701163332036062345 136778988525872499027046759)
  ·
    refine ⟨205168482788808748540570139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136778988525872499027046759 205168482788808748540570139)
    ·
      refine ⟨307752724183213122810855209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205168482788808748540570139 307752724183213122810855209)
      ·
        refine ⟨230814543137409842108141407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307752724183213122810855209 230814543137409842108141407)
        ·
          refine ⟨346221814706114763162212111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230814543137409842108141407 346221814706114763162212111)
          ·
            refine ⟨519332722059172144743318167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346221814706114763162212111 519332722059172144743318167)
            ·
              refine ⟨778999083088758217114977251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519332722059172144743318167 778999083088758217114977251)
              ·
                refine ⟨1168498624633137325672465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778999083088758217114977251 1168498624633137325672465877)
                ·
                  refine ⟨27386686514839156070448419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1168498624633137325672465877 27386686514839156070448419)
                  ·
                    refine ⟨41080029772258734105672629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27386686514839156070448419 41080029772258734105672629)
                    ·
                      refine ⟨3851252791149256322406809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41080029772258734105672629 3851252791149256322406809)
                      ·
                        rfl

theorem cell23_7500288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_7500288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500288 prefixEnd_7500288 := by exact prefixLift 7500288
  have htrace : WordTrace (prefixWord ++ tailWord_7500288) baseStart_7500288 baseEnd_7500288 := by
    simpa [prefixWord, tailWord_7500288, baseEnd_7500288] using wordTrace_append hprefix tailTrace_7500288
  have hstable : (prefixWord ++ tailWord_7500288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500288).length < 2 ^ (prefixWord ++ tailWord_7500288).sum := by decide
  have hdescent : baseEnd_7500288 < baseStart_7500288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500305 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_7500305 : Nat := 118140960795 + 7500305 * 2 ^ 59
def prefixEnd_7500305 : Nat := 4983230072969 + 3 ^ 40 * 7500305 * 2
def baseEnd_7500305 : Nat := 3851261520320382755894231

theorem tailTrace_7500305 : CollatzResearch.WordTrace tailWord_7500305 prefixEnd_7500305 3851261520320382755894231 := by
  unfold tailWord_7500305
  simp only [CollatzResearch.WordTrace]
  refine ⟨273558597092683409957462369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182372398061788939971641579 273558597092683409957462369)
  ·
    refine ⟨205168947819512557468096777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273558597092683409957462369 205168947819512557468096777)
    ·
      refine ⟨153876710864634418101072583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205168947819512557468096777 153876710864634418101072583)
      ·
        refine ⟨230815066296951627151608875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153876710864634418101072583 230815066296951627151608875)
        ·
          refine ⟨346222599445427440727413313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230815066296951627151608875 346222599445427440727413313)
          ·
            refine ⟨259666949584070580545559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346222599445427440727413313 259666949584070580545559985)
            ·
              refine ⟨194750212188052935409169989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259666949584070580545559985 194750212188052935409169989)
              ·
                refine ⟨36515664785259925389219373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194750212188052935409169989 36515664785259925389219373)
                ·
                  refine ⟨13693374294472472020957265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36515664785259925389219373 13693374294472472020957265)
                  ·
                    refine ⟨10270030720854354015717949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13693374294472472020957265 10270030720854354015717949)
                    ·
                      refine ⟨3851261520320382755894231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270030720854354015717949 3851261520320382755894231)
                      ·
                        rfl

theorem cell23_7500305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_7500305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500305 prefixEnd_7500305 := by exact prefixLift 7500305
  have htrace : WordTrace (prefixWord ++ tailWord_7500305) baseStart_7500305 baseEnd_7500305 := by
    simpa [prefixWord, tailWord_7500305, baseEnd_7500305] using wordTrace_append hprefix tailTrace_7500305
  have hstable : (prefixWord ++ tailWord_7500305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500305).length < 2 ^ (prefixWord ++ tailWord_7500305).sum := by decide
  have hdescent : baseEnd_7500305 < baseStart_7500305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500312 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_7500312 : Nat := 118140960795 + 7500312 * 2 ^ 59
def prefixEnd_7500312 : Nat := 4983230072969 + 3 ^ 40 * 7500312 * 2
def baseEnd_7500312 : Nat := 1283755038228321409502233

theorem tailTrace_7500312 : CollatzResearch.WordTrace tailWord_7500312 prefixEnd_7500312 1283755038228321409502233 := by
  unfold tailWord_7500312
  simp only [CollatzResearch.WordTrace]
  refine ⟨136779426201829025076483595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182372568269105366768644793 136779426201829025076483595)
  ·
    refine ⟨205169139302743537614725393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136779426201829025076483595 205169139302743537614725393)
    ·
      refine ⟨153876854477057653211044045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205169139302743537614725393 153876854477057653211044045)
      ·
        refine ⟨57703820428896619954141517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153876854477057653211044045 57703820428896619954141517)
        ·
          refine ⟨21638932660836232482803069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57703820428896619954141517 21638932660836232482803069)
          ·
            refine ⟨8114599747813587181051151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21638932660836232482803069 8114599747813587181051151)
            ·
              refine ⟨12171899621720380771576727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114599747813587181051151 12171899621720380771576727)
              ·
                refine ⟨18257849432580571157365091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12171899621720380771576727 18257849432580571157365091)
                ·
                  refine ⟨27386774148870856736047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18257849432580571157365091 27386774148870856736047637)
                  ·
                    refine ⟨1283755038228321409502233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27386774148870856736047637 1283755038228321409502233)
                    ·
                      rfl

theorem cell23_7500312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_7500312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500312 prefixEnd_7500312 := by exact prefixLift 7500312
  have htrace : WordTrace (prefixWord ++ tailWord_7500312) baseStart_7500312 baseEnd_7500312 := by
    simpa [prefixWord, tailWord_7500312, baseEnd_7500312] using wordTrace_append hprefix tailTrace_7500312
  have hstable : (prefixWord ++ tailWord_7500312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500312).length < 2 ^ (prefixWord ++ tailWord_7500312).sum := by decide
  have hdescent : baseEnd_7500312 < baseStart_7500312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500325 : List Nat := [1, 3, 1, 2, 2, 1, 6, 7]
def baseStart_7500325 : Nat := 118140960795 + 7500325 * 2 ^ 59
def prefixEnd_7500325 : Nat := 4983230072969 + 3 ^ 40 * 7500325 * 2
def baseEnd_7500325 : Nat := 142639695923461951023857

theorem tailTrace_7500325 : CollatzResearch.WordTrace tailWord_7500325 prefixEnd_7500325 142639695923461951023857 := by
  unfold tailWord_7500325
  simp only [CollatzResearch.WordTrace]
  refine ⟨273559326552610953373190429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182372884368407302248793619 273559326552610953373190429)
  ·
    refine ⟨102584747457229107514946411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273559326552610953373190429 102584747457229107514946411)
    ·
      refine ⟨153877121185843661272419617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102584747457229107514946411 153877121185843661272419617)
      ·
        refine ⟨115407840889382745954314713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153877121185843661272419617 115407840889382745954314713)
        ·
          refine ⟨86555880667037059465736035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115407840889382745954314713 86555880667037059465736035)
          ·
            refine ⟨129833821000555589198604053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86555880667037059465736035 129833821000555589198604053)
            ·
              refine ⟨6085960359401043243684565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129833821000555589198604053 6085960359401043243684565)
              ·
                refine ⟨142639695923461951023857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085960359401043243684565 142639695923461951023857)
                ·
                  rfl

theorem cell23_7500325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 7].length) (baseStart_7500325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500325 prefixEnd_7500325 := by exact prefixLift 7500325
  have htrace : WordTrace (prefixWord ++ tailWord_7500325) baseStart_7500325 baseEnd_7500325 := by
    simpa [prefixWord, tailWord_7500325, baseEnd_7500325] using wordTrace_append hprefix tailTrace_7500325
  have hstable : (prefixWord ++ tailWord_7500325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500325).length < 2 ^ (prefixWord ++ tailWord_7500325).sum := by decide
  have hdescent : baseEnd_7500325 < baseStart_7500325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500336 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 1, 2, 2]
def baseStart_7500336 : Nat := 118140960795 + 7500336 * 2 ^ 59
def prefixEnd_7500336 : Nat := 4983230072969 + 3 ^ 40 * 7500336 * 2
def baseEnd_7500336 : Nat := 3851277438220672134606589

theorem tailTrace_7500336 : CollatzResearch.WordTrace tailWord_7500336 prefixEnd_7500336 3851277438220672134606589 := by
  unfold tailWord_7500336
  simp only [CollatzResearch.WordTrace]
  refine ⟨136779863877785551125920431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182373151837047401501227241 136779863877785551125920431)
  ·
    refine ⟨205169795816678326688880647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136779863877785551125920431 205169795816678326688880647)
    ·
      refine ⟨307754693725017490033320971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205169795816678326688880647 307754693725017490033320971)
      ·
        refine ⟨461632040587526235049981457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307754693725017490033320971 461632040587526235049981457)
        ·
          refine ⟨346224030440644676287486093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461632040587526235049981457 346224030440644676287486093)
          ·
            refine ⟨129834011415241753607807285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346224030440644676287486093 129834011415241753607807285)
            ·
              refine ⟨12171938570178914400731933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129834011415241753607807285 12171938570178914400731933)
              ·
                refine ⟨4564476963817092900274475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12171938570178914400731933 4564476963817092900274475)
                ·
                  refine ⟨6846715445725639350411713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564476963817092900274475 6846715445725639350411713)
                  ·
                    refine ⟨5135036584294229512808785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6846715445725639350411713 5135036584294229512808785)
                    ·
                      refine ⟨3851277438220672134606589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135036584294229512808785 3851277438220672134606589)
                      ·
                        rfl

theorem cell23_7500336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 2, 2].length) (baseStart_7500336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500336 prefixEnd_7500336 := by exact prefixLift 7500336
  have htrace : WordTrace (prefixWord ++ tailWord_7500336) baseStart_7500336 baseEnd_7500336 := by
    simpa [prefixWord, tailWord_7500336, baseEnd_7500336] using wordTrace_append hprefix tailTrace_7500336
  have hstable : (prefixWord ++ tailWord_7500336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500336).length < 2 ^ (prefixWord ++ tailWord_7500336).sum := by decide
  have hdescent : baseEnd_7500336 < baseStart_7500336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500342 : List Nat := [5, 1, 2, 1, 2, 3, 9]
def baseStart_7500342 : Nat := 118140960795 + 7500342 * 2 ^ 59
def prefixEnd_7500342 : Nat := 4983230072969 + 3 ^ 40 * 7500342 * 2
def baseEnd_7500342 : Nat := 47546673075365421125081

theorem tailTrace_7500342 : CollatzResearch.WordTrace tailWord_7500342 prefixEnd_7500342 47546673075365421125081 := by
  unfold tailWord_7500342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097496662096835329784955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182373297729032910184372853 17097496662096835329784955)
  ·
    refine ⟨25646244993145252994677433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097496662096835329784955 25646244993145252994677433)
    ·
      refine ⟨19234683744858939746008075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25646244993145252994677433 19234683744858939746008075)
      ·
        refine ⟨28852025617288409619012113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19234683744858939746008075 28852025617288409619012113)
        ·
          refine ⟨21639019212966307214259085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28852025617288409619012113 21639019212966307214259085)
          ·
            refine ⟨8114632204862365205347157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21639019212966307214259085 8114632204862365205347157)
            ·
              refine ⟨47546673075365421125081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8114632204862365205347157 47546673075365421125081)
              ·
                rfl

theorem cell23_7500342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 9].length) (baseStart_7500342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500342 prefixEnd_7500342 := by exact prefixLift 7500342
  have htrace : WordTrace (prefixWord ++ tailWord_7500342) baseStart_7500342 baseEnd_7500342 := by
    simpa [prefixWord, tailWord_7500342, baseEnd_7500342] using wordTrace_append hprefix tailTrace_7500342
  have hstable : (prefixWord ++ tailWord_7500342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500342).length < 2 ^ (prefixWord ++ tailWord_7500342).sum := by decide
  have hdescent : baseEnd_7500342 < baseStart_7500342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500352 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_7500352 : Nat := 118140960795 + 7500352 * 2 ^ 59
def prefixEnd_7500352 : Nat := 4983230072969 + 3 ^ 40 * 7500352 * 2
def baseEnd_7500352 : Nat := 3851285653911144072006515

theorem tailTrace_7500352 : CollatzResearch.WordTrace tailWord_7500352 prefixEnd_7500352 3851285653911144072006515 := by
  unfold tailWord_7500352
  simp only [CollatzResearch.WordTrace]
  refine ⟨136780155661756568492211655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182373540882342091322948873 136780155661756568492211655)
  ·
    refine ⟨205170233492634852738317483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136780155661756568492211655 205170233492634852738317483)
    ·
      refine ⟨307755350238952279107476225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205170233492634852738317483 307755350238952279107476225)
      ·
        refine ⟨230816512679214209330607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307755350238952279107476225 230816512679214209330607169)
        ·
          refine ⟨173112384509410656997955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230816512679214209330607169 173112384509410656997955377)
          ·
            refine ⟨129834288382057992748466533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173112384509410656997955377 129834288382057992748466533)
            ·
              refine ⟨24343929071635873640337475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129834288382057992748466533 24343929071635873640337475)
              ·
                refine ⟨36515893607453810460506213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24343929071635873640337475 36515893607453810460506213)
                ·
                  refine ⟨6846730051397589461344915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36515893607453810460506213 6846730051397589461344915)
                  ·
                    refine ⟨10270095077096384192017373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846730051397589461344915 10270095077096384192017373)
                    ·
                      refine ⟨3851285653911144072006515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270095077096384192017373 3851285653911144072006515)
                      ·
                        rfl

theorem cell23_7500352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_7500352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500352 prefixEnd_7500352 := by exact prefixLift 7500352
  have htrace : WordTrace (prefixWord ++ tailWord_7500352) baseStart_7500352 baseEnd_7500352 := by
    simpa [prefixWord, tailWord_7500352, baseEnd_7500352] using wordTrace_append hprefix tailTrace_7500352
  have hstable : (prefixWord ++ tailWord_7500352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500352).length < 2 ^ (prefixWord ++ tailWord_7500352).sum := by decide
  have hdescent : baseEnd_7500352 < baseStart_7500352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500369 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_7500369 : Nat := 118140960795 + 7500369 * 2 ^ 59
def prefixEnd_7500369 : Nat := 4983230072969 + 3 ^ 40 * 7500369 * 2
def baseEnd_7500369 : Nat := 3851294383082270505493937

theorem tailTrace_7500369 : CollatzResearch.WordTrace tailWord_7500369 prefixEnd_7500369 3851294383082270505493937 := by
  unfold tailWord_7500369
  simp only [CollatzResearch.WordTrace]
  refine ⟨273560931364451548887792161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182373954242967699258528107 273560931364451548887792161)
  ·
    refine ⟨205170698523338661665844121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273560931364451548887792161 205170698523338661665844121)
    ·
      refine ⟨153878023892503996249383091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205170698523338661665844121 153878023892503996249383091)
      ·
        refine ⟨230817035838755994374074637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153878023892503996249383091 230817035838755994374074637)
        ·
          refine ⟨86556388439533497890277989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230817035838755994374074637 86556388439533497890277989)
          ·
            refine ⟨16229322832412530854427123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86556388439533497890277989 16229322832412530854427123)
            ·
              refine ⟨24343984248618796281640685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229322832412530854427123 24343984248618796281640685)
              ·
                refine ⟨9128994093232048605615257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24343984248618796281640685 9128994093232048605615257)
                ·
                  refine ⟨6846745569924036454211443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9128994093232048605615257 6846745569924036454211443)
                  ·
                    refine ⟨10270118354886054681317165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846745569924036454211443 10270118354886054681317165)
                    ·
                      refine ⟨3851294383082270505493937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270118354886054681317165 3851294383082270505493937)
                      ·
                        rfl

theorem cell23_7500369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_7500369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500369 prefixEnd_7500369 := by exact prefixLift 7500369
  have htrace : WordTrace (prefixWord ++ tailWord_7500369) baseStart_7500369 baseEnd_7500369 := by
    simpa [prefixWord, tailWord_7500369, baseEnd_7500369] using wordTrace_append hprefix tailTrace_7500369
  have hstable : (prefixWord ++ tailWord_7500369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500369).length < 2 ^ (prefixWord ++ tailWord_7500369).sum := by decide
  have hdescent : baseEnd_7500369 < baseStart_7500369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500386 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7500386 : Nat := 118140960795 + 7500386 * 2 ^ 59
def prefixEnd_7500386 : Nat := 4983230072969 + 3 ^ 40 * 7500386 * 2
def baseEnd_7500386 : Nat := 3851303112253396938981359

theorem tailTrace_7500386 : CollatzResearch.WordTrace tailWord_7500386 prefixEnd_7500386 3851303112253396938981359 := by
  unfold tailWord_7500386
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390387851347490197790253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182374367603593307194107341 68390387851347490197790253)
  ·
    refine ⟨25646395444255308824171345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68390387851347490197790253 25646395444255308824171345)
    ·
      refine ⟨19234796583191481618128509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25646395444255308824171345 19234796583191481618128509)
      ·
        refine ⟨7213048718696805606798191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19234796583191481618128509 7213048718696805606798191)
        ·
          refine ⟨10819573078045208410197287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213048718696805606798191 10819573078045208410197287)
          ·
            refine ⟨16229359617067812615295931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819573078045208410197287 16229359617067812615295931)
            ·
              refine ⟨24344039425601718922943897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16229359617067812615295931 24344039425601718922943897)
              ·
                refine ⟨18258029569201289192207923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24344039425601718922943897 18258029569201289192207923)
                ·
                  refine ⟨27387044353801933788311885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18258029569201289192207923 27387044353801933788311885)
                  ·
                    refine ⟨10270141632675725170616957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27387044353801933788311885 10270141632675725170616957)
                    ·
                      refine ⟨3851303112253396938981359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270141632675725170616957 3851303112253396938981359)
                      ·
                        rfl

theorem cell23_7500386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7500386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500386 prefixEnd_7500386 := by exact prefixLift 7500386
  have htrace : WordTrace (prefixWord ++ tailWord_7500386) baseStart_7500386 baseEnd_7500386 := by
    simpa [prefixWord, tailWord_7500386, baseEnd_7500386] using wordTrace_append hprefix tailTrace_7500386
  have hstable : (prefixWord ++ tailWord_7500386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500386).length < 2 ^ (prefixWord ++ tailWord_7500386).sum := by decide
  have hdescent : baseEnd_7500386 < baseStart_7500386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500426 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_7500426 : Nat := 118140960795 + 7500426 * 2 ^ 59
def prefixEnd_7500426 : Nat := 4983230072969 + 3 ^ 40 * 7500426 * 2
def baseEnd_7500426 : Nat := 3851323651479576782481175

theorem tailTrace_7500426 : CollatzResearch.WordTrace tailWord_7500426 prefixEnd_7500426 3851323651479576782481175 := by
  unfold tailWord_7500426
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390752581311261905654283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182375340216830031748411421 68390752581311261905654283)
  ·
    refine ⟨102586128871966892858481425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68390752581311261905654283 102586128871966892858481425)
    ·
      refine ⟨76939596653975169643861069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102586128871966892858481425 76939596653975169643861069)
      ·
        refine ⟨28852348745240688616447901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76939596653975169643861069 28852348745240688616447901)
        ·
          refine ⟨10819630779465258231167963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28852348745240688616447901 10819630779465258231167963)
          ·
            refine ⟨16229446169197887346751945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819630779465258231167963 16229446169197887346751945)
            ·
              refine ⟨12172084626898415510063959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16229446169197887346751945 12172084626898415510063959)
              ·
                refine ⟨18258126940347623265095939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172084626898415510063959 18258126940347623265095939)
                ·
                  refine ⟨27387190410521434897643909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18258126940347623265095939 27387190410521434897643909)
                  ·
                    refine ⟨5135098201972769043308233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27387190410521434897643909 5135098201972769043308233)
                    ·
                      refine ⟨3851323651479576782481175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135098201972769043308233 3851323651479576782481175)
                      ·
                        rfl

theorem cell23_7500426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_7500426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500426 prefixEnd_7500426 := by exact prefixLift 7500426
  have htrace : WordTrace (prefixWord ++ tailWord_7500426) baseStart_7500426 baseEnd_7500426 := by
    simpa [prefixWord, tailWord_7500426, baseEnd_7500426] using wordTrace_append hprefix tailTrace_7500426
  have hstable : (prefixWord ++ tailWord_7500426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500426).length < 2 ^ (prefixWord ++ tailWord_7500426).sum := by decide
  have hdescent : baseEnd_7500426 < baseStart_7500426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500505 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 10]
def baseStart_7500505 : Nat := 118140960795 + 7500505 * 2 ^ 59
def prefixEnd_7500505 : Nat := 4983230072969 + 3 ^ 40 * 7500505 * 2
def baseEnd_7500505 : Nat := 427929357383475774821479

theorem tailTrace_7500505 : CollatzResearch.WordTrace tailWord_7500505 prefixEnd_7500505 427929357383475774821479 := by
  unfold tailWord_7500505
  simp only [CollatzResearch.WordTrace]
  refine ⟨273565891691958844114742969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182377261127972562743161979 273565891691958844114742969)
  ·
    refine ⟨205174418768969133086057227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273565891691958844114742969 205174418768969133086057227)
    ·
      refine ⟨307761628153453699629085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205174418768969133086057227 307761628153453699629085841)
      ·
        refine ⟨230821221115090274721814381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307761628153453699629085841 230821221115090274721814381)
        ·
          refine ⟨86557957918158853020680393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230821221115090274721814381 86557957918158853020680393)
          ·
            refine ⟨64918468438619139765510295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86557957918158853020680393 64918468438619139765510295)
            ·
              refine ⟨97377702657928709648265443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64918468438619139765510295 97377702657928709648265443)
              ·
                refine ⟨146066553986893064472398165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97377702657928709648265443 146066553986893064472398165)
                ·
                  refine ⟨427929357383475774821479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146066553986893064472398165 427929357383475774821479)
                  ·
                    rfl

theorem cell23_7500505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_7500505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500505 prefixEnd_7500505 := by exact prefixLift 7500505
  have htrace : WordTrace (prefixWord ++ tailWord_7500505) baseStart_7500505 baseEnd_7500505 := by
    simpa [prefixWord, tailWord_7500505, baseEnd_7500505] using wordTrace_append hprefix tailTrace_7500505
  have hstable : (prefixWord ++ tailWord_7500505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500505).length < 2 ^ (prefixWord ++ tailWord_7500505).sum := by decide
  have hdescent : baseEnd_7500505 < baseStart_7500505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500522 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_7500522 : Nat := 118140960795 + 7500522 * 2 ^ 59
def prefixEnd_7500522 : Nat := 4983230072969 + 3 ^ 40 * 7500522 * 2
def baseEnd_7500522 : Nat := 427930327291378711875637

theorem tailTrace_7500522 : CollatzResearch.WordTrace tailWord_7500522 prefixEnd_7500522 427930327291378711875637 := by
  unfold tailWord_7500522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68391627933224314004527955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182377674488598170678741213 68391627933224314004527955)
  ·
    refine ⟨102587441899836471006791933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68391627933224314004527955 102587441899836471006791933)
    ·
      refine ⟨38470290712438676627546975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102587441899836471006791933 38470290712438676627546975)
      ·
        refine ⟨57705436068658014941320463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470290712438676627546975 57705436068658014941320463)
        ·
          refine ⟨86558154102987022411980695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57705436068658014941320463 86558154102987022411980695)
          ·
            refine ⟨129837231154480533617971043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86558154102987022411980695 129837231154480533617971043)
            ·
              refine ⟨194755846731720800426956565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129837231154480533617971043 194755846731720800426956565)
              ·
                refine ⟨9129180315549412520013589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194755846731720800426956565 9129180315549412520013589)
                ·
                  refine ⟨427930327291378711875637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9129180315549412520013589 427930327291378711875637)
                  ·
                    rfl

theorem cell23_7500522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_7500522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500522 prefixEnd_7500522 := by exact prefixLift 7500522
  have htrace : WordTrace (prefixWord ++ tailWord_7500522) baseStart_7500522 baseEnd_7500522 := by
    simpa [prefixWord, tailWord_7500522, baseEnd_7500522] using wordTrace_append hprefix tailTrace_7500522
  have hstable : (prefixWord ++ tailWord_7500522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500522).length < 2 ^ (prefixWord ++ tailWord_7500522).sum := by decide
  have hdescent : baseEnd_7500522 < baseStart_7500522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500526 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7500526 : Nat := 118140960795 + 7500526 * 2 ^ 59
def prefixEnd_7500526 : Nat := 4983230072969 + 3 ^ 40 * 7500526 * 2
def baseEnd_7500526 : Nat := 1283791666515008797076905

theorem tailTrace_7500526 : CollatzResearch.WordTrace tailWord_7500526 prefixEnd_7500526 1283791666515008797076905 := by
  unfold tailWord_7500526
  simp only [CollatzResearch.WordTrace]
  refine ⟨34195832203110345587657179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182377771749921843134171621 34195832203110345587657179)
  ·
    refine ⟨51293748304665518381485769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34195832203110345587657179 51293748304665518381485769)
    ·
      refine ⟨38470311228499138786114327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51293748304665518381485769 38470311228499138786114327)
      ·
        refine ⟨57705466842748708179171491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470311228499138786114327 57705466842748708179171491)
        ·
          refine ⟨86558200264123062268757237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57705466842748708179171491 86558200264123062268757237)
          ·
            refine ⟨8114831274761537087695991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86558200264123062268757237 8114831274761537087695991)
            ·
              refine ⟨12172246912142305631543987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8114831274761537087695991 12172246912142305631543987)
              ·
                refine ⟨18258370368213458447315981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172246912142305631543987 18258370368213458447315981)
                ·
                  refine ⟨6846888888080046917743493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18258370368213458447315981 6846888888080046917743493)
                  ·
                    refine ⟨1283791666515008797076905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846888888080046917743493 1283791666515008797076905)
                    ·
                      rfl

theorem cell23_7500526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7500526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500526 prefixEnd_7500526 := by exact prefixLift 7500526
  have htrace : WordTrace (prefixWord ++ tailWord_7500526) baseStart_7500526 baseEnd_7500526 := by
    simpa [prefixWord, tailWord_7500526, baseEnd_7500526] using wordTrace_append hprefix tailTrace_7500526
  have hstable : (prefixWord ++ tailWord_7500526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500526).length < 2 ^ (prefixWord ++ tailWord_7500526).sum := by decide
  have hdescent : baseEnd_7500526 < baseStart_7500526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500535 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 2, 9]
def baseStart_7500535 : Nat := 118140960795 + 7500535 * 2 ^ 59
def prefixEnd_7500535 : Nat := 4983230072969 + 3 ^ 40 * 7500535 * 2
def baseEnd_7500535 : Nat := 1283793206956972285339391

theorem tailTrace_7500535 : CollatzResearch.WordTrace tailWord_7500535 prefixEnd_7500535 1283793206956972285339391 := by
  unfold tailWord_7500535
  simp only [CollatzResearch.WordTrace]
  refine ⟨273566985881850159238335059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182377990587900106158890039 273566985881850159238335059)
  ·
    refine ⟨410350478822775238857502589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273566985881850159238335059 410350478822775238857502589)
    ·
      refine ⟨153881429558540714571563471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410350478822775238857502589 153881429558540714571563471)
      ·
        refine ⟨230822144337811071857345207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153881429558540714571563471 230822144337811071857345207)
        ·
          refine ⟨346233216506716607786017811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230822144337811071857345207 346233216506716607786017811)
          ·
            refine ⟨519349824760074911679026717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346233216506716607786017811 519349824760074911679026717)
            ·
              refine ⟨194756184285028091879635019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519349824760074911679026717 194756184285028091879635019)
              ·
                refine ⟨292134276427542137819452529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194756184285028091879635019 292134276427542137819452529)
                ·
                  refine ⟨219100707320656603364589397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292134276427542137819452529 219100707320656603364589397)
                  ·
                    refine ⟨1283793206956972285339391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219100707320656603364589397 1283793206956972285339391)
                    ·
                      rfl

theorem cell23_7500535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_7500535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500535 prefixEnd_7500535 := by exact prefixLift 7500535
  have htrace : WordTrace (prefixWord ++ tailWord_7500535) baseStart_7500535 baseEnd_7500535 := by
    simpa [prefixWord, tailWord_7500535, baseEnd_7500535] using wordTrace_append hprefix tailTrace_7500535
  have hstable : (prefixWord ++ tailWord_7500535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500535).length < 2 ^ (prefixWord ++ tailWord_7500535).sum := by decide
  have hdescent : baseEnd_7500535 < baseStart_7500535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500549 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_7500549 : Nat := 118140960795 + 7500549 * 2 ^ 59
def prefixEnd_7500549 : Nat := 4983230072969 + 3 ^ 40 * 7500549 * 2
def baseEnd_7500549 : Nat := 3851386809600079801243109

theorem tailTrace_7500549 : CollatzResearch.WordTrace tailWord_7500549 prefixEnd_7500549 3851386809600079801243109 := by
  unfold tailWord_7500549
  simp only [CollatzResearch.WordTrace]
  refine ⟨273567496503799439629344701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182378331002532959752896467 273567496503799439629344701)
  ·
    refine ⟨102587811188924789861004263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273567496503799439629344701 102587811188924789861004263)
    ·
      refine ⟨153881716783387184791506395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102587811188924789861004263 153881716783387184791506395)
      ·
        refine ⟨230822575175080777187259593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153881716783387184791506395 230822575175080777187259593)
        ·
          refine ⟨173116931381310582890444695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230822575175080777187259593 173116931381310582890444695)
          ·
            refine ⟨259675397071965874335667043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173116931381310582890444695 259675397071965874335667043)
            ·
              refine ⟨389513095607948811503500565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259675397071965874335667043 389513095607948811503500565)
              ·
                refine ⟨18258426356622600539226589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 389513095607948811503500565 18258426356622600539226589)
                ·
                  refine ⟨6846909883733475202209971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18258426356622600539226589 6846909883733475202209971)
                  ·
                    refine ⟨10270364825600212803314957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846909883733475202209971 10270364825600212803314957)
                    ·
                      refine ⟨3851386809600079801243109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270364825600212803314957 3851386809600079801243109)
                      ·
                        rfl

theorem cell23_7500549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_7500549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500549 prefixEnd_7500549 := by exact prefixLift 7500549
  have htrace : WordTrace (prefixWord ++ tailWord_7500549) baseStart_7500549 baseEnd_7500549 := by
    simpa [prefixWord, tailWord_7500549, baseEnd_7500549] using wordTrace_append hprefix tailTrace_7500549
  have hstable : (prefixWord ++ tailWord_7500549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500549).length < 2 ^ (prefixWord ++ tailWord_7500549).sum := by decide
  have hdescent : baseEnd_7500549 < baseStart_7500549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500576 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7500576 : Nat := 118140960795 + 7500576 * 2 ^ 59
def prefixEnd_7500576 : Nat := 4983230072969 + 3 ^ 40 * 7500576 * 2
def baseEnd_7500576 : Nat := 3851400673577751195605485

theorem tailTrace_7500576 : CollatzResearch.WordTrace tailWord_7500576 prefixEnd_7500576 3851400673577751195605485 := by
  unfold tailWord_7500576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136784240637350811620288791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182378987516467748827051721 136784240637350811620288791)
  ·
    refine ⟨205176360956026217430433187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136784240637350811620288791 205176360956026217430433187)
    ·
      refine ⟨307764541434039326145649781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205176360956026217430433187 307764541434039326145649781)
      ·
        refine ⟨28852925759441186826154667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307764541434039326145649781 28852925759441186826154667)
        ·
          refine ⟨43279388639161780239232001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28852925759441186826154667 43279388639161780239232001)
          ·
            refine ⟨32459541479371335179424001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43279388639161780239232001 32459541479371335179424001)
            ·
              refine ⟨24344656109528501384568001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32459541479371335179424001 24344656109528501384568001)
              ·
                refine ⟨18258492082146376038426001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24344656109528501384568001 18258492082146376038426001)
                ·
                  refine ⟨13693869061609782028819501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18258492082146376038426001 13693869061609782028819501)
                  ·
                    refine ⟨5135200898103668260807313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13693869061609782028819501 5135200898103668260807313)
                    ·
                      refine ⟨3851400673577751195605485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135200898103668260807313 3851400673577751195605485)
                      ·
                        rfl

theorem cell23_7500576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7500576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500576 prefixEnd_7500576 := by exact prefixLift 7500576
  have htrace : WordTrace (prefixWord ++ tailWord_7500576) baseStart_7500576 baseEnd_7500576 := by
    simpa [prefixWord, tailWord_7500576, baseEnd_7500576] using wordTrace_append hprefix tailTrace_7500576
  have hstable : (prefixWord ++ tailWord_7500576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500576).length < 2 ^ (prefixWord ++ tailWord_7500576).sum := by decide
  have hdescent : baseEnd_7500576 < baseStart_7500576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500592 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_7500592 : Nat := 118140960795 + 7500592 * 2 ^ 59
def prefixEnd_7500592 : Nat := 4983230072969 + 3 ^ 40 * 7500592 * 2
def baseEnd_7500592 : Nat := 3851408889268223133005411

theorem tailTrace_7500592 : CollatzResearch.WordTrace tailWord_7500592 prefixEnd_7500592 3851408889268223133005411 := by
  unfold tailWord_7500592
  simp only [CollatzResearch.WordTrace]
  refine ⟨136784532421321828986580015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182379376561762438648773353 136784532421321828986580015)
  ·
    refine ⟨205176798631982743479870023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136784532421321828986580015 205176798631982743479870023)
    ·
      refine ⟨307765197947974115219805035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205176798631982743479870023 307765197947974115219805035)
      ·
        refine ⟨461647796921961172829707553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307765197947974115219805035 461647796921961172829707553)
        ·
          refine ⟨346235847691470879622280665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461647796921961172829707553 346235847691470879622280665)
          ·
            refine ⟨259676885768603159716710499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346235847691470879622280665 259676885768603159716710499)
            ·
              refine ⟨389515328652904739575065749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259676885768603159716710499 389515328652904739575065749)
              ·
                refine ⟨18258531030604909667581207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 389515328652904739575065749 18258531030604909667581207)
                ·
                  refine ⟨27387796545907364501371811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18258531030604909667581207 27387796545907364501371811)
                  ·
                    refine ⟨41081694818861046752057717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27387796545907364501371811 41081694818861046752057717)
                    ·
                      refine ⟨3851408889268223133005411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41081694818861046752057717 3851408889268223133005411)
                      ·
                        rfl

theorem cell23_7500592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_7500592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500592 prefixEnd_7500592 := by exact prefixLift 7500592
  have htrace : WordTrace (prefixWord ++ tailWord_7500592) baseStart_7500592 baseEnd_7500592 := by
    simpa [prefixWord, tailWord_7500592, baseEnd_7500592] using wordTrace_append hprefix tailTrace_7500592
  have hstable : (prefixWord ++ tailWord_7500592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500592).length < 2 ^ (prefixWord ++ tailWord_7500592).sum := by decide
  have hdescent : baseEnd_7500592 < baseStart_7500592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500599 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 2, 4]
def baseStart_7500599 : Nat := 118140960795 + 7500599 * 2 ^ 59
def prefixEnd_7500599 : Nat := 4983230072969 + 3 ^ 40 * 7500599 * 2
def baseEnd_7500599 : Nat := 1283804161210934868539293

theorem tailTrace_7500599 : CollatzResearch.WordTrace tailWord_7500599 prefixEnd_7500599 1283804161210934868539293 := by
  unfold tailWord_7500599
  simp only [CollatzResearch.WordTrace]
  refine ⟨273569320153618298168664851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182379546769078865445776567 273569320153618298168664851)
  ·
    refine ⟨410353980230427447252997277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273569320153618298168664851 410353980230427447252997277)
    ·
      refine ⟨153882742586410292719873979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410353980230427447252997277 153882742586410292719873979)
      ·
        refine ⟨230824113879615439079810969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153882742586410292719873979 230824113879615439079810969)
        ·
          refine ⟨173118085409711579309858227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230824113879615439079810969 173118085409711579309858227)
          ·
            refine ⟨259677128114567368964787341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173118085409711579309858227 259677128114567368964787341)
            ·
              refine ⟨97378923042962763361795253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259677128114567368964787341 97378923042962763361795253)
              ·
                refine ⟨9129274035277759065168305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97378923042962763361795253 9129274035277759065168305)
                ·
                  refine ⟨6846955526458319298876229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129274035277759065168305 6846955526458319298876229)
                  ·
                    refine ⟨1283804161210934868539293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6846955526458319298876229 1283804161210934868539293)
                    ·
                      rfl

theorem cell23_7500599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_7500599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500599 prefixEnd_7500599 := by exact prefixLift 7500599
  have htrace : WordTrace (prefixWord ++ tailWord_7500599) baseStart_7500599 baseEnd_7500599 := by
    simpa [prefixWord, tailWord_7500599, baseEnd_7500599] using wordTrace_append hprefix tailTrace_7500599
  have hstable : (prefixWord ++ tailWord_7500599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500599).length < 2 ^ (prefixWord ++ tailWord_7500599).sum := by decide
  have hdescent : baseEnd_7500599 < baseStart_7500599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500626 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_7500626 : Nat := 118140960795 + 7500626 * 2 ^ 59
def prefixEnd_7500626 : Nat := 4983230072969 + 3 ^ 40 * 7500626 * 2
def baseEnd_7500626 : Nat := 3851426347610475999980255

theorem tailTrace_7500626 : CollatzResearch.WordTrace tailWord_7500626 prefixEnd_7500626 3851426347610475999980255 := by
  unfold tailWord_7500626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68392576231130120444974433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182380203283013654519931821 68392576231130120444974433)
  ·
    refine ⟨51294432173347590333730825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68392576231130120444974433 51294432173347590333730825)
    ·
      refine ⟨38470824130010692750298119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51294432173347590333730825 38470824130010692750298119)
      ·
        refine ⟨57706236195016039125447179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38470824130010692750298119 57706236195016039125447179)
        ·
          refine ⟨86559354292524058688170769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57706236195016039125447179 86559354292524058688170769)
          ·
            refine ⟨64919515719393044016128077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86559354292524058688170769 64919515719393044016128077)
            ·
              refine ⟨24344818394772391506048029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64919515719393044016128077 24344818394772391506048029)
              ·
                refine ⟨9129306898039646814768011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24344818394772391506048029 9129306898039646814768011)
                ·
                  refine ⟨13693960347059470222152017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129306898039646814768011 13693960347059470222152017)
                  ·
                    refine ⟨10270470260294602666614013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13693960347059470222152017 10270470260294602666614013)
                    ·
                      refine ⟨3851426347610475999980255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270470260294602666614013 3851426347610475999980255)
                      ·
                        rfl

theorem cell23_7500626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_7500626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500626 prefixEnd_7500626 := by exact prefixLift 7500626
  have htrace : WordTrace (prefixWord ++ tailWord_7500626) baseStart_7500626 baseEnd_7500626 := by
    simpa [prefixWord, tailWord_7500626, baseEnd_7500626] using wordTrace_append hprefix tailTrace_7500626
  have hstable : (prefixWord ++ tailWord_7500626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500626).length < 2 ^ (prefixWord ++ tailWord_7500626).sum := by decide
  have hdescent : baseEnd_7500626 < baseStart_7500626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500656 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_7500656 : Nat := 118140960795 + 7500656 * 2 ^ 59
def prefixEnd_7500656 : Nat := 4983230072969 + 3 ^ 40 * 7500656 * 2
def baseEnd_7500656 : Nat := 3851441752030110882605117

theorem tailTrace_7500656 : CollatzResearch.WordTrace tailWord_7500656 prefixEnd_7500656 3851441752030110882605117 := by
  unfold tailWord_7500656
  simp only [CollatzResearch.WordTrace]
  refine ⟨136785699557205898451744911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182380932742941197935659881 136785699557205898451744911)
  ·
    refine ⟨205178549335808847677617367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136785699557205898451744911 205178549335808847677617367)
    ·
      refine ⟨307767824003713271516426051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205178549335808847677617367 307767824003713271516426051)
      ·
        refine ⟨461651736005569907274639077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307767824003713271516426051 461651736005569907274639077)
        ·
          refine ⟨86559700501044357613994827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461651736005569907274639077 86559700501044357613994827)
          ·
            refine ⟨129839550751566536420992241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86559700501044357613994827 129839550751566536420992241)
            ·
              refine ⟨97379663063674902315744181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129839550751566536420992241 97379663063674902315744181)
              ·
                refine ⟨9129343412219522092101017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97379663063674902315744181 9129343412219522092101017)
                ·
                  refine ⟨6847007559164641569075763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129343412219522092101017 6847007559164641569075763)
                  ·
                    refine ⟨10270511338746962353613645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847007559164641569075763 10270511338746962353613645)
                    ·
                      refine ⟨3851441752030110882605117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270511338746962353613645 3851441752030110882605117)
                      ·
                        rfl

theorem cell23_7500656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_7500656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500656 prefixEnd_7500656 := by exact prefixLift 7500656
  have htrace : WordTrace (prefixWord ++ tailWord_7500656) baseStart_7500656 baseEnd_7500656 := by
    simpa [prefixWord, tailWord_7500656, baseEnd_7500656] using wordTrace_append hprefix tailTrace_7500656
  have hstable : (prefixWord ++ tailWord_7500656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500656).length < 2 ^ (prefixWord ++ tailWord_7500656).sum := by decide
  have hdescent : baseEnd_7500656 < baseStart_7500656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500672 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_7500672 : Nat := 118140960795 + 7500672 * 2 ^ 59
def prefixEnd_7500672 : Nat := 4983230072969 + 3 ^ 40 * 7500672 * 2
def baseEnd_7500672 : Nat := 1283816655906860940001681

theorem tailTrace_7500672 : CollatzResearch.WordTrace tailWord_7500672 prefixEnd_7500672 1283816655906860940001681 := by
  unfold tailWord_7500672
  simp only [CollatzResearch.WordTrace]
  refine ⟨136785991341176915818036135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182381321788235887757381513 136785991341176915818036135)
  ·
    refine ⟨205178987011765373727054203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136785991341176915818036135 205178987011765373727054203)
    ·
      refine ⟨307768480517648060590581305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205178987011765373727054203 307768480517648060590581305)
      ·
        refine ⟨230826360388236045442935979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307768480517648060590581305 230826360388236045442935979)
        ·
          refine ⟨346239540582354068164403969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230826360388236045442935979 346239540582354068164403969)
          ·
            refine ⟨259679655436765551123302977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346239540582354068164403969 259679655436765551123302977)
            ·
              refine ⟨194759741577574163342477233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259679655436765551123302977 194759741577574163342477233)
              ·
                refine ⟨146069806183180622506857925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194759741577574163342477233 146069806183180622506857925)
                ·
                  refine ⟨27388088659346366720035861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146069806183180622506857925 27388088659346366720035861)
                  ·
                    refine ⟨1283816655906860940001681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27388088659346366720035861 1283816655906860940001681)
                    ·
                      rfl

theorem cell23_7500672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_7500672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500672 prefixEnd_7500672 := by exact prefixLift 7500672
  have htrace : WordTrace (prefixWord ++ tailWord_7500672) baseStart_7500672 baseEnd_7500672 := by
    simpa [prefixWord, tailWord_7500672, baseEnd_7500672] using wordTrace_append hprefix tailTrace_7500672
  have hstable : (prefixWord ++ tailWord_7500672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500672).length < 2 ^ (prefixWord ++ tailWord_7500672).sum := by decide
  have hdescent : baseEnd_7500672 < baseStart_7500672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500713 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 2, 2, 2]
def baseStart_7500713 : Nat := 118140960795 + 7500713 * 2 ^ 59
def prefixEnd_7500713 : Nat := 4983230072969 + 3 ^ 40 * 7500713 * 2
def baseEnd_7500713 : Nat := 3851471020427417159592355

theorem tailTrace_7500713 : CollatzResearch.WordTrace tailWord_7500713 prefixEnd_7500713 3851471020427417159592355 := by
  unfold tailWord_7500713
  simp only [CollatzResearch.WordTrace]
  refine ⟨273573478075205295638314793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182382318716803530425543195 273573478075205295638314793)
  ·
    refine ⟨205180108556403971728736095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273573478075205295638314793 205180108556403971728736095)
    ·
      refine ⟨307770162834605957593104143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205180108556403971728736095 307770162834605957593104143)
      ·
        refine ⟨461655244251908936389656215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307770162834605957593104143 461655244251908936389656215)
        ·
          refine ⟨692482866377863404584484323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461655244251908936389656215 692482866377863404584484323)
          ·
            refine ⟨1038724299566795106876726485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692482866377863404584484323 1038724299566795106876726485)
            ·
              refine ⟨24345100771096760317423277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1038724299566795106876726485 24345100771096760317423277)
              ·
                refine ⟨9129412789161285119033729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24345100771096760317423277 9129412789161285119033729)
                ·
                  refine ⟨6847059591870963839275297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129412789161285119033729 6847059591870963839275297)
                  ·
                    refine ⟨5135294693903222879456473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6847059591870963839275297 5135294693903222879456473)
                    ·
                      refine ⟨3851471020427417159592355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135294693903222879456473 3851471020427417159592355)
                      ·
                        rfl

theorem cell23_7500713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2, 2].length) (baseStart_7500713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500713 prefixEnd_7500713 := by exact prefixLift 7500713
  have htrace : WordTrace (prefixWord ++ tailWord_7500713) baseStart_7500713 baseEnd_7500713 := by
    simpa [prefixWord, tailWord_7500713, baseEnd_7500713] using wordTrace_append hprefix tailTrace_7500713
  have hstable : (prefixWord ++ tailWord_7500713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500713).length < 2 ^ (prefixWord ++ tailWord_7500713).sum := by decide
  have hdescent : baseEnd_7500713 < baseStart_7500713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500742 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7500742 : Nat := 118140960795 + 7500742 * 2 ^ 59
def prefixEnd_7500742 : Nat := 4983230072969 + 3 ^ 40 * 7500742 * 2
def baseEnd_7500742 : Nat := 3851485911366397546129723

theorem tailTrace_7500742 : CollatzResearch.WordTrace tailWord_7500742 prefixEnd_7500742 3851485911366397546129723 := by
  unfold tailWord_7500742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549204243503132299722515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182383023861400155727413653 8549204243503132299722515)
  ·
    refine ⟨12823806365254698449583773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8549204243503132299722515 12823806365254698449583773)
    ·
      refine ⟨4808927386970511918593915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12823806365254698449583773 4808927386970511918593915)
      ·
        refine ⟨7213391080455767877890873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808927386970511918593915 7213391080455767877890873)
        ·
          refine ⟨5410043310341825908418155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213391080455767877890873 5410043310341825908418155)
          ·
            refine ⟨8115064965512738862627233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410043310341825908418155 8115064965512738862627233)
            ·
              refine ⟨6086298724134554146970425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115064965512738862627233 6086298724134554146970425)
              ·
                refine ⟨4564724043100915610227819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086298724134554146970425 4564724043100915610227819)
                ·
                  refine ⟨6847086064651373415341729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564724043100915610227819 6847086064651373415341729)
                  ·
                    refine ⟨5135314548488530061506297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6847086064651373415341729 5135314548488530061506297)
                    ·
                      refine ⟨3851485911366397546129723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135314548488530061506297 3851485911366397546129723)
                      ·
                        rfl

theorem cell23_7500742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7500742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500742 prefixEnd_7500742 := by exact prefixLift 7500742
  have htrace : WordTrace (prefixWord ++ tailWord_7500742) baseStart_7500742 baseEnd_7500742 := by
    simpa [prefixWord, tailWord_7500742, baseEnd_7500742] using wordTrace_append hprefix tailTrace_7500742
  have hstable : (prefixWord ++ tailWord_7500742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500742).length < 2 ^ (prefixWord ++ tailWord_7500742).sum := by decide
  have hdescent : baseEnd_7500742 < baseStart_7500742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500769 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_7500769 : Nat := 118140960795 + 7500769 * 2 ^ 59
def prefixEnd_7500769 : Nat := 4983230072969 + 3 ^ 40 * 7500769 * 2
def baseEnd_7500769 : Nat := 3851499775344068940492097

theorem tailTrace_7500769 : CollatzResearch.WordTrace tailWord_7500769 prefixEnd_7500769 3851499775344068940492097 := by
  unfold tailWord_7500769
  simp only [CollatzResearch.WordTrace]
  refine ⟨273575520563002417202353361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182383680375334944801568907 273575520563002417202353361)
  ·
    refine ⟨205181640422251812901765021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273575520563002417202353361 205181640422251812901765021)
    ·
      refine ⟨76943115158344429838161883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205181640422251812901765021 76943115158344429838161883)
      ·
        refine ⟨115414672737516644757242825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76943115158344429838161883 115414672737516644757242825)
        ·
          refine ⟨86561004553137483567932119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115414672737516644757242825 86561004553137483567932119)
          ·
            refine ⟨129841506829706225351898179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86561004553137483567932119 129841506829706225351898179)
            ·
              refine ⟨194762260244559338027847269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129841506829706225351898179 194762260244559338027847269)
              ·
                refine ⟨36517923795854875880221363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194762260244559338027847269 36517923795854875880221363)
                ·
                  refine ⟨54776885693782313820332045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36517923795854875880221363 54776885693782313820332045)
                  ·
                    refine ⟨20541332135168367682624517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54776885693782313820332045 20541332135168367682624517)
                    ·
                      refine ⟨3851499775344068940492097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20541332135168367682624517 3851499775344068940492097)
                      ·
                        rfl

theorem cell23_7500769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_7500769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500769 prefixEnd_7500769 := by exact prefixLift 7500769
  have htrace : WordTrace (prefixWord ++ tailWord_7500769) baseStart_7500769 baseEnd_7500769 := by
    simpa [prefixWord, tailWord_7500769, baseEnd_7500769] using wordTrace_append hprefix tailTrace_7500769
  have hstable : (prefixWord ++ tailWord_7500769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500769).length < 2 ^ (prefixWord ++ tailWord_7500769).sum := by decide
  have hdescent : baseEnd_7500769 < baseStart_7500769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500876 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7500876 : Nat := 118140960795 + 7500876 * 2 ^ 59
def prefixEnd_7500876 : Nat := 4983230072969 + 3 ^ 40 * 7500876 * 2
def baseEnd_7500876 : Nat := 3851554717774100021854105

theorem tailTrace_7500876 : CollatzResearch.WordTrace tailWord_7500876 prefixEnd_7500876 3851554717774100021854105 := by
  unfold tailWord_7500876
  simp only [CollatzResearch.WordTrace]
  refine ⟨136789711586807387238249241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182386282115743182984332321 136789711586807387238249241)
  ·
    refine ⟨102592283690105540428686931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136789711586807387238249241 102592283690105540428686931)
    ·
      refine ⟨153888425535158310643030397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102592283690105540428686931 153888425535158310643030397)
      ·
        refine ⟨57708159575684366491136399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153888425535158310643030397 57708159575684366491136399)
        ·
          refine ⟨86562239363526549736704599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57708159575684366491136399 86562239363526549736704599)
          ·
            refine ⟨129843359045289824605056899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86562239363526549736704599 129843359045289824605056899)
            ·
              refine ⟨194765038567934736907585349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129843359045289824605056899 194765038567934736907585349)
              ·
                refine ⟨36518444731487763170172253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194765038567934736907585349 36518444731487763170172253)
                ·
                  refine ⟨13694416774307911188814595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36518444731487763170172253 13694416774307911188814595)
                  ·
                    refine ⟨20541625161461866783221893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13694416774307911188814595 20541625161461866783221893)
                    ·
                      refine ⟨3851554717774100021854105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20541625161461866783221893 3851554717774100021854105)
                      ·
                        rfl

theorem cell23_7500876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7500876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500876 prefixEnd_7500876 := by exact prefixLift 7500876
  have htrace : WordTrace (prefixWord ++ tailWord_7500876) baseStart_7500876 baseEnd_7500876 := by
    simpa [prefixWord, tailWord_7500876, baseEnd_7500876] using wordTrace_append hprefix tailTrace_7500876
  have hstable : (prefixWord ++ tailWord_7500876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500876).length < 2 ^ (prefixWord ++ tailWord_7500876).sum := by decide
  have hdescent : baseEnd_7500876 < baseStart_7500876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500921 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 1, 1, 3]
def baseStart_7500921 : Nat := 118140960795 + 7500921 * 2 ^ 59
def prefixEnd_7500921 : Nat := 4983230072969 + 3 ^ 40 * 7500921 * 2
def baseEnd_7500921 : Nat := 3851577824403552345791399

theorem tailTrace_7500921 : CollatzResearch.WordTrace tailWord_7500921 prefixEnd_7500921 3851577824403552345791399 := by
  unfold tailWord_7500921
  simp only [CollatzResearch.WordTrace]
  refine ⟨273581064458451747161886617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182387376305634498107924411 273581064458451747161886617)
  ·
    refine ⟨205185798343838810371414963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273581064458451747161886617 205185798343838810371414963)
    ·
      refine ⟨307778697515758215557122445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205185798343838810371414963 307778697515758215557122445)
      ·
        refine ⟨115417011568409330833920917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307778697515758215557122445 115417011568409330833920917)
        ·
          refine ⟨5410172417269187382840043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115417011568409330833920917 5410172417269187382840043)
          ·
            refine ⟨8115258625903781074260065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410172417269187382840043 8115258625903781074260065)
            ·
              refine ⟨6086443969427835805695049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115258625903781074260065 6086443969427835805695049)
              ·
                refine ⟨4564832977070876854271287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086443969427835805695049 4564832977070876854271287)
                ·
                  refine ⟨6847249465606315281406931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564832977070876854271287 6847249465606315281406931)
                  ·
                    refine ⟨10270874198409472922110397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847249465606315281406931 10270874198409472922110397)
                    ·
                      refine ⟨3851577824403552345791399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270874198409472922110397 3851577824403552345791399)
                      ·
                        rfl

theorem cell23_7500921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_7500921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500921 prefixEnd_7500921 := by exact prefixLift 7500921
  have htrace : WordTrace (prefixWord ++ tailWord_7500921) baseStart_7500921 baseEnd_7500921 := by
    simpa [prefixWord, tailWord_7500921, baseEnd_7500921] using wordTrace_append hprefix tailTrace_7500921
  have hstable : (prefixWord ++ tailWord_7500921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500921).length < 2 ^ (prefixWord ++ tailWord_7500921).sum := by decide
  have hdescent : baseEnd_7500921 < baseStart_7500921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500933 : List Nat := [1, 3, 1, 1, 6, 2, 1, 8]
def baseStart_7500933 : Nat := 118140960795 + 7500933 * 2 ^ 59
def prefixEnd_7500933 : Nat := 4983230072969 + 3 ^ 40 * 7500933 * 2
def baseEnd_7500933 : Nat := 142651258747089122179309

theorem tailTrace_7500933 : CollatzResearch.WordTrace tailWord_7500933 prefixEnd_7500933 142651258747089122179309 := by
  unfold tailWord_7500933
  simp only [CollatzResearch.WordTrace]
  refine ⟨273581502134408273211323453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182387668089605515474215635 273581502134408273211323453)
  ·
    refine ⟨102593063300403102454246295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273581502134408273211323453 102593063300403102454246295)
    ·
      refine ⟨153889594950604653681369443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102593063300403102454246295 153889594950604653681369443)
      ·
        refine ⟨230834392425906980522054165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153889594950604653681369443 230834392425906980522054165)
        ·
          refine ⟨10820362144964389711971289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230834392425906980522054165 10820362144964389711971289)
          ·
            refine ⟨8115271608723292283978467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10820362144964389711971289 8115271608723292283978467)
            ·
              refine ⟨12172907413084938425967701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115271608723292283978467 12172907413084938425967701)
              ·
                refine ⟨142651258747089122179309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12172907413084938425967701 142651258747089122179309)
                ·
                  rfl

theorem cell23_7500933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 8].length) (baseStart_7500933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500933 prefixEnd_7500933 := by exact prefixLift 7500933
  have htrace : WordTrace (prefixWord ++ tailWord_7500933) baseStart_7500933 baseEnd_7500933 := by
    simpa [prefixWord, tailWord_7500933, baseEnd_7500933] using wordTrace_append hprefix tailTrace_7500933
  have hstable : (prefixWord ++ tailWord_7500933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500933).length < 2 ^ (prefixWord ++ tailWord_7500933).sum := by decide
  have hdescent : baseEnd_7500933 < baseStart_7500933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500977 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_7500977 : Nat := 118140960795 + 7500977 * 2 ^ 59
def prefixEnd_7500977 : Nat := 4983230072969 + 3 ^ 40 * 7500977 * 2
def baseEnd_7500977 : Nat := 3851606579320204126691141

theorem tailTrace_7500977 : CollatzResearch.WordTrace tailWord_7500977 prefixEnd_7500977 3851606579320204126691141 := by
  unfold tailWord_7500977
  simp only [CollatzResearch.WordTrace]
  refine ⟨273583106946248868725925185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182388737964165912483950123 273583106946248868725925185)
  ·
    refine ⟨205187330209686651544443889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273583106946248868725925185 205187330209686651544443889)
    ·
      refine ⟨153890497657264988658332917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205187330209686651544443889 153890497657264988658332917)
      ·
        refine ⟨14427234155368592686718711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153890497657264988658332917 14427234155368592686718711)
        ·
          refine ⟨21640851233052889030078067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427234155368592686718711 21640851233052889030078067)
          ·
            refine ⟨32461276849579333545117101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640851233052889030078067 32461276849579333545117101)
            ·
              refine ⟨12172978818592250079418913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32461276849579333545117101 12172978818592250079418913)
              ·
                refine ⟨9129734113944187559564185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12172978818592250079418913 9129734113944187559564185)
                ·
                  refine ⟨6847300585458140669673139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9129734113944187559564185 6847300585458140669673139)
                  ·
                    refine ⟨10270950878187211004509709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847300585458140669673139 10270950878187211004509709)
                    ·
                      refine ⟨3851606579320204126691141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10270950878187211004509709 3851606579320204126691141)
                      ·
                        rfl

theorem cell23_7500977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_7500977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500977 prefixEnd_7500977 := by exact prefixLift 7500977
  have htrace : WordTrace (prefixWord ++ tailWord_7500977) baseStart_7500977 baseEnd_7500977 := by
    simpa [prefixWord, tailWord_7500977, baseEnd_7500977] using wordTrace_append hprefix tailTrace_7500977
  have hstable : (prefixWord ++ tailWord_7500977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500977).length < 2 ^ (prefixWord ++ tailWord_7500977).sum := by decide
  have hdescent : baseEnd_7500977 < baseStart_7500977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7500986 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_7500986 : Nat := 118140960795 + 7500986 * 2 ^ 59
def prefixEnd_7500986 : Nat := 4983230072969 + 3 ^ 40 * 7500986 * 2
def baseEnd_7500986 : Nat := 3851611200646094591478599

theorem tailTrace_7500986 : CollatzResearch.WordTrace tailWord_7500986 prefixEnd_7500986 3851611200646094591478599 := by
  unfold tailWord_7500986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68395858800804065815750703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182388956802144175508668541 68395858800804065815750703)
  ·
    refine ⟨102593788201206098723626055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68395858800804065815750703 102593788201206098723626055)
    ·
      refine ⟨153890682301809148085439083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102593788201206098723626055 153890682301809148085439083)
      ·
        refine ⟨230836023452713722128158625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153890682301809148085439083 230836023452713722128158625)
        ·
          refine ⟨173127017589535291596118969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230836023452713722128158625 173127017589535291596118969)
          ·
            refine ⟨129845263192151468697089227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173127017589535291596118969 129845263192151468697089227)
            ·
              refine ⟨194767894788227203045633841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129845263192151468697089227 194767894788227203045633841)
              ·
                refine ⟨146075921091170402284225381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194767894788227203045633841 146075921091170402284225381)
                ·
                  refine ⟨27389235204594450428292259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146075921091170402284225381 27389235204594450428292259)
                  ·
                    refine ⟨41083852806891675642438389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27389235204594450428292259 41083852806891675642438389)
                    ·
                      refine ⟨3851611200646094591478599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41083852806891675642438389 3851611200646094591478599)
                      ·
                        rfl

theorem cell23_7500986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_7500986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7500986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7500986 prefixEnd_7500986 := by exact prefixLift 7500986
  have htrace : WordTrace (prefixWord ++ tailWord_7500986) baseStart_7500986 baseEnd_7500986 := by
    simpa [prefixWord, tailWord_7500986, baseEnd_7500986] using wordTrace_append hprefix tailTrace_7500986
  have hstable : (prefixWord ++ tailWord_7500986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7500986).length < 2 ^ (prefixWord ++ tailWord_7500986).sum := by decide
  have hdescent : baseEnd_7500986 < baseStart_7500986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7500986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501000 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_7501000 : Nat := 118140960795 + 7501000 * 2 ^ 59
def prefixEnd_7501000 : Nat := 4983230072969 + 3 ^ 40 * 7501000 * 2
def baseEnd_7501000 : Nat := 3851618389375257536703535

theorem tailTrace_7501000 : CollatzResearch.WordTrace tailWord_7501000 prefixEnd_7501000 3851618389375257536703535 := by
  unfold tailWord_7501000
  simp only [CollatzResearch.WordTrace]
  refine ⟨136791972912582771827006227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182389297216777029102674969 136791972912582771827006227)
  ·
    refine ⟨205187959368874157740509341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136791972912582771827006227 205187959368874157740509341)
    ·
      refine ⟨76945484763327809152691003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205187959368874157740509341 76945484763327809152691003)
      ·
        refine ⟨115418227144991713729036505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76945484763327809152691003 115418227144991713729036505)
        ·
          refine ⟨86563670358743785296777379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115418227144991713729036505 86563670358743785296777379)
          ·
            refine ⟨129845505538115677945166069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86563670358743785296777379 129845505538115677945166069)
            ·
              refine ⟨12173016144198344807359319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129845505538115677945166069 12173016144198344807359319)
              ·
                refine ⟨18259524216297517211038979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173016144198344807359319 18259524216297517211038979)
                ·
                  refine ⟨27389286324446275816558469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18259524216297517211038979 27389286324446275816558469)
                  ·
                    refine ⟨5135491185833676715604713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27389286324446275816558469 5135491185833676715604713)
                    ·
                      refine ⟨3851618389375257536703535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135491185833676715604713 3851618389375257536703535)
                      ·
                        rfl

theorem cell23_7501000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_7501000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501000 prefixEnd_7501000 := by exact prefixLift 7501000
  have htrace : WordTrace (prefixWord ++ tailWord_7501000) baseStart_7501000 baseEnd_7501000 := by
    simpa [prefixWord, tailWord_7501000, baseEnd_7501000] using wordTrace_append hprefix tailTrace_7501000
  have hstable : (prefixWord ++ tailWord_7501000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501000).length < 2 ^ (prefixWord ++ tailWord_7501000).sum := by decide
  have hdescent : baseEnd_7501000 < baseStart_7501000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501070 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_7501070 : Nat := 118140960795 + 7501070 * 2 ^ 59
def prefixEnd_7501070 : Nat := 4983230072969 + 3 ^ 40 * 7501070 * 2
def baseEnd_7501070 : Nat := 1283884777673690754276071

theorem tailTrace_7501070 : CollatzResearch.WordTrace tailWord_7501070 prefixEnd_7501070 1283884777673690754276071 := by
  unfold tailWord_7501070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34198312366863993201132583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182390999289941297072707109 34198312366863993201132583)
  ·
    refine ⟨51297468550295989801698875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34198312366863993201132583 51297468550295989801698875)
    ·
      refine ⟨76946202825443984702548313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51297468550295989801698875 76946202825443984702548313)
      ·
        refine ⟨57709652119082988526911235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76946202825443984702548313 57709652119082988526911235)
        ·
          refine ⟨86564478178624482790366853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57709652119082988526911235 86564478178624482790366853)
          ·
            refine ⟨16230839658492090523193785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86564478178624482790366853 16230839658492090523193785)
            ·
              refine ⟨12173129743869067892395339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16230839658492090523193785 12173129743869067892395339)
              ·
                refine ⟨18259694615803601838593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173129743869067892395339 18259694615803601838593009)
                ·
                  refine ⟨13694770961852701378944757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18259694615803601838593009 13694770961852701378944757)
                  ·
                    refine ⟨1283884777673690754276071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13694770961852701378944757 1283884777673690754276071)
                    ·
                      rfl

theorem cell23_7501070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_7501070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501070 prefixEnd_7501070 := by exact prefixLift 7501070
  have htrace : WordTrace (prefixWord ++ tailWord_7501070) baseStart_7501070 baseEnd_7501070 := by
    simpa [prefixWord, tailWord_7501070, baseEnd_7501070] using wordTrace_append hprefix tailTrace_7501070
  have hstable : (prefixWord ++ tailWord_7501070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501070).length < 2 ^ (prefixWord ++ tailWord_7501070).sum := by decide
  have hdescent : baseEnd_7501070 < baseStart_7501070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501124 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7501124 : Nat := 118140960795 + 7501124 * 2 ^ 59
def prefixEnd_7501124 : Nat := 4983230072969 + 3 ^ 40 * 7501124 * 2
def baseEnd_7501124 : Nat := 3851682060976415051552965

theorem tailTrace_7501124 : CollatzResearch.WordTrace tailWord_7501124 prefixEnd_7501124 3851682060976415051552965 := by
  unfold tailWord_7501124
  simp only [CollatzResearch.WordTrace]
  refine ⟨136794234238358156415763213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182392312317810875221017617 136794234238358156415763213)
  ·
    refine ⟨51297837839384308655911205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136794234238358156415763213 51297837839384308655911205)
    ·
      refine ⟨9618344594884557872983351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51297837839384308655911205 9618344594884557872983351)
      ·
        refine ⟨14427516892326836809475027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618344594884557872983351 14427516892326836809475027)
        ·
          refine ⟨21641275338490255214212541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427516892326836809475027 21641275338490255214212541)
          ·
            refine ⟨8115478251933845705329703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21641275338490255214212541 8115478251933845705329703)
            ·
              refine ⟨12173217377900768557994555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115478251933845705329703 12173217377900768557994555)
              ·
                refine ⟨18259826066851152836991833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173217377900768557994555 18259826066851152836991833)
                ·
                  refine ⟨13694869550138364627743875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18259826066851152836991833 13694869550138364627743875)
                  ·
                    refine ⟨20542304325207546941615813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13694869550138364627743875 20542304325207546941615813)
                    ·
                      refine ⟨3851682060976415051552965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20542304325207546941615813 3851682060976415051552965)
                      ·
                        rfl

theorem cell23_7501124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7501124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501124 prefixEnd_7501124 := by exact prefixLift 7501124
  have htrace : WordTrace (prefixWord ++ tailWord_7501124) baseStart_7501124 baseEnd_7501124 := by
    simpa [prefixWord, tailWord_7501124, baseEnd_7501124] using wordTrace_append hprefix tailTrace_7501124
  have hstable : (prefixWord ++ tailWord_7501124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501124).length < 2 ^ (prefixWord ++ tailWord_7501124).sum := by decide
  have hdescent : baseEnd_7501124 < baseStart_7501124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501127 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_7501127 : Nat := 118140960795 + 7501127 * 2 ^ 59
def prefixEnd_7501127 : Nat := 4983230072969 + 3 ^ 40 * 7501127 * 2
def baseEnd_7501127 : Nat := 3851683601418378539815451

theorem tailTrace_7501127 : CollatzResearch.WordTrace tailWord_7501127 prefixEnd_7501127 3851683601418378539815451 := by
  unfold tailWord_7501127
  simp only [CollatzResearch.WordTrace]
  refine ⟨273588577895705444343885635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182392385263803629562590423 273588577895705444343885635)
  ·
    refine ⟨410382866843558166515828453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273588577895705444343885635 410382866843558166515828453)
    ·
      refine ⟨76946787533167156221717835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410382866843558166515828453 76946787533167156221717835)
      ·
        refine ⟨115420181299750734332576753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76946787533167156221717835 115420181299750734332576753)
        ·
          refine ⟨86565135974813050749432565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115420181299750734332576753 86565135974813050749432565)
          ·
            refine ⟨8115481497638723507759303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86565135974813050749432565 8115481497638723507759303)
            ·
              refine ⟨12173222246458085261638955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115481497638723507759303 12173222246458085261638955)
              ·
                refine ⟨18259833369687127892458433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173222246458085261638955 18259833369687127892458433)
                ·
                  refine ⟨13694875027265345919343825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18259833369687127892458433 13694875027265345919343825)
                  ·
                    refine ⟨10271156270449009439507869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13694875027265345919343825 10271156270449009439507869)
                    ·
                      refine ⟨3851683601418378539815451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271156270449009439507869 3851683601418378539815451)
                      ·
                        rfl

theorem cell23_7501127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_7501127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501127 prefixEnd_7501127 := by exact prefixLift 7501127
  have htrace : WordTrace (prefixWord ++ tailWord_7501127) baseStart_7501127 baseEnd_7501127 := by
    simpa [prefixWord, tailWord_7501127, baseEnd_7501127] using wordTrace_append hprefix tailTrace_7501127
  have hstable : (prefixWord ++ tailWord_7501127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501127).length < 2 ^ (prefixWord ++ tailWord_7501127).sum := by decide
  have hdescent : baseEnd_7501127 < baseStart_7501127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501157 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_7501157 : Nat := 118140960795 + 7501157 * 2 ^ 59
def prefixEnd_7501157 : Nat := 4983230072969 + 3 ^ 40 * 7501157 * 2
def baseEnd_7501157 : Nat := 3851699005838013422440313

theorem tailTrace_7501157 : CollatzResearch.WordTrace tailWord_7501157 prefixEnd_7501157 3851699005838013422440313 := by
  unfold tailWord_7501157
  simp only [CollatzResearch.WordTrace]
  refine ⟨273589672085596759467477725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182393114723731172978318483 273589672085596759467477725)
  ·
    refine ⟨102596127032098784800304147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273589672085596759467477725 102596127032098784800304147)
    ·
      refine ⟨153894190548148177200456221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102596127032098784800304147 153894190548148177200456221)
      ·
        refine ⟨57710321455555566450171083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153894190548148177200456221 57710321455555566450171083)
        ·
          refine ⟨86565482183333349675256625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57710321455555566450171083 86565482183333349675256625)
          ·
            refine ⟨64924111637500012256442469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86565482183333349675256625 64924111637500012256442469)
            ·
              refine ⟨12173270932031252298082963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64924111637500012256442469 12173270932031252298082963)
              ·
                refine ⟨18259906398046878447124445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173270932031252298082963 18259906398046878447124445)
                ·
                  refine ⟨6847464899267579417671667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18259906398046878447124445 6847464899267579417671667)
                  ·
                    refine ⟨10271197348901369126507501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847464899267579417671667 10271197348901369126507501)
                    ·
                      refine ⟨3851699005838013422440313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271197348901369126507501 3851699005838013422440313)
                      ·
                        rfl

theorem cell23_7501157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_7501157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501157 prefixEnd_7501157 := by exact prefixLift 7501157
  have htrace : WordTrace (prefixWord ++ tailWord_7501157) baseStart_7501157 baseEnd_7501157 := by
    simpa [prefixWord, tailWord_7501157, baseEnd_7501157] using wordTrace_append hprefix tailTrace_7501157
  have hstable : (prefixWord ++ tailWord_7501157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501157).length < 2 ^ (prefixWord ++ tailWord_7501157).sum := by decide
  have hdescent : baseEnd_7501157 < baseStart_7501157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501180 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_7501180 : Nat := 118140960795 + 7501180 * 2 ^ 59
def prefixEnd_7501180 : Nat := 4983230072969 + 3 ^ 40 * 7501180 * 2
def baseEnd_7501180 : Nat := 3851710815893066832452707

theorem tailTrace_7501180 : CollatzResearch.WordTrace tailWord_7501180 prefixEnd_7501180 3851710815893066832452707 := by
  unfold tailWord_7501180
  simp only [CollatzResearch.WordTrace]
  refine ⟨136795255482256717197782497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182393673976342289597043329 136795255482256717197782497)
  ·
    refine ⟨102596441611692537898336873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136795255482256717197782497 102596441611692537898336873)
    ·
      refine ⟨76947331208769403423752655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102596441611692537898336873 76947331208769403423752655)
      ·
        refine ⟨115420996813154105135628983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76947331208769403423752655 115420996813154105135628983)
        ·
          refine ⟨173131495219731157703443475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115420996813154105135628983 173131495219731157703443475)
          ·
            refine ⟨259697242829596736555165213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173131495219731157703443475 259697242829596736555165213)
            ·
              refine ⟨97386466061098776208186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259697242829596736555165213 97386466061098776208186955)
              ·
                refine ⟨146079699091648164312280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97386466061098776208186955 146079699091648164312280433)
                ·
                  refine ⟨109559774318736123234210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146079699091648164312280433 109559774318736123234210325)
                  ·
                    refine ⟨5135614421190755776603609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109559774318736123234210325 5135614421190755776603609)
                    ·
                      refine ⟨3851710815893066832452707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135614421190755776603609 3851710815893066832452707)
                      ·
                        rfl

theorem cell23_7501180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_7501180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501180 prefixEnd_7501180 := by exact prefixLift 7501180
  have htrace : WordTrace (prefixWord ++ tailWord_7501180) baseStart_7501180 baseEnd_7501180 := by
    simpa [prefixWord, tailWord_7501180, baseEnd_7501180] using wordTrace_append hprefix tailTrace_7501180
  have hstable : (prefixWord ++ tailWord_7501180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501180).length < 2 ^ (prefixWord ++ tailWord_7501180).sum := by decide
  have hdescent : baseEnd_7501180 < baseStart_7501180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501191 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_7501191 : Nat := 118140960795 + 7501191 * 2 ^ 59
def prefixEnd_7501191 : Nat := 4983230072969 + 3 ^ 40 * 7501191 * 2
def baseEnd_7501191 : Nat := 3851716464180266289415157

theorem tailTrace_7501191 : CollatzResearch.WordTrace tailWord_7501191 prefixEnd_7501191 3851716464180266289415157 := by
  unfold tailWord_7501191
  simp only [CollatzResearch.WordTrace]
  refine ⟨273590912167473583274215427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182393941444982388849476951 273590912167473583274215427)
  ·
    refine ⟨410386368251210374911323141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273590912167473583274215427 410386368251210374911323141)
    ·
      refine ⟨76947444047101945295873089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410386368251210374911323141 76947444047101945295873089)
      ·
        refine ⟨57710583035326458971904817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76947444047101945295873089 57710583035326458971904817)
        ·
          refine ⟨43282937276494844228928613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57710583035326458971904817 43282937276494844228928613)
          ·
            refine ⟨8115550739342783292924115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43282937276494844228928613 8115550739342783292924115)
            ·
              refine ⟨12173326109014174939386173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115550739342783292924115 12173326109014174939386173)
              ·
                refine ⟨4564997290880315602269815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12173326109014174939386173 4564997290880315602269815)
                ·
                  refine ⟨6847495936320473403404723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564997290880315602269815 6847495936320473403404723)
                  ·
                    refine ⟨10271243904480710105107085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847495936320473403404723 10271243904480710105107085)
                    ·
                      refine ⟨3851716464180266289415157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271243904480710105107085 3851716464180266289415157)
                      ·
                        rfl

theorem cell23_7501191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_7501191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501191 prefixEnd_7501191 := by exact prefixLift 7501191
  have htrace : WordTrace (prefixWord ++ tailWord_7501191) baseStart_7501191 baseEnd_7501191 := by
    simpa [prefixWord, tailWord_7501191, baseEnd_7501191] using wordTrace_append hprefix tailTrace_7501191
  have hstable : (prefixWord ++ tailWord_7501191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501191).length < 2 ^ (prefixWord ++ tailWord_7501191).sum := by decide
  have hdescent : baseEnd_7501191 < baseStart_7501191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501208 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7501208 : Nat := 118140960795 + 7501208 * 2 ^ 59
def prefixEnd_7501208 : Nat := 4983230072969 + 3 ^ 40 * 7501208 * 2
def baseEnd_7501208 : Nat := 3851725193351392722902579

theorem tailTrace_7501208 : CollatzResearch.WordTrace tailWord_7501208 prefixEnd_7501208 3851725193351392722902579 := by
  unfold tailWord_7501208
  simp only [CollatzResearch.WordTrace]
  refine ⟨136795766104205997588792139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182394354805607996785056185 136795766104205997588792139)
  ·
    refine ⟨205193649156308996383188209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136795766104205997588792139 205193649156308996383188209)
    ·
      refine ⟨153895236867231747287391157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205193649156308996383188209 153895236867231747287391157)
      ·
        refine ⟨14427678456302976308192921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153895236867231747287391157 14427678456302976308192921)
        ·
          refine ⟨10820758842227232231144691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14427678456302976308192921 10820758842227232231144691)
          ·
            refine ⟨16231138263340848346717037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10820758842227232231144691 16231138263340848346717037)
            ·
              refine ⟨6086676848752818130018889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16231138263340848346717037 6086676848752818130018889)
              ·
                refine ⟨4565007636564613597514167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086676848752818130018889 4565007636564613597514167)
                ·
                  refine ⟨6847511454846920396271251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565007636564613597514167 6847511454846920396271251)
                  ·
                    refine ⟨10271267182270380594406877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847511454846920396271251 10271267182270380594406877)
                    ·
                      refine ⟨3851725193351392722902579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271267182270380594406877 3851725193351392722902579)
                      ·
                        rfl

theorem cell23_7501208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7501208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501208 prefixEnd_7501208 := by exact prefixLift 7501208
  have htrace : WordTrace (prefixWord ++ tailWord_7501208) baseStart_7501208 baseEnd_7501208 := by
    simpa [prefixWord, tailWord_7501208, baseEnd_7501208] using wordTrace_append hprefix tailTrace_7501208
  have hstable : (prefixWord ++ tailWord_7501208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501208).length < 2 ^ (prefixWord ++ tailWord_7501208).sum := by decide
  have hdescent : baseEnd_7501208 < baseStart_7501208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501340 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7501340 : Nat := 118140960795 + 7501340 * 2 ^ 59
def prefixEnd_7501340 : Nat := 4983230072969 + 3 ^ 40 * 7501340 * 2
def baseEnd_7501340 : Nat := 1283930990932595402150657

theorem tailTrace_7501340 : CollatzResearch.WordTrace tailWord_7501340 prefixEnd_7501340 1283930990932595402150657 := by
  unfold tailWord_7501340
  simp only [CollatzResearch.WordTrace]
  refine ⟨136798173321966890860694737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182397564429289187814259649 136798173321966890860694737)
  ·
    refine ⟨102598629991475168145521053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136798173321966890860694737 102598629991475168145521053)
    ·
      refine ⟨38474486246803188054570395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102598629991475168145521053 38474486246803188054570395)
      ·
        refine ⟨57711729370204782081855593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38474486246803188054570395 57711729370204782081855593)
        ·
          refine ⟨43283797027653586561391695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57711729370204782081855593 43283797027653586561391695)
          ·
            refine ⟨64925695541480379842087543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43283797027653586561391695 64925695541480379842087543)
            ·
              refine ⟨97388543312220569763131315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64925695541480379842087543 97388543312220569763131315)
              ·
                refine ⟨146082814968330854644696973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97388543312220569763131315 146082814968330854644696973)
                ·
                  refine ⟨54781055613124070491761365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146082814968330854644696973 54781055613124070491761365)
                  ·
                    refine ⟨1283930990932595402150657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54781055613124070491761365 1283930990932595402150657)
                    ·
                      rfl

theorem cell23_7501340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7501340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501340 prefixEnd_7501340 := by exact prefixLift 7501340
  have htrace : WordTrace (prefixWord ++ tailWord_7501340) baseStart_7501340 baseEnd_7501340 := by
    simpa [prefixWord, tailWord_7501340, baseEnd_7501340] using wordTrace_append hprefix tailTrace_7501340
  have hstable : (prefixWord ++ tailWord_7501340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501340).length < 2 ^ (prefixWord ++ tailWord_7501340).sum := by decide
  have hdescent : baseEnd_7501340 < baseStart_7501340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501342 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7501342 : Nat := 118140960795 + 7501342 * 2 ^ 59
def prefixEnd_7501342 : Nat := 4983230072969 + 3 ^ 40 * 7501342 * 2
def baseEnd_7501342 : Nat := 3851793999759095198626963

theorem tailTrace_7501342 : CollatzResearch.WordTrace tailWord_7501342 prefixEnd_7501342 3851793999759095198626963 := by
  unfold tailWord_7501342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34199552448740817007870285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182397613059951024041974853 34199552448740817007870285)
  ·
    refine ⟨12824832168277806377951357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34199552448740817007870285 12824832168277806377951357)
    ·
      refine ⟨4809312063104177391731759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12824832168277806377951357 4809312063104177391731759)
      ·
        refine ⟨7213968094656266087597639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809312063104177391731759 7213968094656266087597639)
        ·
          refine ⟨10820952141984399131396459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213968094656266087597639 10820952141984399131396459)
          ·
            refine ⟨16231428212976598697094689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10820952141984399131396459 16231428212976598697094689)
            ·
              refine ⟨12173571159732449022821017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16231428212976598697094689 12173571159732449022821017)
              ·
                refine ⟨9130178369799336767115763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12173571159732449022821017 9130178369799336767115763)
                ·
                  refine ⟨13695267554699005150673645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130178369799336767115763 13695267554699005150673645)
                  ·
                    refine ⟨5135725333012126931502617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13695267554699005150673645 5135725333012126931502617)
                    ·
                      refine ⟨3851793999759095198626963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135725333012126931502617 3851793999759095198626963)
                      ·
                        rfl

theorem cell23_7501342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7501342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501342 prefixEnd_7501342 := by exact prefixLift 7501342
  have htrace : WordTrace (prefixWord ++ tailWord_7501342) baseStart_7501342 baseEnd_7501342 := by
    simpa [prefixWord, tailWord_7501342, baseEnd_7501342] using wordTrace_append hprefix tailTrace_7501342
  have hstable : (prefixWord ++ tailWord_7501342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501342).length < 2 ^ (prefixWord ++ tailWord_7501342).sum := by decide
  have hdescent : baseEnd_7501342 < baseStart_7501342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501397 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7501397 : Nat := 118140960795 + 7501397 * 2 ^ 59
def prefixEnd_7501397 : Nat := 4983230072969 + 3 ^ 40 * 7501397 * 2
def baseEnd_7501397 : Nat := 3851822241195092483439209

theorem tailTrace_7501397 : CollatzResearch.WordTrace tailWord_7501397 prefixEnd_7501397 3851822241195092483439209 := by
  unfold tailWord_7501397
  simp only [CollatzResearch.WordTrace]
  refine ⟨273598425604727280456214445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182398950403151520304142963 273598425604727280456214445)
  ·
    refine ⟨102599409601772730171080417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273598425604727280456214445 102599409601772730171080417)
    ·
      refine ⟨76949557201329547628310313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102599409601772730171080417 76949557201329547628310313)
      ·
        refine ⟨57712167900997160721232735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76949557201329547628310313 57712167900997160721232735)
        ·
          refine ⟨86568251851495741081849103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712167900997160721232735 86568251851495741081849103)
          ·
            refine ⟨129852377777243611622773655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86568251851495741081849103 129852377777243611622773655)
            ·
              refine ⟨194778566665865417434160483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129852377777243611622773655 194778566665865417434160483)
              ·
                refine ⟨292167849998798126151240725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194778566665865417434160483 292167849998798126151240725)
                ·
                  refine ⟨13695367968693662163339409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292167849998798126151240725 13695367968693662163339409)
                  ·
                    refine ⟨10271525976520246622504557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13695367968693662163339409 10271525976520246622504557)
                    ·
                      refine ⟨3851822241195092483439209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271525976520246622504557 3851822241195092483439209)
                      ·
                        rfl

theorem cell23_7501397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7501397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501397 prefixEnd_7501397 := by exact prefixLift 7501397
  have htrace : WordTrace (prefixWord ++ tailWord_7501397) baseStart_7501397 baseEnd_7501397 := by
    simpa [prefixWord, tailWord_7501397, baseEnd_7501397] using wordTrace_append hprefix tailTrace_7501397
  have hstable : (prefixWord ++ tailWord_7501397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501397).length < 2 ^ (prefixWord ++ tailWord_7501397).sum := by decide
  have hdescent : baseEnd_7501397 < baseStart_7501397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_7501420 : Nat := 118140960795 + 7501420 * 2 ^ 59
def prefixEnd_7501420 : Nat := 4983230072969 + 3 ^ 40 * 7501420 * 2
def baseEnd_7501420 : Nat := 3851834051250145893451603

theorem tailTrace_7501420 : CollatzResearch.WordTrace tailWord_7501420 prefixEnd_7501420 3851834051250145893451603 := by
  unfold tailWord_7501420
  simp only [CollatzResearch.WordTrace]
  refine ⟨136799632241821977692150857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182399509655762636922867809 136799632241821977692150857)
  ·
    refine ⟨102599724181366483269113143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136799632241821977692150857 102599724181366483269113143)
    ·
      refine ⟨153899586272049724903669715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102599724181366483269113143 153899586272049724903669715)
      ·
        refine ⟨230849379408074587355504573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153899586272049724903669715 230849379408074587355504573)
        ·
          refine ⟨86568517278027970258314215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230849379408074587355504573 86568517278027970258314215)
          ·
            refine ⟨129852775917041955387471323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86568517278027970258314215 129852775917041955387471323)
            ·
              refine ⟨194779163875562933081206985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129852775917041955387471323 194779163875562933081206985)
              ·
                refine ⟨146084372906672199810905239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194779163875562933081206985 146084372906672199810905239)
                ·
                  refine ⟨219126559360008299716357859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146084372906672199810905239 219126559360008299716357859)
                  ·
                    refine ⟨328689839040012449574536789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219126559360008299716357859 328689839040012449574536789)
                    ·
                      refine ⟨3851834051250145893451603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328689839040012449574536789 3851834051250145893451603)
                      ·
                        rfl

theorem cell23_7501420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_7501420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501420 prefixEnd_7501420 := by exact prefixLift 7501420
  have htrace : WordTrace (prefixWord ++ tailWord_7501420) baseStart_7501420 baseEnd_7501420 := by
    simpa [prefixWord, tailWord_7501420, baseEnd_7501420] using wordTrace_append hprefix tailTrace_7501420
  have hstable : (prefixWord ++ tailWord_7501420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501420).length < 2 ^ (prefixWord ++ tailWord_7501420).sum := by decide
  have hdescent : baseEnd_7501420 < baseStart_7501420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501447 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 3, 5]
def baseStart_7501447 : Nat := 118140960795 + 7501447 * 2 ^ 59
def prefixEnd_7501447 : Nat := 4983230072969 + 3 ^ 40 * 7501447 * 2
def baseEnd_7501447 : Nat := 1283949305075939095937993

theorem tailTrace_7501447 : CollatzResearch.WordTrace tailWord_7501447 prefixEnd_7501447 1283949305075939095937993 := by
  unfold tailWord_7501447
  simp only [CollatzResearch.WordTrace]
  refine ⟨273600249254546138995534595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182400166169697425997023063 273600249254546138995534595)
  ·
    refine ⟨410400373881819208493301893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273600249254546138995534595 410400373881819208493301893)
    ·
      refine ⟨76950070102841101592494105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410400373881819208493301893 76950070102841101592494105)
      ·
        refine ⟨57712552577130826194370579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76950070102841101592494105 57712552577130826194370579)
        ·
          refine ⟨86568828865696239291555869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712552577130826194370579 86568828865696239291555869)
          ·
            refine ⟨32463310824636089734333451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86568828865696239291555869 32463310824636089734333451)
            ·
              refine ⟨48694966236954134601500177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32463310824636089734333451 48694966236954134601500177)
              ·
                refine ⟨36521224677715600951125133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48694966236954134601500177 36521224677715600951125133)
                ·
                  refine ⟨13695459254143350356671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36521224677715600951125133 13695459254143350356671925)
                  ·
                    refine ⟨1283949305075939095937993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13695459254143350356671925 1283949305075939095937993)
                    ·
                      rfl

theorem cell23_7501447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_7501447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501447 prefixEnd_7501447 := by exact prefixLift 7501447
  have htrace : WordTrace (prefixWord ++ tailWord_7501447) baseStart_7501447 baseEnd_7501447 := by
    simpa [prefixWord, tailWord_7501447, baseEnd_7501447] using wordTrace_append hprefix tailTrace_7501447
  have hstable : (prefixWord ++ tailWord_7501447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501447).length < 2 ^ (prefixWord ++ tailWord_7501447).sum := by decide
  have hdescent : baseEnd_7501447 < baseStart_7501447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501477 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_7501477 : Nat := 118140960795 + 7501477 * 2 ^ 59
def prefixEnd_7501477 : Nat := 4983230072969 + 3 ^ 40 * 7501477 * 2
def baseEnd_7501477 : Nat := 1283954439882484056812947

theorem tailTrace_7501477 : CollatzResearch.WordTrace tailWord_7501477 prefixEnd_7501477 1283954439882484056812947 := by
  unfold tailWord_7501477
  simp only [CollatzResearch.WordTrace]
  refine ⟨273601343444437454119126685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182400895629624969412751123 273601343444437454119126685)
  ·
    refine ⟨102600503791664045294672507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273601343444437454119126685 102600503791664045294672507)
    ·
      refine ⟨153900755687496067942008761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102600503791664045294672507 153900755687496067942008761)
      ·
        refine ⟨115425566765622050956506571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153900755687496067942008761 115425566765622050956506571)
        ·
          refine ⟨173138350148433076434759857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115425566765622050956506571 173138350148433076434759857)
          ·
            refine ⟨129853762611324807326069893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173138350148433076434759857 129853762611324807326069893)
            ·
              refine ⟨24347580489623401373638105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129853762611324807326069893 24347580489623401373638105)
              ·
                refine ⟨18260685367217551030228579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24347580489623401373638105 18260685367217551030228579)
                ·
                  refine ⟨27391028050826326545342869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18260685367217551030228579 27391028050826326545342869)
                  ·
                    refine ⟨1283954439882484056812947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27391028050826326545342869 1283954439882484056812947)
                    ·
                      rfl

theorem cell23_7501477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_7501477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501477 prefixEnd_7501477 := by exact prefixLift 7501477
  have htrace : WordTrace (prefixWord ++ tailWord_7501477) baseStart_7501477 baseEnd_7501477 := by
    simpa [prefixWord, tailWord_7501477, baseEnd_7501477] using wordTrace_append hprefix tailTrace_7501477
  have hstable : (prefixWord ++ tailWord_7501477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501477).length < 2 ^ (prefixWord ++ tailWord_7501477).sum := by decide
  have hdescent : baseEnd_7501477 < baseStart_7501477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501487 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_7501487 : Nat := 118140960795 + 7501487 * 2 ^ 59
def prefixEnd_7501487 : Nat := 4983230072969 + 3 ^ 40 * 7501487 * 2
def baseEnd_7501487 : Nat := 3851868454453997131313795

theorem tailTrace_7501487 : CollatzResearch.WordTrace tailWord_7501487 prefixEnd_7501487 3851868454453997131313795 := by
  unfold tailWord_7501487
  simp only [CollatzResearch.WordTrace]
  refine ⟨273601708174401225826990715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182401138782934150551327143 273601708174401225826990715)
  ·
    refine ⟨410402562261601838740486073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273601708174401225826990715 410402562261601838740486073)
    ·
      refine ⟨307801921696201379055364555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410402562261601838740486073 307801921696201379055364555)
      ·
        refine ⟨461702882544302068583046833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307801921696201379055364555 461702882544302068583046833)
        ·
          refine ⟨346277161908226551437285125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461702882544302068583046833 346277161908226551437285125)
          ·
            refine ⟨64926967857792478394490961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346277161908226551437285125 64926967857792478394490961)
            ·
              refine ⟨48695225893344358795868221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64926967857792478394490961 48695225893344358795868221)
              ·
                refine ⟨18260709710004134548450583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48695225893344358795868221 18260709710004134548450583)
                ·
                  refine ⟨27391064565006201822675875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18260709710004134548450583 27391064565006201822675875)
                  ·
                    refine ⟨41086596847509302734013813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27391064565006201822675875 41086596847509302734013813)
                    ·
                      refine ⟨3851868454453997131313795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41086596847509302734013813 3851868454453997131313795)
                      ·
                        rfl

theorem cell23_7501487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_7501487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501487 prefixEnd_7501487 := by exact prefixLift 7501487
  have htrace : WordTrace (prefixWord ++ tailWord_7501487) baseStart_7501487 baseEnd_7501487 := by
    simpa [prefixWord, tailWord_7501487, baseEnd_7501487] using wordTrace_append hprefix tailTrace_7501487
  have hstable : (prefixWord ++ tailWord_7501487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501487).length < 2 ^ (prefixWord ++ tailWord_7501487).sum := by decide
  have hdescent : baseEnd_7501487 < baseStart_7501487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501497 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7501497 : Nat := 118140960795 + 7501497 * 2 ^ 59
def prefixEnd_7501497 : Nat := 4983230072969 + 3 ^ 40 * 7501497 * 2
def baseEnd_7501497 : Nat := 3851873589260542092188749

theorem tailTrace_7501497 : CollatzResearch.WordTrace tailWord_7501497 prefixEnd_7501497 3851873589260542092188749 := by
  unfold tailWord_7501497
  simp only [CollatzResearch.WordTrace]
  refine ⟨273602072904364997534854745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182401381936243331689903163 273602072904364997534854745)
  ·
    refine ⟨205201554678273748151141059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273602072904364997534854745 205201554678273748151141059)
    ·
      refine ⟨307802332017410622226711589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205201554678273748151141059 307802332017410622226711589)
      ·
        refine ⟨57712937253264491667508423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307802332017410622226711589 57712937253264491667508423)
        ·
          refine ⟨86569405879896737501262635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712937253264491667508423 86569405879896737501262635)
          ·
            refine ⟨129854108819845106251893953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86569405879896737501262635 129854108819845106251893953)
            ·
              refine ⟨97390581614883829688920465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129854108819845106251893953 97390581614883829688920465)
              ·
                refine ⟨73042936211162872266690349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97390581614883829688920465 73042936211162872266690349)
                ·
                  refine ⟨27391101079186077100008881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73042936211162872266690349 27391101079186077100008881)
                  ·
                    refine ⟨20543325809389557825006661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27391101079186077100008881 20543325809389557825006661)
                    ·
                      refine ⟨3851873589260542092188749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20543325809389557825006661 3851873589260542092188749)
                      ·
                        rfl

theorem cell23_7501497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7501497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501497 prefixEnd_7501497 := by exact prefixLift 7501497
  have htrace : WordTrace (prefixWord ++ tailWord_7501497) baseStart_7501497 baseEnd_7501497 := by
    simpa [prefixWord, tailWord_7501497, baseEnd_7501497] using wordTrace_append hprefix tailTrace_7501497
  have hstable : (prefixWord ++ tailWord_7501497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501497).length < 2 ^ (prefixWord ++ tailWord_7501497).sum := by decide
  have hdescent : baseEnd_7501497 < baseStart_7501497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501511 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 2, 4]
def baseStart_7501511 : Nat := 118140960795 + 7501511 * 2 ^ 59
def prefixEnd_7501511 : Nat := 4983230072969 + 3 ^ 40 * 7501511 * 2
def baseEnd_7501511 : Nat := 1283960259329901679137895

theorem tailTrace_7501511 : CollatzResearch.WordTrace tailWord_7501511 prefixEnd_7501511 1283960259329901679137895 := by
  unfold tailWord_7501511
  simp only [CollatzResearch.WordTrace]
  refine ⟨273602583526314277925864387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182401722350876185283909591 273602583526314277925864387)
  ·
    refine ⟨410403875289471416888796581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273602583526314277925864387 410403875289471416888796581)
    ·
      refine ⟨76950726616775890666649359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410403875289471416888796581 76950726616775890666649359)
      ·
        refine ⟨115426089925163835999974039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76950726616775890666649359 115426089925163835999974039)
        ·
          refine ⟨173139134887745753999961059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115426089925163835999974039 173139134887745753999961059)
          ·
            refine ⟨259708702331618630999941589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173139134887745753999961059 259708702331618630999941589)
            ·
              refine ⟨6086922710897311664061131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259708702331618630999941589 6086922710897311664061131)
              ·
                refine ⟨9130384066345967496091697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086922710897311664061131 9130384066345967496091697)
                ·
                  refine ⟨6847788049759475622068773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130384066345967496091697 6847788049759475622068773)
                  ·
                    refine ⟨1283960259329901679137895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6847788049759475622068773 1283960259329901679137895)
                    ·
                      rfl

theorem cell23_7501511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_7501511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501511 prefixEnd_7501511 := by exact prefixLift 7501511
  have htrace : WordTrace (prefixWord ++ tailWord_7501511) baseStart_7501511 baseEnd_7501511 := by
    simpa [prefixWord, tailWord_7501511, baseEnd_7501511] using wordTrace_append hprefix tailTrace_7501511
  have hstable : (prefixWord ++ tailWord_7501511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501511).length < 2 ^ (prefixWord ++ tailWord_7501511).sum := by decide
  have hdescent : baseEnd_7501511 < baseStart_7501511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501514 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_7501514 : Nat := 118140960795 + 7501514 * 2 ^ 59
def prefixEnd_7501514 : Nat := 4983230072969 + 3 ^ 40 * 7501514 * 2
def baseEnd_7501514 : Nat := 3851882318431668525676171

theorem tailTrace_7501514 : CollatzResearch.WordTrace tailWord_7501514 prefixEnd_7501514 3851882318431668525676171 := by
  unfold tailWord_7501514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400673236325852359555899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182401795296868939625482397 68400673236325852359555899)
  ·
    refine ⟨102601009854488778539333849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68400673236325852359555899 102601009854488778539333849)
    ·
      refine ⟨76950757390866583904500387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102601009854488778539333849 76950757390866583904500387)
      ·
        refine ⟨115426136086299875856750581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76950757390866583904500387 115426136086299875856750581)
        ·
          refine ⟨10821200258090613361570367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115426136086299875856750581 10821200258090613361570367)
          ·
            refine ⟨16231800387135920042355551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821200258090613361570367 16231800387135920042355551)
            ·
              refine ⟨24347700580703880063533327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16231800387135920042355551 24347700580703880063533327)
              ·
                refine ⟨36521550871055820095299991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24347700580703880063533327 36521550871055820095299991)
                ·
                  refine ⟨54782326306583730142949987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36521550871055820095299991 54782326306583730142949987)
                  ·
                    refine ⟨82173489459875595214424981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54782326306583730142949987 82173489459875595214424981)
                    ·
                      refine ⟨3851882318431668525676171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82173489459875595214424981 3851882318431668525676171)
                      ·
                        rfl

theorem cell23_7501514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_7501514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501514 prefixEnd_7501514 := by exact prefixLift 7501514
  have htrace : WordTrace (prefixWord ++ tailWord_7501514) baseStart_7501514 baseEnd_7501514 := by
    simpa [prefixWord, tailWord_7501514, baseEnd_7501514] using wordTrace_append hprefix tailTrace_7501514
  have hstable : (prefixWord ++ tailWord_7501514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501514).length < 2 ^ (prefixWord ++ tailWord_7501514).sum := by decide
  have hdescent : baseEnd_7501514 < baseStart_7501514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501521 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_7501521 : Nat := 118140960795 + 7501521 * 2 ^ 59
def prefixEnd_7501521 : Nat := 4983230072969 + 3 ^ 40 * 7501521 * 2
def baseEnd_7501521 : Nat := 3851885912796249998288639

theorem tailTrace_7501521 : CollatzResearch.WordTrace tailWord_7501521 prefixEnd_7501521 3851885912796249998288639 := by
  unfold tailWord_7501521
  simp only [CollatzResearch.WordTrace]
  refine ⟨273602948256278049633728417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182401965504185366422485611 273602948256278049633728417)
  ·
    refine ⟨205202211192208537225296313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273602948256278049633728417 205202211192208537225296313)
    ·
      refine ⟨153901658394156402918972235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205202211192208537225296313 153901658394156402918972235)
      ·
        refine ⟨230852487591234604378458353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153901658394156402918972235 230852487591234604378458353)
        ·
          refine ⟨173139365693425953283843765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230852487591234604378458353 173139365693425953283843765)
          ·
            refine ⟨16231815533758683120360353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173139365693425953283843765 16231815533758683120360353)
            ·
              refine ⟨12173861650319012340270265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16231815533758683120360353 12173861650319012340270265)
              ·
                refine ⟨9130396237739259255202699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12173861650319012340270265 9130396237739259255202699)
                ·
                  refine ⟨13695594356608888882804049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130396237739259255202699 13695594356608888882804049)
                  ·
                    refine ⟨10271695767456666662103037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13695594356608888882804049 10271695767456666662103037)
                    ·
                      refine ⟨3851885912796249998288639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271695767456666662103037 3851885912796249998288639)
                      ·
                        rfl

theorem cell23_7501521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_7501521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501521 prefixEnd_7501521 := by exact prefixLift 7501521
  have htrace : WordTrace (prefixWord ++ tailWord_7501521) baseStart_7501521 baseEnd_7501521 := by
    simpa [prefixWord, tailWord_7501521, baseEnd_7501521] using wordTrace_append hprefix tailTrace_7501521
  have hstable : (prefixWord ++ tailWord_7501521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501521).length < 2 ^ (prefixWord ++ tailWord_7501521).sum := by decide
  have hdescent : baseEnd_7501521 < baseStart_7501521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501524 : List Nat := [2, 4, 1, 3, 1, 2, 1, 9]
def baseStart_7501524 : Nat := 118140960795 + 7501524 * 2 ^ 59
def prefixEnd_7501524 : Nat := 4983230072969 + 3 ^ 40 * 7501524 * 2
def baseEnd_7501524 : Nat := 142662498268081980983375

theorem tailTrace_7501524 : CollatzResearch.WordTrace tailWord_7501524 prefixEnd_7501524 142662498268081980983375 := by
  unfold tailWord_7501524
  simp only [CollatzResearch.WordTrace]
  refine ⟨136801528837633590573043813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182402038450178120764058417 136801528837633590573043813)
  ·
    refine ⟨25650286657056298232445715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136801528837633590573043813 25650286657056298232445715)
    ·
      refine ⟨38475429985584447348668573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25650286657056298232445715 38475429985584447348668573)
      ·
        refine ⟨14428286244594167755750715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38475429985584447348668573 14428286244594167755750715)
        ·
          refine ⟨21642429366891251633626073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428286244594167755750715 21642429366891251633626073)
          ·
            refine ⟨16231822025168438725219555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21642429366891251633626073 16231822025168438725219555)
            ·
              refine ⟨24347733037752658087829333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16231822025168438725219555 24347733037752658087829333)
              ·
                refine ⟨142662498268081980983375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24347733037752658087829333 142662498268081980983375)
                ·
                  rfl

theorem cell23_7501524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 9].length) (baseStart_7501524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501524 prefixEnd_7501524 := by exact prefixLift 7501524
  have htrace : WordTrace (prefixWord ++ tailWord_7501524) baseStart_7501524 baseEnd_7501524 := by
    simpa [prefixWord, tailWord_7501524, baseEnd_7501524] using wordTrace_append hprefix tailTrace_7501524
  have hstable : (prefixWord ++ tailWord_7501524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501524).length < 2 ^ (prefixWord ++ tailWord_7501524).sum := by decide
  have hdescent : baseEnd_7501524 < baseStart_7501524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501551 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_7501551 : Nat := 118140960795 + 7501551 * 2 ^ 59
def prefixEnd_7501551 : Nat := 4983230072969 + 3 ^ 40 * 7501551 * 2
def baseEnd_7501551 : Nat := 3851901317215884880913501

theorem tailTrace_7501551 : CollatzResearch.WordTrace tailWord_7501551 prefixEnd_7501551 3851901317215884880913501 := by
  unfold tailWord_7501551
  simp only [CollatzResearch.WordTrace]
  refine ⟨273604042446169364757320507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182402694964112909838213671 273604042446169364757320507)
  ·
    refine ⟨410406063669254047135980761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273604042446169364757320507 410406063669254047135980761)
    ·
      refine ⟨307804547751940535351985571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410406063669254047135980761 307804547751940535351985571)
      ·
        refine ⟨461706821627910803027978357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307804547751940535351985571 461706821627910803027978357)
        ·
          refine ⟨43285014527616637783872971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461706821627910803027978357 43285014527616637783872971)
          ·
            refine ⟨64927521791424956675809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43285014527616637783872971 64927521791424956675809457)
            ·
              refine ⟨48695641343568717506857093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64927521791424956675809457 48695641343568717506857093)
              ·
                refine ⟨9130432751919134532535705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48695641343568717506857093 9130432751919134532535705)
                ·
                  refine ⟨6847824563939350899401779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130432751919134532535705 6847824563939350899401779)
                  ·
                    refine ⟨10271736845909026349102669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6847824563939350899401779 10271736845909026349102669)
                    ·
                      refine ⟨3851901317215884880913501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271736845909026349102669 3851901317215884880913501)
                      ·
                        rfl

theorem cell23_7501551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_7501551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501551 prefixEnd_7501551 := by exact prefixLift 7501551
  have htrace : WordTrace (prefixWord ++ tailWord_7501551) baseStart_7501551 baseEnd_7501551 := by
    simpa [prefixWord, tailWord_7501551, baseEnd_7501551] using wordTrace_append hprefix tailTrace_7501551
  have hstable : (prefixWord ++ tailWord_7501551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501551).length < 2 ^ (prefixWord ++ tailWord_7501551).sum := by decide
  have hdescent : baseEnd_7501551 < baseStart_7501551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501567 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 6]
def baseStart_7501567 : Nat := 118140960795 + 7501567 * 2 ^ 59
def prefixEnd_7501567 : Nat := 4983230072969 + 3 ^ 40 * 7501567 * 2
def baseEnd_7501567 : Nat := 1283969844302118939437809

theorem tailTrace_7501567 : CollatzResearch.WordTrace tailWord_7501567 prefixEnd_7501567 1283969844302118939437809 := by
  unfold tailWord_7501567
  simp only [CollatzResearch.WordTrace]
  refine ⟨273604626014111399489902955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182403084009407599659935303 273604626014111399489902955)
  ·
    refine ⟨410406939021167099234854433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273604626014111399489902955 410406939021167099234854433)
    ·
      refine ⟨307805204265875324426140825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410406939021167099234854433 307805204265875324426140825)
      ·
        refine ⟨230853903199406493319605619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307805204265875324426140825 230853903199406493319605619)
        ·
          refine ⟨346280854799109739979408429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230853903199406493319605619 346280854799109739979408429)
          ·
            refine ⟨129855320549666152492278161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346280854799109739979408429 129855320549666152492278161)
            ·
              refine ⟨97391490412249614369208621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129855320549666152492278161 97391490412249614369208621)
              ·
                refine ⟨36521808904593605388453233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97391490412249614369208621 36521808904593605388453233)
                ·
                  refine ⟨27391356678445204041339925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36521808904593605388453233 27391356678445204041339925)
                  ·
                    refine ⟨1283969844302118939437809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27391356678445204041339925 1283969844302118939437809)
                    ·
                      rfl

theorem cell23_7501567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_7501567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501567 prefixEnd_7501567 := by exact prefixLift 7501567
  have htrace : WordTrace (prefixWord ++ tailWord_7501567) baseStart_7501567 baseEnd_7501567 := by
    simpa [prefixWord, tailWord_7501567, baseEnd_7501567] using wordTrace_append hprefix tailTrace_7501567
  have hstable : (prefixWord ++ tailWord_7501567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501567).length < 2 ^ (prefixWord ++ tailWord_7501567).sum := by decide
  have hdescent : baseEnd_7501567 < baseStart_7501567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501578 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_7501578 : Nat := 118140960795 + 7501578 * 2 ^ 59
def prefixEnd_7501578 : Nat := 4983230072969 + 3 ^ 40 * 7501578 * 2
def baseEnd_7501578 : Nat := 3851915181193556275275877

theorem tailTrace_7501578 : CollatzResearch.WordTrace tailWord_7501578 prefixEnd_7501578 3851915181193556275275877 := by
  unfold tailWord_7501578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68401256804267887092138347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182403351478047698912368925 68401256804267887092138347)
  ·
    refine ⟨102601885206401830638207521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68401256804267887092138347 102601885206401830638207521)
    ·
      refine ⟨76951413904801372978655641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102601885206401830638207521 76951413904801372978655641)
      ·
        refine ⟨57713560428601029733991731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76951413904801372978655641 57713560428601029733991731)
        ·
          refine ⟨86570340642901544600987597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57713560428601029733991731 86570340642901544600987597)
          ·
            refine ⟨32463877741088079225370349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86570340642901544600987597 32463877741088079225370349)
            ·
              refine ⟨12173954152908029709513881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32463877741088079225370349 12173954152908029709513881)
              ·
                refine ⟨9130465614681022282135411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12173954152908029709513881 9130465614681022282135411)
                ·
                  refine ⟨13695698422021533423203117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130465614681022282135411 13695698422021533423203117)
                  ·
                    refine ⟨5135886908258075033701169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13695698422021533423203117 5135886908258075033701169)
                    ·
                      refine ⟨3851915181193556275275877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135886908258075033701169 3851915181193556275275877)
                      ·
                        rfl

theorem cell23_7501578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_7501578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501578 prefixEnd_7501578 := by exact prefixLift 7501578
  have htrace : WordTrace (prefixWord ++ tailWord_7501578) baseStart_7501578 baseEnd_7501578 := by
    simpa [prefixWord, tailWord_7501578, baseEnd_7501578] using wordTrace_append hprefix tailTrace_7501578
  have hstable : (prefixWord ++ tailWord_7501578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501578).length < 2 ^ (prefixWord ++ tailWord_7501578).sum := by decide
  have hdescent : baseEnd_7501578 < baseStart_7501578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501587 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_7501587 : Nat := 118140960795 + 7501587 * 2 ^ 59
def prefixEnd_7501587 : Nat := 4983230072969 + 3 ^ 40 * 7501587 * 2
def baseEnd_7501587 : Nat := 3851919802519446740063335

theorem tailTrace_7501587 : CollatzResearch.WordTrace tailWord_7501587 prefixEnd_7501587 3851919802519446740063335 := by
  unfold tailWord_7501587
  simp only [CollatzResearch.WordTrace]
  refine ⟨273605355474038942905631015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182403570316025961937087343 273605355474038942905631015)
  ·
    refine ⟨410408033211058414358446523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273605355474038942905631015 410408033211058414358446523)
    ·
      refine ⟨615612049816587621537669785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410408033211058414358446523 615612049816587621537669785)
      ·
        refine ⟨461709037362440716153252339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615612049816587621537669785 461709037362440716153252339)
        ·
          refine ⟨692563556043661074229878509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461709037362440716153252339 692563556043661074229878509)
          ·
            refine ⟨259711333516372902836204441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692563556043661074229878509 259711333516372902836204441)
            ·
              refine ⟨194783500137279677127153331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259711333516372902836204441 194783500137279677127153331)
              ·
                refine ⟨292175250205919515690729997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194783500137279677127153331 292175250205919515690729997)
                ·
                  refine ⟨109565718827219818384023749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292175250205919515690729997 109565718827219818384023749)
                  ·
                    refine ⟨20543572280103715947004453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109565718827219818384023749 20543572280103715947004453)
                    ·
                      refine ⟨3851919802519446740063335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20543572280103715947004453 3851919802519446740063335)
                      ·
                        rfl

theorem cell23_7501587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_7501587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501587 prefixEnd_7501587 := by exact prefixLift 7501587
  have htrace : WordTrace (prefixWord ++ tailWord_7501587) baseStart_7501587 baseEnd_7501587 := by
    simpa [prefixWord, tailWord_7501587, baseEnd_7501587] using wordTrace_append hprefix tailTrace_7501587
  have hstable : (prefixWord ++ tailWord_7501587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501587).length < 2 ^ (prefixWord ++ tailWord_7501587).sum := by decide
  have hdescent : baseEnd_7501587 < baseStart_7501587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501591 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_7501591 : Nat := 118140960795 + 7501591 * 2 ^ 59
def prefixEnd_7501591 : Nat := 4983230072969 + 3 ^ 40 * 7501591 * 2
def baseEnd_7501591 : Nat := 3851921856442064724413317

theorem tailTrace_7501591 : CollatzResearch.WordTrace tailWord_7501591 prefixEnd_7501591 3851921856442064724413317 := by
  unfold tailWord_7501591
  simp only [CollatzResearch.WordTrace]
  refine ⟨273605501366024451588776627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182403667577349634392517751 273605501366024451588776627)
  ·
    refine ⟨410408252049036677383164941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273605501366024451588776627 410408252049036677383164941)
    ·
      refine ⟨153903094518388754018686853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410408252049036677383164941 153903094518388754018686853)
      ·
        refine ⟨28856830222197891378503785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153903094518388754018686853 28856830222197891378503785)
        ·
          refine ⟨21642622666648418533877839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28856830222197891378503785 21642622666648418533877839)
          ·
            refine ⟨32463933999972627800816759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642622666648418533877839 32463933999972627800816759)
            ·
              refine ⟨48695900999958941701225139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32463933999972627800816759 48695900999958941701225139)
              ·
                refine ⟨73043851499938412551837709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48695900999958941701225139 73043851499938412551837709)
                ·
                  refine ⟨27391444312476904706939141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73043851499938412551837709 27391444312476904706939141)
                  ·
                    refine ⟨5135895808589419632551089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27391444312476904706939141 5135895808589419632551089)
                    ·
                      refine ⟨3851921856442064724413317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135895808589419632551089 3851921856442064724413317)
                      ·
                        rfl

theorem cell23_7501591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_7501591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501591 prefixEnd_7501591 := by exact prefixLift 7501591
  have htrace : WordTrace (prefixWord ++ tailWord_7501591) baseStart_7501591 baseEnd_7501591 := by
    simpa [prefixWord, tailWord_7501591, baseEnd_7501591] using wordTrace_append hprefix tailTrace_7501591
  have hstable : (prefixWord ++ tailWord_7501591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501591).length < 2 ^ (prefixWord ++ tailWord_7501591).sum := by decide
  have hdescent : baseEnd_7501591 < baseStart_7501591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501594 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_7501594 : Nat := 118140960795 + 7501594 * 2 ^ 59
def prefixEnd_7501594 : Nat := 4983230072969 + 3 ^ 40 * 7501594 * 2
def baseEnd_7501594 : Nat := 3851923396884028212675803

theorem tailTrace_7501594 : CollatzResearch.WordTrace tailWord_7501594 prefixEnd_7501594 3851923396884028212675803 := by
  unfold tailWord_7501594
  simp only [CollatzResearch.WordTrace]
  refine ⟨68401402696253395775283959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182403740523342388734090557 68401402696253395775283959)
  ·
    refine ⟨102602104044380093662925939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68401402696253395775283959 102602104044380093662925939)
    ·
      refine ⟨153903156066570140494388909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102602104044380093662925939 153903156066570140494388909)
      ·
        refine ⟨57713683524963802685395841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153903156066570140494388909 57713683524963802685395841)
        ·
          refine ⟨43285262643722852014046881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57713683524963802685395841 43285262643722852014046881)
          ·
            refine ⟨32463946982792139010535161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43285262643722852014046881 32463946982792139010535161)
            ·
              refine ⟨24347960237094104257901371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32463946982792139010535161 24347960237094104257901371)
              ·
                refine ⟨36521940355641156386852057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24347960237094104257901371 36521940355641156386852057)
                ·
                  refine ⟨27391455266730867290139043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36521940355641156386852057 27391455266730867290139043)
                  ·
                    refine ⟨41087182900096300935208565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27391455266730867290139043 41087182900096300935208565)
                    ·
                      refine ⟨3851923396884028212675803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41087182900096300935208565 3851923396884028212675803)
                      ·
                        rfl

theorem cell23_7501594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_7501594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501594 prefixEnd_7501594 := by exact prefixLift 7501594
  have htrace : WordTrace (prefixWord ++ tailWord_7501594) baseStart_7501594 baseEnd_7501594 := by
    simpa [prefixWord, tailWord_7501594, baseEnd_7501594] using wordTrace_append hprefix tailTrace_7501594
  have hstable : (prefixWord ++ tailWord_7501594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501594).length < 2 ^ (prefixWord ++ tailWord_7501594).sum := by decide
  have hdescent : baseEnd_7501594 < baseStart_7501594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501621 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_7501621 : Nat := 118140960795 + 7501621 * 2 ^ 59
def prefixEnd_7501621 : Nat := 4983230072969 + 3 ^ 40 * 7501621 * 2
def baseEnd_7501621 : Nat := 3851937260861699607038179

theorem tailTrace_7501621 : CollatzResearch.WordTrace tailWord_7501621 prefixEnd_7501621 3851937260861699607038179 := by
  unfold tailWord_7501621
  simp only [CollatzResearch.WordTrace]
  refine ⟨273606595555915766712368717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182404397037277177808245811 273606595555915766712368717)
  ·
    refine ⟨102602473333468412517138269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273606595555915766712368717 102602473333468412517138269)
    ·
      refine ⟨38475927500050654693926851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102602473333468412517138269 38475927500050654693926851)
      ·
        refine ⟨57713891250075982040890277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38475927500050654693926851 57713891250075982040890277)
        ·
          refine ⟨10821354609389246632666927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57713891250075982040890277 10821354609389246632666927)
          ·
            refine ⟨16232031914083869949000391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821354609389246632666927 16232031914083869949000391)
            ·
              refine ⟨24348047871125804923500587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16232031914083869949000391 24348047871125804923500587)
              ·
                refine ⟨36522071806688707385250881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24348047871125804923500587 36522071806688707385250881)
                ·
                  refine ⟨27391553855016530538938161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36522071806688707385250881 27391553855016530538938161)
                  ·
                    refine ⟨20543665391262397904203621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27391553855016530538938161 20543665391262397904203621)
                    ·
                      refine ⟨3851937260861699607038179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20543665391262397904203621 3851937260861699607038179)
                      ·
                        rfl

theorem cell23_7501621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_7501621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501621 prefixEnd_7501621 := by exact prefixLift 7501621
  have htrace : WordTrace (prefixWord ++ tailWord_7501621) baseStart_7501621 baseEnd_7501621 := by
    simpa [prefixWord, tailWord_7501621, baseEnd_7501621] using wordTrace_append hprefix tailTrace_7501621
  have hstable : (prefixWord ++ tailWord_7501621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501621).length < 2 ^ (prefixWord ++ tailWord_7501621).sum := by decide
  have hdescent : baseEnd_7501621 < baseStart_7501621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501624 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_7501624 : Nat := 118140960795 + 7501624 * 2 ^ 59
def prefixEnd_7501624 : Nat := 4983230072969 + 3 ^ 40 * 7501624 * 2
def baseEnd_7501624 : Nat := 3851938801303663095300665

theorem tailTrace_7501624 : CollatzResearch.WordTrace tailWord_7501624 prefixEnd_7501624 3851938801303663095300665 := by
  unfold tailWord_7501624
  simp only [CollatzResearch.WordTrace]
  refine ⟨136803352487452449112363963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182404469983269932149818617 136803352487452449112363963)
  ·
    refine ⟨205205028731178673668545945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136803352487452449112363963 205205028731178673668545945)
    ·
      refine ⟨153903771548384005251409459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205205028731178673668545945 153903771548384005251409459)
      ·
        refine ⟨230855657322576007877114189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153903771548384005251409459 230855657322576007877114189)
        ·
          refine ⟨86570871495966002953917821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230855657322576007877114189 86570871495966002953917821)
          ·
            refine ⟨32464076810987251107719183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86570871495966002953917821 32464076810987251107719183)
            ·
              refine ⟨48696115216480876661578775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32464076810987251107719183 48696115216480876661578775)
              ·
                refine ⟨73044172824721314992368163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48696115216480876661578775 73044172824721314992368163)
                ·
                  refine ⟨109566259237081972488552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73044172824721314992368163 109566259237081972488552245)
                  ·
                    refine ⟨10271836803476434920801773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109566259237081972488552245 10271836803476434920801773)
                    ·
                      refine ⟨3851938801303663095300665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271836803476434920801773 3851938801303663095300665)
                      ·
                        rfl

theorem cell23_7501624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_7501624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501624 prefixEnd_7501624 := by exact prefixLift 7501624
  have htrace : WordTrace (prefixWord ++ tailWord_7501624) baseStart_7501624 baseEnd_7501624 := by
    simpa [prefixWord, tailWord_7501624, baseEnd_7501624] using wordTrace_append hprefix tailTrace_7501624
  have hstable : (prefixWord ++ tailWord_7501624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501624).length < 2 ^ (prefixWord ++ tailWord_7501624).sum := by decide
  have hdescent : baseEnd_7501624 < baseStart_7501624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501625 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7501625 : Nat := 118140960795 + 7501625 * 2 ^ 59
def prefixEnd_7501625 : Nat := 4983230072969 + 3 ^ 40 * 7501625 * 2
def baseEnd_7501625 : Nat := 3851939314784317591388161

theorem tailTrace_7501625 : CollatzResearch.WordTrace tailWord_7501625 prefixEnd_7501625 3851939314784317591388161 := by
  unfold tailWord_7501625
  simp only [CollatzResearch.WordTrace]
  refine ⟨273606741447901275395514329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182404494298600850263676219 273606741447901275395514329)
  ·
    refine ⟨205205056085925956546635747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273606741447901275395514329 205205056085925956546635747)
    ·
      refine ⟨307807584128888934819953621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205205056085925956546635747 307807584128888934819953621)
      ·
        refine ⟨7214240253020834409842663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 307807584128888934819953621 7214240253020834409842663)
        ·
          refine ⟨10821360379531251614763995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214240253020834409842663 10821360379531251614763995)
          ·
            refine ⟨16232040569296877422145993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821360379531251614763995 16232040569296877422145993)
            ·
              refine ⟨12174030426972658066609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16232040569296877422145993 12174030426972658066609495)
              ·
                refine ⟨18261045640458987099914243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174030426972658066609495 18261045640458987099914243)
                ·
                  refine ⟨27391568460688480649871365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18261045640458987099914243 27391568460688480649871365)
                  ·
                    refine ⟨5135919086379090121850881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27391568460688480649871365 5135919086379090121850881)
                    ·
                      refine ⟨3851939314784317591388161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135919086379090121850881 3851939314784317591388161)
                      ·
                        rfl

theorem cell23_7501625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7501625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501625 prefixEnd_7501625 := by exact prefixLift 7501625
  have htrace : WordTrace (prefixWord ++ tailWord_7501625) baseStart_7501625 baseEnd_7501625 := by
    simpa [prefixWord, tailWord_7501625, baseEnd_7501625] using wordTrace_append hprefix tailTrace_7501625
  have hstable : (prefixWord ++ tailWord_7501625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501625).length < 2 ^ (prefixWord ++ tailWord_7501625).sum := by decide
  have hdescent : baseEnd_7501625 < baseStart_7501625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501681 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_7501681 : Nat := 118140960795 + 7501681 * 2 ^ 59
def prefixEnd_7501681 : Nat := 4983230072969 + 3 ^ 40 * 7501681 * 2
def baseEnd_7501681 : Nat := 3851968069700969372287903

theorem tailTrace_7501681 : CollatzResearch.WordTrace tailWord_7501681 prefixEnd_7501681 3851968069700969372287903 := by
  unfold tailWord_7501681
  simp only [CollatzResearch.WordTrace]
  refine ⟨273608783935698396959552897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182405855957132264639701931 273608783935698396959552897)
  ·
    refine ⟨205206587951773797719664673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273608783935698396959552897 205206587951773797719664673)
    ·
      refine ⟨153904940963830348289748505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205206587951773797719664673 153904940963830348289748505)
      ·
        refine ⟨115428705722872761217311379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153904940963830348289748505 115428705722872761217311379)
        ·
          refine ⟨173143058584309141825967069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115428705722872761217311379 173143058584309141825967069)
          ·
            refine ⟨64928646969115928184737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173143058584309141825967069 64928646969115928184737651)
            ·
              refine ⟨97392970453673892277106477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64928646969115928184737651 97392970453673892277106477)
              ·
                refine ⟨36522363920127709603914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97392970453673892277106477 36522363920127709603914929)
                ·
                  refine ⟨27391772940095782202936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36522363920127709603914929 27391772940095782202936197)
                  ·
                    refine ⟨5135957426267959163050537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27391772940095782202936197 5135957426267959163050537)
                    ·
                      refine ⟨3851968069700969372287903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5135957426267959163050537 3851968069700969372287903)
                      ·
                        rfl

theorem cell23_7501681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_7501681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501681 prefixEnd_7501681 := by exact prefixLift 7501681
  have htrace : WordTrace (prefixWord ++ tailWord_7501681) baseStart_7501681 baseEnd_7501681 := by
    simpa [prefixWord, tailWord_7501681, baseEnd_7501681] using wordTrace_append hprefix tailTrace_7501681
  have hstable : (prefixWord ++ tailWord_7501681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501681).length < 2 ^ (prefixWord ++ tailWord_7501681).sum := by decide
  have hdescent : baseEnd_7501681 < baseStart_7501681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501701 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_7501701 : Nat := 118140960795 + 7501701 * 2 ^ 59
def prefixEnd_7501701 : Nat := 4983230072969 + 3 ^ 40 * 7501701 * 2
def baseEnd_7501701 : Nat := 3851978339314059294037811

theorem tailTrace_7501701 : CollatzResearch.WordTrace tailWord_7501701 prefixEnd_7501701 3851978339314059294037811 := by
  unfold tailWord_7501701
  simp only [CollatzResearch.WordTrace]
  refine ⟨273609513395625940375280957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182406342263750626916853971 273609513395625940375280957)
  ·
    refine ⟨102603567523359727640730359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273609513395625940375280957 102603567523359727640730359)
    ·
      refine ⟨153905351285039591461095539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102603567523359727640730359 153905351285039591461095539)
      ·
        refine ⟨230858026927559387191643309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153905351285039591461095539 230858026927559387191643309)
        ·
          refine ⟨86571760097834770196866241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230858026927559387191643309 86571760097834770196866241)
          ·
            refine ⟨64928820073376077647649681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86571760097834770196866241 64928820073376077647649681)
            ·
              refine ⟨48696615055032058235737261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64928820073376077647649681 48696615055032058235737261)
              ·
                refine ⟨18261230645637021838401473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48696615055032058235737261 18261230645637021838401473)
                ·
                  refine ⟨13695922984227766378801105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18261230645637021838401473 13695922984227766378801105)
                  ·
                    refine ⟨10271942238170824784100829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13695922984227766378801105 10271942238170824784100829)
                    ·
                      refine ⟨3851978339314059294037811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10271942238170824784100829 3851978339314059294037811)
                      ·
                        rfl

theorem cell23_7501701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_7501701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501701 prefixEnd_7501701 := by exact prefixLift 7501701
  have htrace : WordTrace (prefixWord ++ tailWord_7501701) baseStart_7501701 baseEnd_7501701 := by
    simpa [prefixWord, tailWord_7501701, baseEnd_7501701] using wordTrace_append hprefix tailTrace_7501701
  have hstable : (prefixWord ++ tailWord_7501701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501701).length < 2 ^ (prefixWord ++ tailWord_7501701).sum := by decide
  have hdescent : baseEnd_7501701 < baseStart_7501701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501804 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_7501804 : Nat := 118140960795 + 7501804 * 2 ^ 59
def prefixEnd_7501804 : Nat := 4983230072969 + 3 ^ 40 * 7501804 * 2
def baseEnd_7501804 : Nat := 3852031227821472391049837

theorem tailTrace_7501804 : CollatzResearch.WordTrace tailWord_7501804 prefixEnd_7501804 3852031227821472391049837 := by
  unfold tailWord_7501804
  simp only [CollatzResearch.WordTrace]
  refine ⟨136806635057126394483140233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182408846742835192644186977 136806635057126394483140233)
  ·
    refine ⟨102604976292844795862355175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136806635057126394483140233 102604976292844795862355175)
    ·
      refine ⟨153907464439267193793532763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102604976292844795862355175 153907464439267193793532763)
      ·
        refine ⟨230861196658900790690299145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153907464439267193793532763 230861196658900790690299145)
        ·
          refine ⟨173145897494175593017724359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230861196658900790690299145 173145897494175593017724359)
          ·
            refine ⟨259718846241263389526586539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173145897494175593017724359 259718846241263389526586539)
            ·
              refine ⟨389578269361895084289879809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259718846241263389526586539 389578269361895084289879809)
              ·
                refine ⟨292183702021421313217409857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389578269361895084289879809 292183702021421313217409857)
                ·
                  refine ⟨219137776516065984913057393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292183702021421313217409857 219137776516065984913057393)
                  ·
                    refine ⟨164353332387049488684793045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219137776516065984913057393 164353332387049488684793045)
                    ·
                      refine ⟨3852031227821472391049837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164353332387049488684793045 3852031227821472391049837)
                      ·
                        rfl

theorem cell23_7501804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7501804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501804 prefixEnd_7501804 := by exact prefixLift 7501804
  have htrace : WordTrace (prefixWord ++ tailWord_7501804) baseStart_7501804 baseEnd_7501804 := by
    simpa [prefixWord, tailWord_7501804, baseEnd_7501804] using wordTrace_append hprefix tailTrace_7501804
  have hstable : (prefixWord ++ tailWord_7501804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501804).length < 2 ^ (prefixWord ++ tailWord_7501804).sum := by decide
  have hdescent : baseEnd_7501804 < baseStart_7501804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501822 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7501822 : Nat := 118140960795 + 7501822 * 2 ^ 59
def prefixEnd_7501822 : Nat := 4983230072969 + 3 ^ 40 * 7501822 * 2
def baseEnd_7501822 : Nat := 3852040470473253320624755

theorem tailTrace_7501822 : CollatzResearch.WordTrace tailWord_7501822 prefixEnd_7501822 3852040470473253320624755 := by
  unfold tailWord_7501822
  simp only [CollatzResearch.WordTrace]
  refine ⟨34201740828523447255054465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182409284418791718693623813 34201740828523447255054465)
  ·
    refine ⟨25651305621392585441290849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34201740828523447255054465 25651305621392585441290849)
    ·
      refine ⟨19238479216044439080968137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25651305621392585441290849 19238479216044439080968137)
      ·
        refine ⟨14428859412033329310726103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19238479216044439080968137 14428859412033329310726103)
        ·
          refine ⟨21643289118049993966089155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428859412033329310726103 21643289118049993966089155)
          ·
            refine ⟨32464933677074990949133733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21643289118049993966089155 32464933677074990949133733)
            ·
              refine ⟨6087175064451560802962575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32464933677074990949133733 6087175064451560802962575)
              ·
                refine ⟨9130762596677341204443863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087175064451560802962575 9130762596677341204443863)
                ·
                  refine ⟨13696143895016011806665795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9130762596677341204443863 13696143895016011806665795)
                  ·
                    refine ⟨20544215842524017709998693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13696143895016011806665795 20544215842524017709998693)
                    ·
                      refine ⟨3852040470473253320624755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20544215842524017709998693 3852040470473253320624755)
                      ·
                        rfl

theorem cell23_7501822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7501822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501822 prefixEnd_7501822 := by exact prefixLift 7501822
  have htrace : WordTrace (prefixWord ++ tailWord_7501822) baseStart_7501822 baseEnd_7501822 := by
    simpa [prefixWord, tailWord_7501822, baseEnd_7501822] using wordTrace_append hprefix tailTrace_7501822
  have hstable : (prefixWord ++ tailWord_7501822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501822).length < 2 ^ (prefixWord ++ tailWord_7501822).sum := by decide
  have hdescent : baseEnd_7501822 < baseStart_7501822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501824 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_7501824 : Nat := 118140960795 + 7501824 * 2 ^ 59
def prefixEnd_7501824 : Nat := 4983230072969 + 3 ^ 40 * 7501824 * 2
def baseEnd_7501824 : Nat := 1284013832478187437599915

theorem tailTrace_7501824 : CollatzResearch.WordTrace tailWord_7501824 prefixEnd_7501824 1284013832478187437599915 := by
  unfold tailWord_7501824
  simp only [CollatzResearch.WordTrace]
  refine ⟨136806999787090166191004263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182409333049453554921339017 136806999787090166191004263)
  ·
    refine ⟨205210499680635249286506395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136806999787090166191004263 205210499680635249286506395)
    ·
      refine ⟨307815749520952873929759593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205210499680635249286506395 307815749520952873929759593)
      ·
        refine ⟨230861812140714655447319695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307815749520952873929759593 230861812140714655447319695)
        ·
          refine ⟨346292718211071983170979543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230861812140714655447319695 346292718211071983170979543)
          ·
            refine ⟨519439077316607974756469315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346292718211071983170979543 519439077316607974756469315)
            ·
              refine ⟨779158615974911962134703973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519439077316607974756469315 779158615974911962134703973)
              ·
                refine ⟨146092240495295992900256995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 779158615974911962134703973 146092240495295992900256995)
                ·
                  refine ⟨219138360742943989350385493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146092240495295992900256995 219138360742943989350385493)
                  ·
                    refine ⟨1284013832478187437599915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219138360742943989350385493 1284013832478187437599915)
                    ·
                      rfl

theorem cell23_7501824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_7501824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501824 prefixEnd_7501824 := by exact prefixLift 7501824
  have htrace : WordTrace (prefixWord ++ tailWord_7501824) baseStart_7501824 baseEnd_7501824 := by
    simpa [prefixWord, tailWord_7501824, baseEnd_7501824] using wordTrace_append hprefix tailTrace_7501824
  have hstable : (prefixWord ++ tailWord_7501824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501824).length < 2 ^ (prefixWord ++ tailWord_7501824).sum := by decide
  have hdescent : baseEnd_7501824 < baseStart_7501824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501828 : List Nat := [2, 3, 2, 4, 1, 1, 10]
def baseStart_7501828 : Nat := 118140960795 + 7501828 * 2 ^ 59
def prefixEnd_7501828 : Nat := 4983230072969 + 3 ^ 40 * 7501828 * 2
def baseEnd_7501828 : Nat := 47556093226631855520367

theorem tailTrace_7501828 : CollatzResearch.WordTrace tailWord_7501828 prefixEnd_7501828 47556093226631855520367 := by
  unfold tailWord_7501828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136807072733082920532577069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182409430310777227376769425 136807072733082920532577069)
  ·
    refine ⟨51302652274906095199716401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136807072733082920532577069 51302652274906095199716401)
    ·
      refine ⟨38476989206179571399787301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51302652274906095199716401 38476989206179571399787301)
      ·
        refine ⟨7214435476158669637460119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38476989206179571399787301 7214435476158669637460119)
        ·
          refine ⟨10821653214238004456190179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214435476158669637460119 10821653214238004456190179)
          ·
            refine ⟨16232479821357006684285269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821653214238004456190179 16232479821357006684285269)
            ·
              refine ⟨47556093226631855520367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16232479821357006684285269 47556093226631855520367)
              ·
                rfl

theorem cell23_7501828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 10].length) (baseStart_7501828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501828 prefixEnd_7501828 := by exact prefixLift 7501828
  have htrace : WordTrace (prefixWord ++ tailWord_7501828) baseStart_7501828 baseEnd_7501828 := by
    simpa [prefixWord, tailWord_7501828, baseEnd_7501828] using wordTrace_append hprefix tailTrace_7501828
  have hstable : (prefixWord ++ tailWord_7501828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501828).length < 2 ^ (prefixWord ++ tailWord_7501828).sum := by decide
  have hdescent : baseEnd_7501828 < baseStart_7501828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501891 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_7501891 : Nat := 118140960795 + 7501891 * 2 ^ 59
def prefixEnd_7501891 : Nat := 4983230072969 + 3 ^ 40 * 7501891 * 2
def baseEnd_7501891 : Nat := 3852075900638413550661937

theorem tailTrace_7501891 : CollatzResearch.WordTrace tailWord_7501891 prefixEnd_7501891 3852075900638413550661937 := by
  unfold tailWord_7501891
  simp only [CollatzResearch.WordTrace]
  refine ⟨273616443264937602824697527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182410962176625068549798351 273616443264937602824697527)
  ·
    refine ⟨410424664897406404237046291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273616443264937602824697527 410424664897406404237046291)
    ·
      refine ⟨615636997346109606355569437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410424664897406404237046291 615636997346109606355569437)
      ·
        refine ⟨230863874004791102383338539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615636997346109606355569437 230863874004791102383338539)
        ·
          refine ⟨346295811007186653575007809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230863874004791102383338539 346295811007186653575007809)
          ·
            refine ⟨259721858255389990181255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346295811007186653575007809 259721858255389990181255857)
            ·
              refine ⟨194791393691542492635941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259721858255389990181255857 194791393691542492635941893)
              ·
                refine ⟨36523386317164217369239105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194791393691542492635941893 36523386317164217369239105)
                ·
                  refine ⟨27392539737873163026929329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36523386317164217369239105 27392539737873163026929329)
                  ·
                    refine ⟨20544404803404872270196997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27392539737873163026929329 20544404803404872270196997)
                    ·
                      refine ⟨3852075900638413550661937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20544404803404872270196997 3852075900638413550661937)
                      ·
                        rfl

theorem cell23_7501891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_7501891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501891 prefixEnd_7501891 := by exact prefixLift 7501891
  have htrace : WordTrace (prefixWord ++ tailWord_7501891) baseStart_7501891 baseEnd_7501891 := by
    simpa [prefixWord, tailWord_7501891, baseEnd_7501891] using wordTrace_append hprefix tailTrace_7501891
  have hstable : (prefixWord ++ tailWord_7501891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501891).length < 2 ^ (prefixWord ++ tailWord_7501891).sum := by decide
  have hdescent : baseEnd_7501891 < baseStart_7501891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501895 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_7501895 : Nat := 118140960795 + 7501895 * 2 ^ 59
def prefixEnd_7501895 : Nat := 4983230072969 + 3 ^ 40 * 7501895 * 2
def baseEnd_7501895 : Nat := 3852077954561031535011919

theorem tailTrace_7501895 : CollatzResearch.WordTrace tailWord_7501895 prefixEnd_7501895 3852077954561031535011919 := by
  unfold tailWord_7501895
  simp only [CollatzResearch.WordTrace]
  refine ⟨273616589156923111507843139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182411059437948741005228759 273616589156923111507843139)
  ·
    refine ⟨410424883735384667261764709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273616589156923111507843139 410424883735384667261764709)
    ·
      refine ⟨76954665700384625111580883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410424883735384667261764709 76954665700384625111580883)
      ·
        refine ⟨115431998550576937667371325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76954665700384625111580883 115431998550576937667371325)
        ·
          refine ⟨43286999456466351625264247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115431998550576937667371325 43286999456466351625264247)
          ·
            refine ⟨64930499184699527437896371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43286999456466351625264247 64930499184699527437896371)
            ·
              refine ⟨97395748777049291156844557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64930499184699527437896371 97395748777049291156844557)
              ·
                refine ⟨36523405791393484183816709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97395748777049291156844557 36523405791393484183816709)
                ·
                  refine ⟨6848138585886278284465633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36523405791393484183816709 6848138585886278284465633)
                  ·
                    refine ⟨5136103939414708713349225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6848138585886278284465633 5136103939414708713349225)
                    ·
                      refine ⟨3852077954561031535011919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136103939414708713349225 3852077954561031535011919)
                      ·
                        rfl

theorem cell23_7501895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_7501895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501895 prefixEnd_7501895 := by exact prefixLift 7501895
  have htrace : WordTrace (prefixWord ++ tailWord_7501895) baseStart_7501895 baseEnd_7501895 := by
    simpa [prefixWord, tailWord_7501895, baseEnd_7501895] using wordTrace_append hprefix tailTrace_7501895
  have hstable : (prefixWord ++ tailWord_7501895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501895).length < 2 ^ (prefixWord ++ tailWord_7501895).sum := by decide
  have hdescent : baseEnd_7501895 < baseStart_7501895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501906 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_7501906 : Nat := 118140960795 + 7501906 * 2 ^ 59
def prefixEnd_7501906 : Nat := 4983230072969 + 3 ^ 40 * 7501906 * 2
def baseEnd_7501906 : Nat := 3852083602848230991974369

theorem tailTrace_7501906 : CollatzResearch.WordTrace tailWord_7501906 prefixEnd_7501906 3852083602848230991974369 := by
  unfold tailWord_7501906
  simp only [CollatzResearch.WordTrace]
  refine ⟨68404247589970815096623393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182411326906588840257662381 68404247589970815096623393)
  ·
    refine ⟨51303185692478111322467545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68404247589970815096623393 51303185692478111322467545)
    ·
      refine ⟨38477389269358583491850659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51303185692478111322467545 38477389269358583491850659)
      ·
        refine ⟨57716083904037875237775989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38477389269358583491850659 57716083904037875237775989)
        ·
          refine ⟨5410882866003550803541499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57716083904037875237775989 5410882866003550803541499)
          ·
            refine ⟨8116324299005326205312249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5410882866003550803541499 8116324299005326205312249)
            ·
              refine ⟨6087243224253994653984187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116324299005326205312249 6087243224253994653984187)
              ·
                refine ⟨9130864836380991980976281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087243224253994653984187 9130864836380991980976281)
                ·
                  refine ⟨6848148627285743985732211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130864836380991980976281 6848148627285743985732211)
                  ·
                    refine ⟨10272222940928615978598317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848148627285743985732211 10272222940928615978598317)
                    ·
                      refine ⟨3852083602848230991974369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272222940928615978598317 3852083602848230991974369)
                      ·
                        rfl

theorem cell23_7501906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_7501906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501906 prefixEnd_7501906 := by exact prefixLift 7501906
  have htrace : WordTrace (prefixWord ++ tailWord_7501906) baseStart_7501906 baseEnd_7501906 := by
    simpa [prefixWord, tailWord_7501906, baseEnd_7501906] using wordTrace_append hprefix tailTrace_7501906
  have hstable : (prefixWord ++ tailWord_7501906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501906).length < 2 ^ (prefixWord ++ tailWord_7501906).sum := by decide
  have hdescent : baseEnd_7501906 < baseStart_7501906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501912 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_7501912 : Nat := 118140960795 + 7501912 * 2 ^ 59
def prefixEnd_7501912 : Nat := 4983230072969 + 3 ^ 40 * 7501912 * 2
def baseEnd_7501912 : Nat := 3852086683732157968499341

theorem tailTrace_7501912 : CollatzResearch.WordTrace tailWord_7501912 prefixEnd_7501912 3852086683732157968499341 := by
  unfold tailWord_7501912
  simp only [CollatzResearch.WordTrace]
  refine ⟨136808604598930761705605995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182411472798574348940807993 136808604598930761705605995)
  ·
    refine ⟨205212906898396142558408993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136808604598930761705605995 205212906898396142558408993)
    ·
      refine ⟨153909680173797106918806745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205212906898396142558408993 153909680173797106918806745)
      ·
        refine ⟨115432260130347830189105059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153909680173797106918806745 115432260130347830189105059)
        ·
          refine ⟨173148390195521745283657589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115432260130347830189105059 173148390195521745283657589)
          ·
            refine ⟨16232661580830163620342899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173148390195521745283657589 16232661580830163620342899)
            ·
              refine ⟨24348992371245245430514349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16232661580830163620342899 24348992371245245430514349)
              ·
                refine ⟨9130872139216967036442881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24348992371245245430514349 9130872139216967036442881)
                ·
                  refine ⟨6848154104412725277332161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9130872139216967036442881 6848154104412725277332161)
                  ·
                    refine ⟨5136115578309543957999121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6848154104412725277332161 5136115578309543957999121)
                    ·
                      refine ⟨3852086683732157968499341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136115578309543957999121 3852086683732157968499341)
                      ·
                        rfl

theorem cell23_7501912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_7501912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501912 prefixEnd_7501912 := by exact prefixLift 7501912
  have htrace : WordTrace (prefixWord ++ tailWord_7501912) baseStart_7501912 baseEnd_7501912 := by
    simpa [prefixWord, tailWord_7501912, baseEnd_7501912] using wordTrace_append hprefix tailTrace_7501912
  have hstable : (prefixWord ++ tailWord_7501912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501912).length < 2 ^ (prefixWord ++ tailWord_7501912).sum := by decide
  have hdescent : baseEnd_7501912 < baseStart_7501912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501948 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_7501948 : Nat := 118140960795 + 7501948 * 2 ^ 59
def prefixEnd_7501948 : Nat := 4983230072969 + 3 ^ 40 * 7501948 * 2
def baseEnd_7501948 : Nat := 1284035056345239942549725

theorem tailTrace_7501948 : CollatzResearch.WordTrace tailWord_7501948 prefixEnd_7501948 1284035056345239942549725 := by
  unfold tailWord_7501948
  simp only [CollatzResearch.WordTrace]
  refine ⟨136809261112865550779761249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182412348150487401039681665 136809261112865550779761249)
  ·
    refine ⟨102606945834649163084820937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136809261112865550779761249 102606945834649163084820937)
    ·
      refine ⟨76955209375986872313615703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102606945834649163084820937 76955209375986872313615703)
      ·
        refine ⟨115432814063980308470423555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76955209375986872313615703 115432814063980308470423555)
        ·
          refine ⟨173149221095970462705635333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115432814063980308470423555 173149221095970462705635333)
          ·
            refine ⟨32465478955494461757306625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173149221095970462705635333 32465478955494461757306625)
            ·
              refine ⟨24349109216620846317979969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32465478955494461757306625 24349109216620846317979969)
              ·
                refine ⟨18261831912465634738484977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24349109216620846317979969 18261831912465634738484977)
                ·
                  refine ⟨13696373934349226053863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18261831912465634738484977 13696373934349226053863733)
                  ·
                    refine ⟨1284035056345239942549725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13696373934349226053863733 1284035056345239942549725)
                    ·
                      rfl

theorem cell23_7501948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_7501948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501948 prefixEnd_7501948 := by exact prefixLift 7501948
  have htrace : WordTrace (prefixWord ++ tailWord_7501948) baseStart_7501948 baseEnd_7501948 := by
    simpa [prefixWord, tailWord_7501948, baseEnd_7501948] using wordTrace_append hprefix tailTrace_7501948
  have hstable : (prefixWord ++ tailWord_7501948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501948).length < 2 ^ (prefixWord ++ tailWord_7501948).sum := by decide
  have hdescent : baseEnd_7501948 < baseStart_7501948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7501985 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7501985 : Nat := 118140960795 + 7501985 * 2 ^ 59
def prefixEnd_7501985 : Nat := 4983230072969 + 3 ^ 40 * 7501985 * 2
def baseEnd_7501985 : Nat := 3852124167819936182886505

theorem tailTrace_7501985 : CollatzResearch.WordTrace tailWord_7501985 prefixEnd_7501985 3852124167819936182886505 := by
  unfold tailWord_7501985
  simp only [CollatzResearch.WordTrace]
  refine ⟨273619871726597056878619409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182413247817731371252412939 273619871726597056878619409)
  ·
    refine ⟨205214903794947792658964557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273619871726597056878619409 205214903794947792658964557)
    ·
      refine ⟨76955588923105422247111709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205214903794947792658964557 76955588923105422247111709)
      ·
        refine ⟨28858345846164533342666891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76955588923105422247111709 28858345846164533342666891)
        ·
          refine ⟨43287518769246800014000337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28858345846164533342666891 43287518769246800014000337)
          ·
            refine ⟨32465639076935100010500253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43287518769246800014000337 32465639076935100010500253)
            ·
              refine ⟨12174614653850662503937595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32465639076935100010500253 12174614653850662503937595)
              ·
                refine ⟨18261921980775993755906393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174614653850662503937595 18261921980775993755906393)
                ·
                  refine ⟨13696441485581995316929795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18261921980775993755906393 13696441485581995316929795)
                  ·
                    refine ⟨20544662228372992975394693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13696441485581995316929795 20544662228372992975394693)
                    ·
                      refine ⟨3852124167819936182886505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20544662228372992975394693 3852124167819936182886505)
                      ·
                        rfl

theorem cell23_7501985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7501985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7501985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7501985 prefixEnd_7501985 := by exact prefixLift 7501985
  have htrace : WordTrace (prefixWord ++ tailWord_7501985) baseStart_7501985 baseEnd_7501985 := by
    simpa [prefixWord, tailWord_7501985, baseEnd_7501985] using wordTrace_append hprefix tailTrace_7501985
  have hstable : (prefixWord ++ tailWord_7501985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7501985).length < 2 ^ (prefixWord ++ tailWord_7501985).sum := by decide
  have hdescent : baseEnd_7501985 < baseStart_7501985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7501985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502011 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_7502011 : Nat := 118140960795 + 7502011 * 2 ^ 59
def prefixEnd_7502011 : Nat := 4983230072969 + 3 ^ 40 * 7502011 * 2
def baseEnd_7502011 : Nat := 3852137518316953081161385

theorem tailTrace_7502011 : CollatzResearch.WordTrace tailWord_7502011 prefixEnd_7502011 3852137518316953081161385 := by
  unfold tailWord_7502011
  simp only [CollatzResearch.WordTrace]
  refine ⟨273620820024502863319065887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182413880016335242212710591 273620820024502863319065887)
  ·
    refine ⟨410431230036754294978598831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273620820024502863319065887 410431230036754294978598831)
    ·
      refine ⟨615646845055131442467898247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410431230036754294978598831 615646845055131442467898247)
      ·
        refine ⟨923470267582697163701847371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615646845055131442467898247 923470267582697163701847371)
        ·
          refine ⟨1385205401374045745552771057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923470267582697163701847371 1385205401374045745552771057)
          ·
            refine ⟨1038904051030534309164578293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385205401374045745552771057 1038904051030534309164578293)
            ·
              refine ⟨97397254784112591484179215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1038904051030534309164578293 97397254784112591484179215)
              ·
                refine ⟨146095882176168887226268823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97397254784112591484179215 146095882176168887226268823)
                ·
                  refine ⟨219143823264253330839403235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146095882176168887226268823 219143823264253330839403235)
                  ·
                    refine ⟨328715734896379996259104853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219143823264253330839403235 328715734896379996259104853)
                    ·
                      refine ⟨3852137518316953081161385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328715734896379996259104853 3852137518316953081161385)
                      ·
                        rfl

theorem cell23_7502011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_7502011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502011 prefixEnd_7502011 := by exact prefixLift 7502011
  have htrace : WordTrace (prefixWord ++ tailWord_7502011) baseStart_7502011 baseEnd_7502011 := by
    simpa [prefixWord, tailWord_7502011, baseEnd_7502011] using wordTrace_append hprefix tailTrace_7502011
  have hstable : (prefixWord ++ tailWord_7502011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502011).length < 2 ^ (prefixWord ++ tailWord_7502011).sum := by decide
  have hdescent : baseEnd_7502011 < baseStart_7502011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502012 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_7502012 : Nat := 118140960795 + 7502012 * 2 ^ 59
def prefixEnd_7502012 : Nat := 4983230072969 + 3 ^ 40 * 7502012 * 2
def baseEnd_7502012 : Nat := 1284046010599202525749627

theorem tailTrace_7502012 : CollatzResearch.WordTrace tailWord_7502012 prefixEnd_7502012 1284046010599202525749627 := by
  unfold tailWord_7502012
  simp only [CollatzResearch.WordTrace]
  refine ⟨136810428248749620244926145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182413904331666160326568193 136810428248749620244926145)
  ·
    refine ⟨102607821186562215183694609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136810428248749620244926145 102607821186562215183694609)
    ·
      refine ⟨76955865889921661387770957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102607821186562215183694609 76955865889921661387770957)
      ·
        refine ⟨28858449708720623020414109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76955865889921661387770957 28858449708720623020414109)
        ·
          refine ⟨10821918640770233632655291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28858449708720623020414109 10821918640770233632655291)
          ·
            refine ⟨16232877961155350448982937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821918640770233632655291 16232877961155350448982937)
            ·
              refine ⟨12174658470866512836737203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16232877961155350448982937 12174658470866512836737203)
              ·
                refine ⟨18261987706299769255105805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174658470866512836737203 18261987706299769255105805)
                ·
                  refine ⟨6848245389862413470664677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18261987706299769255105805 6848245389862413470664677)
                  ·
                    refine ⟨1284046010599202525749627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6848245389862413470664677 1284046010599202525749627)
                    ·
                      rfl

theorem cell23_7502012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_7502012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502012 prefixEnd_7502012 := by exact prefixLift 7502012
  have htrace : WordTrace (prefixWord ++ tailWord_7502012) baseStart_7502012 baseEnd_7502012 := by
    simpa [prefixWord, tailWord_7502012, baseEnd_7502012] using wordTrace_append hprefix tailTrace_7502012
  have hstable : (prefixWord ++ tailWord_7502012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502012).length < 2 ^ (prefixWord ++ tailWord_7502012).sum := by decide
  have hdescent : baseEnd_7502012 < baseStart_7502012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502092 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_7502092 : Nat := 118140960795 + 7502092 * 2 ^ 59
def prefixEnd_7502092 : Nat := 4983230072969 + 3 ^ 40 * 7502092 * 2
def baseEnd_7502092 : Nat := 3852179110249967264248513

theorem tailTrace_7502092 : CollatzResearch.WordTrace tailWord_7502092 prefixEnd_7502092 3852179110249967264248513 := by
  unfold tailWord_7502092
  simp only [CollatzResearch.WordTrace]
  refine ⟨136811887168604707076382265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182415849558139609435176353 136811887168604707076382265)
  ·
    refine ⟨102608915376453530307286699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136811887168604707076382265 102608915376453530307286699)
    ·
      refine ⟨153913373064680295460930049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102608915376453530307286699 153913373064680295460930049)
      ·
        refine ⟨115435029798510221595697537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153913373064680295460930049 115435029798510221595697537)
        ·
          refine ⟨86576272348882666196773153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115435029798510221595697537 86576272348882666196773153)
          ·
            refine ⟨64932204261661999647579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86576272348882666196773153 64932204261661999647579865)
            ·
              refine ⟨48699153196246499735684899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64932204261661999647579865 48699153196246499735684899)
              ·
                refine ⟨73048729794369749603527349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48699153196246499735684899 73048729794369749603527349)
                ·
                  refine ⟨6848318418222164025330689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73048729794369749603527349 6848318418222164025330689)
                  ·
                    refine ⟨5136238813666623018998017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6848318418222164025330689 5136238813666623018998017)
                    ·
                      refine ⟨3852179110249967264248513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136238813666623018998017 3852179110249967264248513)
                      ·
                        rfl

theorem cell23_7502092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_7502092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502092 prefixEnd_7502092 := by exact prefixLift 7502092
  have htrace : WordTrace (prefixWord ++ tailWord_7502092) baseStart_7502092 baseEnd_7502092 := by
    simpa [prefixWord, tailWord_7502092, baseEnd_7502092] using wordTrace_append hprefix tailTrace_7502092
  have hstable : (prefixWord ++ tailWord_7502092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502092).length < 2 ^ (prefixWord ++ tailWord_7502092).sum := by decide
  have hdescent : baseEnd_7502092 < baseStart_7502092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502112 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7502112 : Nat := 118140960795 + 7502112 * 2 ^ 59
def prefixEnd_7502112 : Nat := 4983230072969 + 3 ^ 40 * 7502112 * 2
def baseEnd_7502112 : Nat := 3852189379863057185998421

theorem tailTrace_7502112 : CollatzResearch.WordTrace tailWord_7502112 prefixEnd_7502112 3852189379863057185998421 := by
  unfold tailWord_7502112
  simp only [CollatzResearch.WordTrace]
  refine ⟨136812251898568478784246295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182416335864757971712328393 136812251898568478784246295)
  ·
    refine ⟨205218377847852718176369443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136812251898568478784246295 205218377847852718176369443)
    ·
      refine ⟨307827566771779077264554165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205218377847852718176369443 307827566771779077264554165)
      ·
        refine ⟨28858834384854288493551953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307827566771779077264554165 28858834384854288493551953)
        ·
          refine ⟨21644125788640716370163965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28858834384854288493551953 21644125788640716370163965)
          ·
            refine ⟨8116547170740268638811487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21644125788640716370163965 8116547170740268638811487)
            ·
              refine ⟨12174820756110402958217231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116547170740268638811487 12174820756110402958217231)
              ·
                refine ⟨18262231134165604437325847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12174820756110402958217231 18262231134165604437325847)
                ·
                  refine ⟨27393346701248406655988771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18262231134165604437325847 27393346701248406655988771)
                  ·
                    refine ⟨41090020051872609983983157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27393346701248406655988771 41090020051872609983983157)
                    ·
                      refine ⟨3852189379863057185998421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41090020051872609983983157 3852189379863057185998421)
                      ·
                        rfl

theorem cell23_7502112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7502112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502112 prefixEnd_7502112 := by exact prefixLift 7502112
  have htrace : WordTrace (prefixWord ++ tailWord_7502112) baseStart_7502112 baseEnd_7502112 := by
    simpa [prefixWord, tailWord_7502112, baseEnd_7502112] using wordTrace_append hprefix tailTrace_7502112
  have hstable : (prefixWord ++ tailWord_7502112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502112).length < 2 ^ (prefixWord ++ tailWord_7502112).sum := by decide
  have hdescent : baseEnd_7502112 < baseStart_7502112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502120 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7502120 : Nat := 118140960795 + 7502120 * 2 ^ 59
def prefixEnd_7502120 : Nat := 4983230072969 + 3 ^ 40 * 7502120 * 2
def baseEnd_7502120 : Nat := 3852193487708293154698385

theorem tailTrace_7502120 : CollatzResearch.WordTrace tailWord_7502120 prefixEnd_7502120 3852193487708293154698385 := by
  unfold tailWord_7502120
  simp only [CollatzResearch.WordTrace]
  refine ⟨136812397790553987467391907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182416530387405316623189209 136812397790553987467391907)
  ·
    refine ⟨205218596685830981201087861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136812397790553987467391907 205218596685830981201087861)
    ·
      refine ⟨19239243439296654487601987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205218596685830981201087861 19239243439296654487601987)
      ·
        refine ⟨28858865158944981731402981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239243439296654487601987 28858865158944981731402981)
        ·
          refine ⟨5411037217302184074638059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28858865158944981731402981 5411037217302184074638059)
          ·
            refine ⟨8116555825953276111957089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411037217302184074638059 8116555825953276111957089)
            ·
              refine ⟨6087416869464957083967817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116555825953276111957089 6087416869464957083967817)
              ·
                refine ⟨4565562652098717812975863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087416869464957083967817 4565562652098717812975863)
                ·
                  refine ⟨6848343978148076719463795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565562652098717812975863 6848343978148076719463795)
                  ·
                    refine ⟨10272515967222115079195693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848343978148076719463795 10272515967222115079195693)
                    ·
                      refine ⟨3852193487708293154698385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272515967222115079195693 3852193487708293154698385)
                      ·
                        rfl

theorem cell23_7502120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7502120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502120 prefixEnd_7502120 := by exact prefixLift 7502120
  have htrace : WordTrace (prefixWord ++ tailWord_7502120) baseStart_7502120 baseEnd_7502120 := by
    simpa [prefixWord, tailWord_7502120, baseEnd_7502120] using wordTrace_append hprefix tailTrace_7502120
  have hstable : (prefixWord ++ tailWord_7502120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502120).length < 2 ^ (prefixWord ++ tailWord_7502120).sum := by decide
  have hdescent : baseEnd_7502120 < baseStart_7502120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502132 : List Nat := [2, 5, 1, 1, 1, 4, 1, 8]
def baseStart_7502132 : Nat := 118140960795 + 7502132 * 2 ^ 59
def prefixEnd_7502132 : Nat := 4983230072969 + 3 ^ 40 * 7502132 * 2
def baseEnd_7502132 : Nat := 142674061091709152138827

theorem tailTrace_7502132 : CollatzResearch.WordTrace tailWord_7502132 prefixEnd_7502132 142674061091709152138827 := by
  unfold tailWord_7502132
  simp only [CollatzResearch.WordTrace]
  refine ⟨136812616628532250492110325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182416822171376333989480433 136812616628532250492110325)
  ·
    refine ⟨12826182808924898483635343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136812616628532250492110325 12826182808924898483635343)
    ·
      refine ⟨19239274213387347725453015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12826182808924898483635343 19239274213387347725453015)
      ·
        refine ⟨28858911320081021588179523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239274213387347725453015 28858911320081021588179523)
        ·
          refine ⟨43288366980121532382269285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28858911320081021588179523 43288366980121532382269285)
          ·
            refine ⟨8116568808772787321675491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43288366980121532382269285 8116568808772787321675491)
            ·
              refine ⟨12174853213159180982513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116568808772787321675491 12174853213159180982513237)
              ·
                refine ⟨142674061091709152138827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12174853213159180982513237 142674061091709152138827)
                ·
                  rfl

theorem cell23_7502132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 8].length) (baseStart_7502132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502132 prefixEnd_7502132 := by exact prefixLift 7502132
  have htrace : WordTrace (prefixWord ++ tailWord_7502132) baseStart_7502132 baseEnd_7502132 := by
    simpa [prefixWord, tailWord_7502132, baseEnd_7502132] using wordTrace_append hprefix tailTrace_7502132
  have hstable : (prefixWord ++ tailWord_7502132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502132).length < 2 ^ (prefixWord ++ tailWord_7502132).sum := by decide
  have hdescent : baseEnd_7502132 < baseStart_7502132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502142 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_7502142 : Nat := 118140960795 + 7502142 * 2 ^ 59
def prefixEnd_7502142 : Nat := 4983230072969 + 3 ^ 40 * 7502142 * 2
def baseEnd_7502142 : Nat := 3852204784282692068623283

theorem tailTrace_7502142 : CollatzResearch.WordTrace tailWord_7502142 prefixEnd_7502142 3852204784282692068623283 := by
  unfold tailWord_7502142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203199748378534086510585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182417065324685515128056453 34203199748378534086510585)
  ·
    refine ⟨25652399811283900564882939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34203199748378534086510585 25652399811283900564882939)
    ·
      refine ⟨38478599716925850847324409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25652399811283900564882939 38478599716925850847324409)
      ·
        refine ⟨28858949787694388135493307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38478599716925850847324409 28858949787694388135493307)
        ·
          refine ⟨43288424681541582203239961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28858949787694388135493307 43288424681541582203239961)
          ·
            refine ⟨32466318511156186652429971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43288424681541582203239961 32466318511156186652429971)
            ·
              refine ⟨48699477766734279978644957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32466318511156186652429971 48699477766734279978644957)
              ·
                refine ⟨18262304162525354991991859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48699477766734279978644957 18262304162525354991991859)
                ·
                  refine ⟨27393456243788032487987789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18262304162525354991991859 27393456243788032487987789)
                  ·
                    refine ⟨10272546091420512182995421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27393456243788032487987789 10272546091420512182995421)
                    ·
                      refine ⟨3852204784282692068623283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272546091420512182995421 3852204784282692068623283)
                      ·
                        rfl

theorem cell23_7502142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_7502142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502142 prefixEnd_7502142 := by exact prefixLift 7502142
  have htrace : WordTrace (prefixWord ++ tailWord_7502142) baseStart_7502142 baseEnd_7502142 := by
    simpa [prefixWord, tailWord_7502142, baseEnd_7502142] using wordTrace_append hprefix tailTrace_7502142
  have hstable : (prefixWord ++ tailWord_7502142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502142).length < 2 ^ (prefixWord ++ tailWord_7502142).sum := by decide
  have hdescent : baseEnd_7502142 < baseStart_7502142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502152 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_7502152 : Nat := 118140960795 + 7502152 * 2 ^ 59
def prefixEnd_7502152 : Nat := 4983230072969 + 3 ^ 40 * 7502152 * 2
def baseEnd_7502152 : Nat := 3852209919089237029498237

theorem tailTrace_7502152 : CollatzResearch.WordTrace tailWord_7502152 prefixEnd_7502152 3852209919089237029498237 := by
  unfold tailWord_7502152
  simp only [CollatzResearch.WordTrace]
  refine ⟨136812981358496022199974355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182417308477994696266632473 136812981358496022199974355)
  ·
    refine ⟨205219472037744033299961533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136812981358496022199974355 205219472037744033299961533)
    ·
      refine ⟨76957302014154012487485575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205219472037744033299961533 76957302014154012487485575)
      ·
        refine ⟨115435953021231018731228363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76957302014154012487485575 115435953021231018731228363)
        ·
          refine ⟨173153929531846528096842545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115435953021231018731228363 173153929531846528096842545)
          ·
            refine ⟨129865447148884896072631909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173153929531846528096842545 129865447148884896072631909)
            ·
              refine ⟨24349771340415918013618483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129865447148884896072631909 24349771340415918013618483)
              ·
                refine ⟨36524657010623877020427725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24349771340415918013618483 36524657010623877020427725)
                ·
                  refine ⟨13696746378983953882660397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36524657010623877020427725 13696746378983953882660397)
                  ·
                    refine ⟨5136279892118982705997649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13696746378983953882660397 5136279892118982705997649)
                    ·
                      refine ⟨3852209919089237029498237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136279892118982705997649 3852209919089237029498237)
                      ·
                        rfl

theorem cell23_7502152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_7502152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502152 prefixEnd_7502152 := by exact prefixLift 7502152
  have htrace : WordTrace (prefixWord ++ tailWord_7502152) baseStart_7502152 baseEnd_7502152 := by
    simpa [prefixWord, tailWord_7502152, baseEnd_7502152] using wordTrace_append hprefix tailTrace_7502152
  have hstable : (prefixWord ++ tailWord_7502152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502152).length < 2 ^ (prefixWord ++ tailWord_7502152).sum := by decide
  have hdescent : baseEnd_7502152 < baseStart_7502152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502176 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3]
def baseStart_7502176 : Nat := 118140960795 + 7502176 * 2 ^ 59
def prefixEnd_7502176 : Nat := 4983230072969 + 3 ^ 40 * 7502176 * 2
def baseEnd_7502176 : Nat := 3852222242624944935598127

theorem tailTrace_7502176 : CollatzResearch.WordTrace tailWord_7502176 prefixEnd_7502176 3852222242624944935598127 := by
  unfold tailWord_7502176
  simp only [CollatzResearch.WordTrace]
  refine ⟨136813419034452548249411191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182417892045936730999214921 136813419034452548249411191)
  ·
    refine ⟨205220128551678822374116787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136813419034452548249411191 205220128551678822374116787)
    ·
      refine ⟨307830192827518233561175181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205220128551678822374116787 307830192827518233561175181)
      ·
        refine ⟨115436322310319337585440693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307830192827518233561175181 115436322310319337585440693)
        ·
          refine ⟨10822155216592437898635065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115436322310319337585440693 10822155216592437898635065)
          ·
            refine ⟨8116616412444328423976299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10822155216592437898635065 8116616412444328423976299)
            ·
              refine ⟨12174924618666492635964449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8116616412444328423976299 12174924618666492635964449)
              ·
                refine ⟨9131193463999869476973337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12174924618666492635964449 9131193463999869476973337)
                ·
                  refine ⟨6848395097999902107730003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9131193463999869476973337 6848395097999902107730003)
                  ·
                    refine ⟨10272592646999853161595005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848395097999902107730003 10272592646999853161595005)
                    ·
                      refine ⟨3852222242624944935598127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272592646999853161595005 3852222242624944935598127)
                      ·
                        rfl

theorem cell23_7502176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_7502176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502176 prefixEnd_7502176 := by exact prefixLift 7502176
  have htrace : WordTrace (prefixWord ++ tailWord_7502176) baseStart_7502176 baseEnd_7502176 := by
    simpa [prefixWord, tailWord_7502176, baseEnd_7502176] using wordTrace_append hprefix tailTrace_7502176
  have hstable : (prefixWord ++ tailWord_7502176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502176).length < 2 ^ (prefixWord ++ tailWord_7502176).sum := by decide
  have hdescent : baseEnd_7502176 < baseStart_7502176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502205 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 7]
def baseStart_7502205 : Nat := 118140960795 + 7502205 * 2 ^ 59
def prefixEnd_7502205 : Nat := 4983230072969 + 3 ^ 40 * 7502205 * 2
def baseEnd_7502205 : Nat := 428026348173769480237277

theorem tailTrace_7502205 : CollatzResearch.WordTrace tailWord_7502205 prefixEnd_7502205 428026348173769480237277 := by
  unfold tailWord_7502205
  simp only [CollatzResearch.WordTrace]
  refine ⟨273627895785800034451628069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182418597190533356301085379 273627895785800034451628069)
  ·
    refine ⟨51305230459837506459680263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273627895785800034451628069 51305230459837506459680263)
    ·
      refine ⟨76957845689756259689520395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51305230459837506459680263 76957845689756259689520395)
      ·
        refine ⟨115436768534634389534280593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76957845689756259689520395 115436768534634389534280593)
        ·
          refine ⟨86577576400975792150710445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115436768534634389534280593 86577576400975792150710445)
          ·
            refine ⟨32466591150365922056516417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86577576400975792150710445 32466591150365922056516417)
            ·
              refine ⟨24349943362774441542387313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32466591150365922056516417 24349943362774441542387313)
              ·
                refine ⟨18262457522080831156790485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24349943362774441542387313 18262457522080831156790485)
                ·
                  refine ⟨428026348173769480237277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18262457522080831156790485 428026348173769480237277)
                  ·
                    rfl

theorem cell23_7502205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_7502205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502205 prefixEnd_7502205 := by exact prefixLift 7502205
  have htrace : WordTrace (prefixWord ++ tailWord_7502205) baseStart_7502205 baseEnd_7502205 := by
    simpa [prefixWord, tailWord_7502205, baseEnd_7502205] using wordTrace_append hprefix tailTrace_7502205
  have hstable : (prefixWord ++ tailWord_7502205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502205).length < 2 ^ (prefixWord ++ tailWord_7502205).sum := by decide
  have hdescent : baseEnd_7502205 < baseStart_7502205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502239 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 5]
def baseStart_7502239 : Nat := 118140960795 + 7502239 * 2 ^ 59
def prefixEnd_7502239 : Nat := 4983230072969 + 3 ^ 40 * 7502239 * 2
def baseEnd_7502239 : Nat := 428028287989575354345593

theorem tailTrace_7502239 : CollatzResearch.WordTrace tailWord_7502239 prefixEnd_7502239 428028287989575354345593 := by
  unfold tailWord_7502239
  simp only [CollatzResearch.WordTrace]
  refine ⟨273629135867676858258365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182419423911784572172243847 273629135867676858258365771)
  ·
    refine ⟨410443703801515287387548657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273629135867676858258365771 410443703801515287387548657)
    ·
      refine ⟨307832777851136465540661493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410443703801515287387548657 307832777851136465540661493)
      ·
        refine ⟨28859322923544043644437015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307832777851136465540661493 28859322923544043644437015)
        ·
          refine ⟨43288984385316065466655523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28859322923544043644437015 43288984385316065466655523)
          ·
            refine ⟨64933476577974098199983285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43288984385316065466655523 64933476577974098199983285)
            ·
              refine ⟨6087513429185071706248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64933476577974098199983285 6087513429185071706248433)
              ·
                refine ⟨4565635071888803779686325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087513429185071706248433 4565635071888803779686325)
                ·
                  refine ⟨428028287989575354345593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565635071888803779686325 428028287989575354345593)
                  ·
                    rfl

theorem cell23_7502239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 5].length) (baseStart_7502239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502239 prefixEnd_7502239 := by exact prefixLift 7502239
  have htrace : WordTrace (prefixWord ++ tailWord_7502239) baseStart_7502239 baseEnd_7502239 := by
    simpa [prefixWord, tailWord_7502239, baseEnd_7502239] using wordTrace_append hprefix tailTrace_7502239
  have hstable : (prefixWord ++ tailWord_7502239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502239).length < 2 ^ (prefixWord ++ tailWord_7502239).sum := by decide
  have hdescent : baseEnd_7502239 < baseStart_7502239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502245 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_7502245 : Nat := 118140960795 + 7502245 * 2 ^ 59
def prefixEnd_7502245 : Nat := 4983230072969 + 3 ^ 40 * 7502245 * 2
def baseEnd_7502245 : Nat := 3852257672790105165635309

theorem tailTrace_7502245 : CollatzResearch.WordTrace tailWord_7502245 prefixEnd_7502245 3852257672790105165635309 := by
  unfold tailWord_7502245
  simp only [CollatzResearch.WordTrace]
  refine ⟨273629354705655121283084189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182419569803770080855389459 273629354705655121283084189)
  ·
    refine ⟨102611008014620670481156571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273629354705655121283084189 102611008014620670481156571)
    ·
      refine ⟨153916512021931005721734857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102611008014620670481156571 153916512021931005721734857)
      ·
        refine ⟨115437384016448254291301143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153916512021931005721734857 115437384016448254291301143)
        ·
          refine ⟨173156076024672381436951715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115437384016448254291301143 173156076024672381436951715)
          ·
            refine ⟨259734114037008572155427573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173156076024672381436951715 259734114037008572155427573)
            ·
              refine ⟨24350073190969553639571335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259734114037008572155427573 24350073190969553639571335)
              ·
                refine ⟨36525109786454330459357003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24350073190969553639571335 36525109786454330459357003)
                ·
                  refine ⟨54787664679681495689035505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36525109786454330459357003 54787664679681495689035505)
                  ·
                    refine ⟨41090748509761121766776629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54787664679681495689035505 41090748509761121766776629)
                    ·
                      refine ⟨3852257672790105165635309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41090748509761121766776629 3852257672790105165635309)
                      ·
                        rfl

theorem cell23_7502245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_7502245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502245 prefixEnd_7502245 := by exact prefixLift 7502245
  have htrace : WordTrace (prefixWord ++ tailWord_7502245) baseStart_7502245 baseEnd_7502245 := by
    simpa [prefixWord, tailWord_7502245, baseEnd_7502245] using wordTrace_append hprefix tailTrace_7502245
  have hstable : (prefixWord ++ tailWord_7502245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502245).length < 2 ^ (prefixWord ++ tailWord_7502245).sum := by decide
  have hdescent : baseEnd_7502245 < baseStart_7502245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502272 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2]
def baseStart_7502272 : Nat := 118140960795 + 7502272 * 2 ^ 59
def prefixEnd_7502272 : Nat := 4983230072969 + 3 ^ 40 * 7502272 * 2
def baseEnd_7502272 : Nat := 3852271536767776559997685

theorem tailTrace_7502272 : CollatzResearch.WordTrace tailWord_7502272 prefixEnd_7502272 3852271536767776559997685 := by
  unfold tailWord_7502272
  simp only [CollatzResearch.WordTrace]
  refine ⟨136815169738278652447158535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182420226317704869929544713 136815169738278652447158535)
  ·
    refine ⟨205222754607417978670737803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136815169738278652447158535 205222754607417978670737803)
    ·
      refine ⟨307834131911126968006106705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205222754607417978670737803 307834131911126968006106705)
      ·
        refine ⟨230875598933345226004580029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307834131911126968006106705 230875598933345226004580029)
        ·
          refine ⟨86578349600004459751717511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230875598933345226004580029 86578349600004459751717511)
          ·
            refine ⟨129867524400006689627576267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86578349600004459751717511 129867524400006689627576267)
            ·
              refine ⟨194801286600010034441364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129867524400006689627576267 194801286600010034441364401)
              ·
                refine ⟨146100964950007525831023301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194801286600010034441364401 146100964950007525831023301)
                ·
                  refine ⟨27393930928126411093316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146100964950007525831023301 27393930928126411093316869)
                  ·
                    refine ⟨5136362049023702079996913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27393930928126411093316869 5136362049023702079996913)
                    ·
                      refine ⟨3852271536767776559997685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136362049023702079996913 3852271536767776559997685)
                      ·
                        rfl

theorem cell23_7502272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_7502272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502272 prefixEnd_7502272 := by exact prefixLift 7502272
  have htrace : WordTrace (prefixWord ++ tailWord_7502272) baseStart_7502272 baseEnd_7502272 := by
    simpa [prefixWord, tailWord_7502272, baseEnd_7502272] using wordTrace_append hprefix tailTrace_7502272
  have hstable : (prefixWord ++ tailWord_7502272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502272).length < 2 ^ (prefixWord ++ tailWord_7502272).sum := by decide
  have hdescent : baseEnd_7502272 < baseStart_7502272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502290 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_7502290 : Nat := 118140960795 + 7502290 * 2 ^ 59
def prefixEnd_7502290 : Nat := 4983230072969 + 3 ^ 40 * 7502290 * 2
def baseEnd_7502290 : Nat := 428031197713284165508067

theorem tailTrace_7502290 : CollatzResearch.WordTrace tailWord_7502290 prefixEnd_7502290 428031197713284165508067 := by
  unfold tailWord_7502290
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407748997623023492118081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182420663993661395978981549 68407748997623023492118081)
  ·
    refine ⟨51305811748217267619088561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68407748997623023492118081 51305811748217267619088561)
    ·
      refine ⟨38479358811162950714316421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51305811748217267619088561 38479358811162950714316421)
      ·
        refine ⟨7214879777093053258934329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38479358811162950714316421 7214879777093053258934329)
        ·
          refine ⟨5411159832819789944200747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214879777093053258934329 5411159832819789944200747)
          ·
            refine ⟨8116739749229684916301121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411159832819789944200747 8116739749229684916301121)
            ·
              refine ⟨6087554811922263687225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8116739749229684916301121 6087554811922263687225841)
              ·
                refine ⟨4565666108941697765419381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6087554811922263687225841 4565666108941697765419381)
                ·
                  refine ⟨428031197713284165508067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565666108941697765419381 428031197713284165508067)
                  ·
                    rfl

theorem cell23_7502290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_7502290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502290 prefixEnd_7502290 := by exact prefixLift 7502290
  have htrace : WordTrace (prefixWord ++ tailWord_7502290) baseStart_7502290 baseEnd_7502290 := by
    simpa [prefixWord, tailWord_7502290, baseEnd_7502290] using wordTrace_append hprefix tailTrace_7502290
  have hstable : (prefixWord ++ tailWord_7502290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502290).length < 2 ^ (prefixWord ++ tailWord_7502290).sum := by decide
  have hdescent : baseEnd_7502290 < baseStart_7502290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502312 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 6]
def baseStart_7502312 : Nat := 118140960795 + 7502312 * 2 ^ 59
def prefixEnd_7502312 : Nat := 4983230072969 + 3 ^ 40 * 7502312 * 2
def baseEnd_7502312 : Nat := 428032452888217378166389

theorem tailTrace_7502312 : CollatzResearch.WordTrace tailWord_7502312 prefixEnd_7502312 428032452888217378166389 := by
  unfold tailWord_7502312
  simp only [CollatzResearch.WordTrace]
  refine ⟨136815899198206195862886595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182421198930941594483848793 136815899198206195862886595)
  ·
    refine ⟨205223848797309293794329893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136815899198206195862886595 205223848797309293794329893)
    ·
      refine ⟨38479471649495492586436855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205223848797309293794329893 38479471649495492586436855)
      ·
        refine ⟨57719207474243238879655283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38479471649495492586436855 57719207474243238879655283)
        ·
          refine ⟨86578811211364858319482925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57719207474243238879655283 86578811211364858319482925)
          ·
            refine ⟨32467054204261821869806097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86578811211364858319482925 32467054204261821869806097)
            ·
              refine ⟨24350290653196366402354573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32467054204261821869806097 24350290653196366402354573)
              ·
                refine ⟨9131358994948637400882965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24350290653196366402354573 9131358994948637400882965)
                ·
                  refine ⟨428032452888217378166389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9131358994948637400882965 428032452888217378166389)
                  ·
                    rfl

theorem cell23_7502312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_7502312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502312 prefixEnd_7502312 := by exact prefixLift 7502312
  have htrace : WordTrace (prefixWord ++ tailWord_7502312) baseStart_7502312 baseEnd_7502312 := by
    simpa [prefixWord, tailWord_7502312, baseEnd_7502312] using wordTrace_append hprefix tailTrace_7502312
  have hstable : (prefixWord ++ tailWord_7502312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502312).length < 2 ^ (prefixWord ++ tailWord_7502312).sum := by decide
  have hdescent : baseEnd_7502312 < baseStart_7502312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502362 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_7502362 : Nat := 118140960795 + 7502362 * 2 ^ 59
def prefixEnd_7502362 : Nat := 4983230072969 + 3 ^ 40 * 7502362 * 2
def baseEnd_7502362 : Nat := 3852317750026681207872271

theorem tailTrace_7502362 : CollatzResearch.WordTrace tailWord_7502362 prefixEnd_7502362 3852317750026681207872271 := by
  unfold tailWord_7502362
  simp only [CollatzResearch.WordTrace]
  refine ⟨68408405511557812566273335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182422414697487500176728893 68408405511557812566273335)
  ·
    refine ⟨102612608267336718849410003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68408405511557812566273335 102612608267336718849410003)
    ·
      refine ⟨153918912401005078274115005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102612608267336718849410003 153918912401005078274115005)
      ·
        refine ⟨57719592150376904352793127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153918912401005078274115005 57719592150376904352793127)
        ·
          refine ⟨86579388225565356529189691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57719592150376904352793127 86579388225565356529189691)
          ·
            refine ⟨129869082338348034793784537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86579388225565356529189691 129869082338348034793784537)
            ·
              refine ⟨97401811753761026095338403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129869082338348034793784537 97401811753761026095338403)
              ·
                refine ⟨146102717630641539143007605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97401811753761026095338403 146102717630641539143007605)
                ·
                  refine ⟨13697129777872644294656963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146102717630641539143007605 13697129777872644294656963)
                  ·
                    refine ⟨20545694666808966441985445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13697129777872644294656963 20545694666808966441985445)
                    ·
                      refine ⟨3852317750026681207872271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20545694666808966441985445 3852317750026681207872271)
                      ·
                        rfl

theorem cell23_7502362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_7502362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502362 prefixEnd_7502362 := by exact prefixLift 7502362
  have htrace : WordTrace (prefixWord ++ tailWord_7502362) baseStart_7502362 baseEnd_7502362 := by
    simpa [prefixWord, tailWord_7502362, baseEnd_7502362] using wordTrace_append hprefix tailTrace_7502362
  have hstable : (prefixWord ++ tailWord_7502362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502362).length < 2 ^ (prefixWord ++ tailWord_7502362).sum := by decide
  have hdescent : baseEnd_7502362 < baseStart_7502362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502376 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7502376 : Nat := 118140960795 + 7502376 * 2 ^ 59
def prefixEnd_7502376 : Nat := 4983230072969 + 3 ^ 40 * 7502376 * 2
def baseEnd_7502376 : Nat := 1284108312918614717699069

theorem tailTrace_7502376 : CollatzResearch.WordTrace tailWord_7502376 prefixEnd_7502376 1284108312918614717699069 := by
  unfold tailWord_7502376
  simp only [CollatzResearch.WordTrace]
  refine ⟨136817066334090265328051491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182422755112120353770735321 136817066334090265328051491)
  ·
    refine ⟨205225599501135397992077237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136817066334090265328051491 205225599501135397992077237)
    ·
      refine ⟨19239899953231443561757241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205225599501135397992077237 19239899953231443561757241)
      ·
        refine ⟨14429924964923582671317931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19239899953231443561757241 14429924964923582671317931)
        ·
          refine ⟨21644887447385374006976897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14429924964923582671317931 21644887447385374006976897)
          ·
            refine ⟨16233665585539030505232673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21644887447385374006976897 16233665585539030505232673)
            ·
              refine ⟨12175249189154272878924505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16233665585539030505232673 12175249189154272878924505)
              ·
                refine ⟨9131436891865704659193379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12175249189154272878924505 9131436891865704659193379)
                ·
                  refine ⟨13697155337798556988790069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131436891865704659193379 13697155337798556988790069)
                  ·
                    refine ⟨1284108312918614717699069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13697155337798556988790069 1284108312918614717699069)
                    ·
                      rfl

theorem cell23_7502376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7502376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502376 prefixEnd_7502376 := by exact prefixLift 7502376
  have htrace : WordTrace (prefixWord ++ tailWord_7502376) baseStart_7502376 baseEnd_7502376 := by
    simpa [prefixWord, tailWord_7502376, baseEnd_7502376] using wordTrace_append hprefix tailTrace_7502376
  have hstable : (prefixWord ++ tailWord_7502376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502376).length < 2 ^ (prefixWord ++ tailWord_7502376).sum := by decide
  have hdescent : baseEnd_7502376 < baseStart_7502376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502390 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7502390 : Nat := 118140960795 + 7502390 * 2 ^ 59
def prefixEnd_7502390 : Nat := 4983230072969 + 3 ^ 40 * 7502390 * 2
def baseEnd_7502390 : Nat := 3852332127485007098322143

theorem tailTrace_7502390 : CollatzResearch.WordTrace tailWord_7502390 prefixEnd_7502390 3852332127485007098322143 := by
  unfold tailWord_7502390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102165205633113190444539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182423095526753207364741749 17102165205633113190444539)
  ·
    refine ⟨25653247808449669785666809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17102165205633113190444539 25653247808449669785666809)
    ·
      refine ⟨19239935856337252339250107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25653247808449669785666809 19239935856337252339250107)
      ·
        refine ⟨28859903784505878508875161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239935856337252339250107 28859903784505878508875161)
        ·
          refine ⟨21644927838379408881656371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28859903784505878508875161 21644927838379408881656371)
          ·
            refine ⟨32467391757569113322484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21644927838379408881656371 32467391757569113322484557)
            ·
              refine ⟨12175271909088417495931709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32467391757569113322484557 12175271909088417495931709)
              ·
                refine ⟨4565726965908156560974391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12175271909088417495931709 4565726965908156560974391)
                ·
                  refine ⟨6848590448862234841461587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565726965908156560974391 6848590448862234841461587)
                  ·
                    refine ⟨10272885673293352262192381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6848590448862234841461587 10272885673293352262192381)
                    ·
                      refine ⟨3852332127485007098322143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272885673293352262192381 3852332127485007098322143)
                      ·
                        rfl

theorem cell23_7502390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7502390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502390 prefixEnd_7502390 := by exact prefixLift 7502390
  have htrace : WordTrace (prefixWord ++ tailWord_7502390) baseStart_7502390 baseEnd_7502390 := by
    simpa [prefixWord, tailWord_7502390, baseEnd_7502390] using wordTrace_append hprefix tailTrace_7502390
  have hstable : (prefixWord ++ tailWord_7502390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502390).length < 2 ^ (prefixWord ++ tailWord_7502390).sum := by decide
  have hdescent : baseEnd_7502390 < baseStart_7502390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502392 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_7502392 : Nat := 118140960795 + 7502392 * 2 ^ 59
def prefixEnd_7502392 : Nat := 4983230072969 + 3 ^ 40 * 7502392 * 2
def baseEnd_7502392 : Nat := 3852333154446316090497133

theorem tailTrace_7502392 : CollatzResearch.WordTrace tailWord_7502392 prefixEnd_7502392 3852333154446316090497133 := by
  unfold tailWord_7502392
  simp only [CollatzResearch.WordTrace]
  refine ⟨136817358118061282694342715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182423144157415043592456953 136817358118061282694342715)
  ·
    refine ⟨205226037177091924041514073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136817358118061282694342715 205226037177091924041514073)
    ·
      refine ⟨153919527882818943031135555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205226037177091924041514073 153919527882818943031135555)
      ·
        refine ⟨230879291824228414546703333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153919527882818943031135555 230879291824228414546703333)
        ·
          refine ⟨43289867217042827727506875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230879291824228414546703333 43289867217042827727506875)
          ·
            refine ⟨64934800825564241591260313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43289867217042827727506875 64934800825564241591260313)
            ·
              refine ⟨48701100619173181193445235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64934800825564241591260313 48701100619173181193445235)
              ·
                refine ⟨73051650928759771790167853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48701100619173181193445235 73051650928759771790167853)
                ·
                  refine ⟨27394369098284914421312945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73051650928759771790167853 27394369098284914421312945)
                  ·
                    refine ⟨20545776823713685815984709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27394369098284914421312945 20545776823713685815984709)
                    ·
                      refine ⟨3852333154446316090497133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20545776823713685815984709 3852333154446316090497133)
                      ·
                        rfl

theorem cell23_7502392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_7502392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502392 prefixEnd_7502392 := by exact prefixLift 7502392
  have htrace : WordTrace (prefixWord ++ tailWord_7502392) baseStart_7502392 baseEnd_7502392 := by
    simpa [prefixWord, tailWord_7502392, baseEnd_7502392] using wordTrace_append hprefix tailTrace_7502392
  have hstable : (prefixWord ++ tailWord_7502392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502392).length < 2 ^ (prefixWord ++ tailWord_7502392).sum := by decide
  have hdescent : baseEnd_7502392 < baseStart_7502392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502395 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_7502395 : Nat := 118140960795 + 7502395 * 2 ^ 59
def prefixEnd_7502395 : Nat := 4983230072969 + 3 ^ 40 * 7502395 * 2
def baseEnd_7502395 : Nat := 3852334694888279578759619

theorem tailTrace_7502395 : CollatzResearch.WordTrace tailWord_7502395 prefixEnd_7502395 3852334694888279578759619 := by
  unfold tailWord_7502395
  simp only [CollatzResearch.WordTrace]
  refine ⟨273634825655111696901044639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182423217103407797934029759 273634825655111696901044639)
  ·
    refine ⟨410452238482667545351566959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273634825655111696901044639 410452238482667545351566959)
    ·
      refine ⟨615678357724001318027350439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410452238482667545351566959 615678357724001318027350439)
      ·
        refine ⟨923517536586001977041025659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615678357724001318027350439 923517536586001977041025659)
        ·
          refine ⟨1385276304879002965561538489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923517536586001977041025659 1385276304879002965561538489)
          ·
            refine ⟨1038957228659252224171153867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385276304879002965561538489 1038957228659252224171153867)
            ·
              refine ⟨1558435842988878336256730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038957228659252224171153867 1558435842988878336256730801)
              ·
                refine ⟨1168826882241658752192548101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558435842988878336256730801 1168826882241658752192548101)
                ·
                  refine ⟨219155040420311016036102769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1168826882241658752192548101 219155040420311016036102769)
                  ·
                    refine ⟨164366280315233262027077077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219155040420311016036102769 164366280315233262027077077)
                    ·
                      refine ⟨3852334694888279578759619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164366280315233262027077077 3852334694888279578759619)
                      ·
                        rfl

theorem cell23_7502395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_7502395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502395 prefixEnd_7502395 := by exact prefixLift 7502395
  have htrace : WordTrace (prefixWord ++ tailWord_7502395) baseStart_7502395 baseEnd_7502395 := by
    simpa [prefixWord, tailWord_7502395, baseEnd_7502395] using wordTrace_append hprefix tailTrace_7502395
  have hstable : (prefixWord ++ tailWord_7502395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502395).length < 2 ^ (prefixWord ++ tailWord_7502395).sum := by decide
  have hdescent : baseEnd_7502395 < baseStart_7502395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502399 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_7502399 : Nat := 118140960795 + 7502399 * 2 ^ 59
def prefixEnd_7502399 : Nat := 4983230072969 + 3 ^ 40 * 7502399 * 2
def baseEnd_7502399 : Nat := 3852336748810897563109601

theorem tailTrace_7502399 : CollatzResearch.WordTrace tailWord_7502399 prefixEnd_7502399 3852336748810897563109601 := by
  unfold tailWord_7502399
  simp only [CollatzResearch.WordTrace]
  refine ⟨273634971547097205584190251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182423314364731470389460167 273634971547097205584190251)
  ·
    refine ⟨410452457320645808376285377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273634971547097205584190251 410452457320645808376285377)
    ·
      refine ⟨307839342990484356282214033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410452457320645808376285377 307839342990484356282214033)
      ·
        refine ⟨230879507242863267211660525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307839342990484356282214033 230879507242863267211660525)
        ·
          refine ⟨86579815216073725204372697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230879507242863267211660525 86579815216073725204372697)
          ·
            refine ⟨64934861412055293903279523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86579815216073725204372697 64934861412055293903279523)
            ·
              refine ⟨97402292118082940854919285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64934861412055293903279523 97402292118082940854919285)
              ·
                refine ⟨9131464886070275705148683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97402292118082940854919285 9131464886070275705148683)
                ·
                  refine ⟨13697197329105413557723025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131464886070275705148683 13697197329105413557723025)
                  ·
                    refine ⟨10272897996829060168292269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13697197329105413557723025 10272897996829060168292269)
                    ·
                      refine ⟨3852336748810897563109601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272897996829060168292269 3852336748810897563109601)
                      ·
                        rfl

theorem cell23_7502399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_7502399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502399 prefixEnd_7502399 := by exact prefixLift 7502399
  have htrace : WordTrace (prefixWord ++ tailWord_7502399) baseStart_7502399 baseEnd_7502399 := by
    simpa [prefixWord, tailWord_7502399, baseEnd_7502399] using wordTrace_append hprefix tailTrace_7502399
  have hstable : (prefixWord ++ tailWord_7502399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502399).length < 2 ^ (prefixWord ++ tailWord_7502399).sum := by decide
  have hdescent : baseEnd_7502399 < baseStart_7502399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502430 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7502430 : Nat := 118140960795 + 7502430 * 2 ^ 59
def prefixEnd_7502430 : Nat := 4983230072969 + 3 ^ 40 * 7502430 * 2
def baseEnd_7502430 : Nat := 3852352666711186941821959

theorem tailTrace_7502430 : CollatzResearch.WordTrace tailWord_7502430 prefixEnd_7502430 3852352666711186941821959 := by
  unfold tailWord_7502430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204512776248112234821093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182424068139989931919045829 34204512776248112234821093)
  ·
    refine ⟨6413346145546521044028955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34204512776248112234821093 6413346145546521044028955)
    ·
      refine ⟨9620019218319781566043433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413346145546521044028955 9620019218319781566043433)
      ·
        refine ⟨7215014413739836174532575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9620019218319781566043433 7215014413739836174532575)
        ·
          refine ⟨10822521620609754261798863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215014413739836174532575 10822521620609754261798863)
          ·
            refine ⟨16233782430914631392698295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822521620609754261798863 16233782430914631392698295)
            ·
              refine ⟨24350673646371947089047443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16233782430914631392698295 24350673646371947089047443)
              ·
                refine ⟨36526010469557920633571165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24350673646371947089047443 36526010469557920633571165)
                ·
                  refine ⟨13697253926084220237589187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36526010469557920633571165 13697253926084220237589187)
                  ·
                    refine ⟨20545880889126330356383781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13697253926084220237589187 20545880889126330356383781)
                    ·
                      refine ⟨3852352666711186941821959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20545880889126330356383781 3852352666711186941821959)
                      ·
                        rfl

theorem cell23_7502430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7502430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502430 prefixEnd_7502430 := by exact prefixLift 7502430
  have htrace : WordTrace (prefixWord ++ tailWord_7502430) baseStart_7502430 baseEnd_7502430 := by
    simpa [prefixWord, tailWord_7502430, baseEnd_7502430] using wordTrace_append hprefix tailTrace_7502430
  have hstable : (prefixWord ++ tailWord_7502430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502430).length < 2 ^ (prefixWord ++ tailWord_7502430).sum := by decide
  have hdescent : baseEnd_7502430 < baseStart_7502430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502446 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7502446 : Nat := 118140960795 + 7502446 * 2 ^ 59
def prefixEnd_7502446 : Nat := 4983230072969 + 3 ^ 40 * 7502446 * 2
def baseEnd_7502446 : Nat := 3852360882401658879221885

theorem tailTrace_7502446 : CollatzResearch.WordTrace tailWord_7502446 prefixEnd_7502446 3852360882401658879221885 := by
  unfold tailWord_7502446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204585722240866576393899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182424457185284621740767461 34204585722240866576393899)
  ·
    refine ⟨51306878583361299864590849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34204585722240866576393899 51306878583361299864590849)
    ·
      refine ⟨38480158937520974898443137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51306878583361299864590849 38480158937520974898443137)
      ·
        refine ⟨28860119203140731173832353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38480158937520974898443137 28860119203140731173832353)
        ·
          refine ⟨21645089402355548380374265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28860119203140731173832353 21645089402355548380374265)
          ·
            refine ⟨16233817051766661285280699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21645089402355548380374265 16233817051766661285280699)
            ·
              refine ⟨24350725577649991927921049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16233817051766661285280699 24350725577649991927921049)
              ·
                refine ⟨18263044183237493945940787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24350725577649991927921049 18263044183237493945940787)
                ·
                  refine ⟨27394566274856240918911181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18263044183237493945940787 27394566274856240918911181)
                  ·
                    refine ⟨10272962353071090344591693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27394566274856240918911181 10272962353071090344591693)
                    ·
                      refine ⟨3852360882401658879221885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10272962353071090344591693 3852360882401658879221885)
                      ·
                        rfl

theorem cell23_7502446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7502446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502446 prefixEnd_7502446 := by exact prefixLift 7502446
  have htrace : WordTrace (prefixWord ++ tailWord_7502446) baseStart_7502446 baseEnd_7502446 := by
    simpa [prefixWord, tailWord_7502446, baseEnd_7502446] using wordTrace_append hprefix tailTrace_7502446
  have hstable : (prefixWord ++ tailWord_7502446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502446).length < 2 ^ (prefixWord ++ tailWord_7502446).sum := by decide
  have hdescent : baseEnd_7502446 < baseStart_7502446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502526 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_7502526 : Nat := 118140960795 + 7502526 * 2 ^ 59
def prefixEnd_7502526 : Nat := 4983230072969 + 3 ^ 40 * 7502526 * 2
def baseEnd_7502526 : Nat := 428044662317113174024613

theorem tailTrace_7502526 : CollatzResearch.WordTrace tailWord_7502526 prefixEnd_7502526 428044662317113174024613 := by
  unfold tailWord_7502526
  simp only [CollatzResearch.WordTrace]
  refine ⟨34204950452204638284257929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182426402411758070849375621 34204950452204638284257929)
  ·
    refine ⟨25653712839153478713193447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34204950452204638284257929 25653712839153478713193447)
    ·
      refine ⟨38480569258730218069790171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25653712839153478713193447 38480569258730218069790171)
      ·
        refine ⟨57720853888095327104685257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38480569258730218069790171 57720853888095327104685257)
        ·
          refine ⟨43290640416071495328513943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57720853888095327104685257 43290640416071495328513943)
          ·
            refine ⟨64935960624107242992770915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43290640416071495328513943 64935960624107242992770915)
            ·
              refine ⟨97403940936160864489156373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64935960624107242992770915 97403940936160864489156373)
              ·
                refine ⟨4565809731382540522929205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97403940936160864489156373 4565809731382540522929205)
                ·
                  refine ⟨428044662317113174024613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565809731382540522929205 428044662317113174024613)
                  ·
                    rfl

theorem cell23_7502526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_7502526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502526 prefixEnd_7502526 := by exact prefixLift 7502526
  have htrace : WordTrace (prefixWord ++ tailWord_7502526) baseStart_7502526 baseEnd_7502526 := by
    simpa [prefixWord, tailWord_7502526, baseEnd_7502526] using wordTrace_append hprefix tailTrace_7502526
  have hstable : (prefixWord ++ tailWord_7502526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502526).length < 2 ^ (prefixWord ++ tailWord_7502526).sum := by decide
  have hdescent : baseEnd_7502526 < baseStart_7502526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502556 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7502556 : Nat := 118140960795 + 7502556 * 2 ^ 59
def prefixEnd_7502556 : Nat := 4983230072969 + 3 ^ 40 * 7502556 * 2
def baseEnd_7502556 : Nat := 1284139121757884482948793

theorem tailTrace_7502556 : CollatzResearch.WordTrace tailWord_7502556 prefixEnd_7502556 1284139121757884482948793 := by
  unfold tailWord_7502556
  simp only [CollatzResearch.WordTrace]
  refine ⟨136820348903764210698827761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182427131871685614265103681 136820348903764210698827761)
  ·
    refine ⟨102615261677823158024120821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136820348903764210698827761 102615261677823158024120821)
    ·
      refine ⟨9620180782295921064761327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102615261677823158024120821 9620180782295921064761327)
      ·
        refine ⟨14430271173443881597141991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9620180782295921064761327 14430271173443881597141991)
        ·
          refine ⟨21645406760165822395712987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14430271173443881597141991 21645406760165822395712987)
          ·
            refine ⟨32468110140248733593569481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21645406760165822395712987 32468110140248733593569481)
            ·
              refine ⟨24351082605186550195177111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32468110140248733593569481 24351082605186550195177111)
              ·
                refine ⟨36526623907779825292765667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24351082605186550195177111 36526623907779825292765667)
                ·
                  refine ⟨54789935861669737939148501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36526623907779825292765667 54789935861669737939148501)
                  ·
                    refine ⟨1284139121757884482948793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54789935861669737939148501 1284139121757884482948793)
                    ·
                      rfl

theorem cell23_7502556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7502556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502556 prefixEnd_7502556 := by exact prefixLift 7502556
  have htrace : WordTrace (prefixWord ++ tailWord_7502556) baseStart_7502556 baseEnd_7502556 := by
    simpa [prefixWord, tailWord_7502556, baseEnd_7502556] using wordTrace_append hprefix tailTrace_7502556
  have hstable : (prefixWord ++ tailWord_7502556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502556).length < 2 ^ (prefixWord ++ tailWord_7502556).sum := by decide
  have hdescent : baseEnd_7502556 < baseStart_7502556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502559 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_7502559 : Nat := 118140960795 + 7502559 * 2 ^ 59
def prefixEnd_7502559 : Nat := 4983230072969 + 3 ^ 40 * 7502559 * 2
def baseEnd_7502559 : Nat := 3852418905715616937108865

theorem tailTrace_7502559 : CollatzResearch.WordTrace tailWord_7502559 prefixEnd_7502559 3852418905715616937108865 := by
  unfold tailWord_7502559
  simp only [CollatzResearch.WordTrace]
  refine ⟨273640807226517552910014731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182427204817678368606676487 273640807226517552910014731)
  ·
    refine ⟨410461210839776329365022097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273640807226517552910014731 410461210839776329365022097)
    ·
      refine ⟨307845908129832247023766573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410461210839776329365022097 307845908129832247023766573)
      ·
        refine ⟨115442215548687092633912465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307845908129832247023766573 115442215548687092633912465)
        ·
          refine ⟨86581661661515319475434349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115442215548687092633912465 86581661661515319475434349)
          ·
            refine ⟨32468123123068244803287881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86581661661515319475434349 32468123123068244803287881)
            ·
              refine ⟨24351092342301183602465911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32468123123068244803287881 24351092342301183602465911)
              ·
                refine ⟨36526638513451775403698867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24351092342301183602465911 36526638513451775403698867)
                ·
                  refine ⟨54789957770177663105548301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36526638513451775403698867 54789957770177663105548301)
                  ·
                    refine ⟨20546234163816623664580613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54789957770177663105548301 20546234163816623664580613)
                    ·
                      refine ⟨3852418905715616937108865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20546234163816623664580613 3852418905715616937108865)
                      ·
                        rfl

theorem cell23_7502559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_7502559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502559 prefixEnd_7502559 := by exact prefixLift 7502559
  have htrace : WordTrace (prefixWord ++ tailWord_7502559) baseStart_7502559 baseEnd_7502559 := by
    simpa [prefixWord, tailWord_7502559, baseEnd_7502559] using wordTrace_append hprefix tailTrace_7502559
  have hstable : (prefixWord ++ tailWord_7502559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502559).length < 2 ^ (prefixWord ++ tailWord_7502559).sum := by decide
  have hdescent : baseEnd_7502559 < baseStart_7502559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502569 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_7502569 : Nat := 118140960795 + 7502569 * 2 ^ 59
def prefixEnd_7502569 : Nat := 4983230072969 + 3 ^ 40 * 7502569 * 2
def baseEnd_7502569 : Nat := 1284141346840720632661273

theorem tailTrace_7502569 : CollatzResearch.WordTrace tailWord_7502569 prefixEnd_7502569 1284141346840720632661273 := by
  unfold tailWord_7502569
  simp only [CollatzResearch.WordTrace]
  refine ⟨273641171956481324617878761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182427447970987549745252507 273641171956481324617878761)
  ·
    refine ⟨205230878967360993463409071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273641171956481324617878761 205230878967360993463409071)
    ·
      refine ⟨307846318451041490195113607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205230878967360993463409071 307846318451041490195113607)
      ·
        refine ⟨461769477676562235292670411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307846318451041490195113607 461769477676562235292670411)
        ·
          refine ⟨692654216514843352939005617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461769477676562235292670411 692654216514843352939005617)
          ·
            refine ⟨519490662386132514704254213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692654216514843352939005617 519490662386132514704254213)
            ·
              refine ⟨97404499197399846507047665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519490662386132514704254213 97404499197399846507047665)
              ·
                refine ⟨73053374398049884880285749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97404499197399846507047665 73053374398049884880285749)
                ·
                  refine ⟨6848753849817176707526789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73053374398049884880285749 6848753849817176707526789)
                  ·
                    refine ⟨1284141346840720632661273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6848753849817176707526789 1284141346840720632661273)
                    ·
                      rfl

theorem cell23_7502569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_7502569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502569 prefixEnd_7502569 := by exact prefixLift 7502569
  have htrace : WordTrace (prefixWord ++ tailWord_7502569) baseStart_7502569 baseEnd_7502569 := by
    simpa [prefixWord, tailWord_7502569, baseEnd_7502569] using wordTrace_append hprefix tailTrace_7502569
  have hstable : (prefixWord ++ tailWord_7502569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502569).length < 2 ^ (prefixWord ++ tailWord_7502569).sum := by decide
  have hdescent : baseEnd_7502569 < baseStart_7502569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502586 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_7502586 : Nat := 118140960795 + 7502586 * 2 ^ 59
def prefixEnd_7502586 : Nat := 4983230072969 + 3 ^ 40 * 7502586 * 2
def baseEnd_7502586 : Nat := 1284144256564429443823747

theorem tailTrace_7502586 : CollatzResearch.WordTrace tailWord_7502586 prefixEnd_7502586 1284144256564429443823747 := by
  unfold tailWord_7502586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68410447999354934130311903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182427861331613157680831741 68410447999354934130311903)
  ·
    refine ⟨102615671999032401195467855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68410447999354934130311903 102615671999032401195467855)
    ·
      refine ⟨153923507998548601793201783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102615671999032401195467855 153923507998548601793201783)
      ·
        refine ⟨230885261997822902689802675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153923507998548601793201783 230885261997822902689802675)
        ·
          refine ⟨346327892996734354034704013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230885261997822902689802675 346327892996734354034704013)
          ·
            refine ⟨129872959873775382763014005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346327892996734354034704013 129872959873775382763014005)
            ·
              refine ⟨12175589988166442134032563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129872959873775382763014005 12175589988166442134032563)
              ·
                refine ⟨18263384982249663201048845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175589988166442134032563 18263384982249663201048845)
                ·
                  refine ⟨6848769368343623700393317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18263384982249663201048845 6848769368343623700393317)
                  ·
                    refine ⟨1284144256564429443823747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6848769368343623700393317 1284144256564429443823747)
                    ·
                      rfl

theorem cell23_7502586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_7502586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502586 prefixEnd_7502586 := by exact prefixLift 7502586
  have htrace : WordTrace (prefixWord ++ tailWord_7502586) baseStart_7502586 baseEnd_7502586 := by
    simpa [prefixWord, tailWord_7502586, baseEnd_7502586] using wordTrace_append hprefix tailTrace_7502586
  have hstable : (prefixWord ++ tailWord_7502586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502586).length < 2 ^ (prefixWord ++ tailWord_7502586).sum := by decide
  have hdescent : baseEnd_7502586 < baseStart_7502586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502596 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7502596 : Nat := 118140960795 + 7502596 * 2 ^ 59
def prefixEnd_7502596 : Nat := 4983230072969 + 3 ^ 40 * 7502596 * 2
def baseEnd_7502596 : Nat := 3852437904499833292346195

theorem tailTrace_7502596 : CollatzResearch.WordTrace tailWord_7502596 prefixEnd_7502596 3852437904499833292346195 := by
  unfold tailWord_7502596
  simp only [CollatzResearch.WordTrace]
  refine ⟨136821078363691754114555821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182428104484922338819407761 136821078363691754114555821)
  ·
    refine ⟨51307904386384407792958433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136821078363691754114555821 51307904386384407792958433)
    ·
      refine ⟨38480928289788305844718825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51307904386384407792958433 38480928289788305844718825)
      ·
        refine ⟨28860696217341229383539119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38480928289788305844718825 28860696217341229383539119)
        ·
          refine ⟨43291044326011844075308679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28860696217341229383539119 43291044326011844075308679)
          ·
            refine ⟨64936566489017766112963019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43291044326011844075308679 64936566489017766112963019)
            ·
              refine ⟨97404849733526649169444529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64936566489017766112963019 97404849733526649169444529)
              ·
                refine ⟨73053637300144986877083397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97404849733526649169444529 73053637300144986877083397)
                ·
                  refine ⟨13697556993777185039453137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73053637300144986877083397 13697556993777185039453137)
                  ·
                    refine ⟨10273167745332888779589853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13697556993777185039453137 10273167745332888779589853)
                    ·
                      refine ⟨3852437904499833292346195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10273167745332888779589853 3852437904499833292346195)
                      ·
                        rfl

theorem cell23_7502596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7502596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502596 prefixEnd_7502596 := by exact prefixLift 7502596
  have htrace : WordTrace (prefixWord ++ tailWord_7502596) baseStart_7502596 baseEnd_7502596 := by
    simpa [prefixWord, tailWord_7502596, baseEnd_7502596] using wordTrace_append hprefix tailTrace_7502596
  have hstable : (prefixWord ++ tailWord_7502596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502596).length < 2 ^ (prefixWord ++ tailWord_7502596).sum := by decide
  have hdescent : baseEnd_7502596 < baseStart_7502596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502609 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_7502609 : Nat := 118140960795 + 7502609 * 2 ^ 59
def prefixEnd_7502609 : Nat := 4983230072969 + 3 ^ 40 * 7502609 * 2
def baseEnd_7502609 : Nat := 3852444579748341741483635

theorem tailTrace_7502609 : CollatzResearch.WordTrace tailWord_7502609 prefixEnd_7502609 3852444579748341741483635 := by
  unfold tailWord_7502609
  simp only [CollatzResearch.WordTrace]
  refine ⟨273642630876336411449334881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182428420584224274299556587 273642630876336411449334881)
  ·
    refine ⟨205231973157252308587001161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273642630876336411449334881 205231973157252308587001161)
    ·
      refine ⟨153923979867939231440250871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205231973157252308587001161 153923979867939231440250871)
      ·
        refine ⟨230885969801908847160376307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153923979867939231440250871 230885969801908847160376307)
        ·
          refine ⟨346328954702863270740564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230885969801908847160376307 346328954702863270740564461)
          ·
            refine ⟨129873358013573726527711673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346328954702863270740564461 129873358013573726527711673)
            ·
              refine ⟨97405018510180294895783755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129873358013573726527711673 97405018510180294895783755)
              ·
                refine ⟨146107527765270442343675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97405018510180294895783755 146107527765270442343675633)
                ·
                  refine ⟨109580645823952831757756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146107527765270442343675633 109580645823952831757756725)
                  ·
                    refine ⟨10273185545995577977289693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109580645823952831757756725 10273185545995577977289693)
                    ·
                      refine ⟨3852444579748341741483635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10273185545995577977289693 3852444579748341741483635)
                      ·
                        rfl

theorem cell23_7502609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_7502609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502609 prefixEnd_7502609 := by exact prefixLift 7502609
  have htrace : WordTrace (prefixWord ++ tailWord_7502609) baseStart_7502609 baseEnd_7502609 := by
    simpa [prefixWord, tailWord_7502609, baseEnd_7502609] using wordTrace_append hprefix tailTrace_7502609
  have hstable : (prefixWord ++ tailWord_7502609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502609).length < 2 ^ (prefixWord ++ tailWord_7502609).sum := by decide
  have hdescent : baseEnd_7502609 < baseStart_7502609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502610 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7502610 : Nat := 118140960795 + 7502610 * 2 ^ 59
def prefixEnd_7502610 : Nat := 4983230072969 + 3 ^ 40 * 7502610 * 2
def baseEnd_7502610 : Nat := 3852445093228996237571131

theorem tailTrace_7502610 : CollatzResearch.WordTrace tailWord_7502610 prefixEnd_7502610 3852445093228996237571131 := by
  unfold tailWord_7502610
  simp only [CollatzResearch.WordTrace]
  refine ⟨68410666837333197155030321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182428444899555192413414189 68410666837333197155030321)
  ·
    refine ⟨51308000127999897866272741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68410666837333197155030321 51308000127999897866272741)
    ·
      refine ⟨9620250023999980849926139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51308000127999897866272741 9620250023999980849926139)
      ·
        refine ⟨14430375035999971274889209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9620250023999980849926139 14430375035999971274889209)
        ·
          refine ⟨10822781276999978456166907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14430375035999971274889209 10822781276999978456166907)
          ·
            refine ⟨16234171915499967684250361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10822781276999978456166907 16234171915499967684250361)
            ·
              refine ⟨12175628936624975763187771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16234171915499967684250361 12175628936624975763187771)
              ·
                refine ⟨18263443404937463644781657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175628936624975763187771 18263443404937463644781657)
                ·
                  refine ⟨13697582553703097733586243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18263443404937463644781657 13697582553703097733586243)
                  ·
                    refine ⟨20546373830554646600379365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13697582553703097733586243 20546373830554646600379365)
                    ·
                      refine ⟨3852445093228996237571131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20546373830554646600379365 3852445093228996237571131)
                      ·
                        rfl

theorem cell23_7502610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7502610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502610 prefixEnd_7502610 := by exact prefixLift 7502610
  have htrace : WordTrace (prefixWord ++ tailWord_7502610) baseStart_7502610 baseEnd_7502610 := by
    simpa [prefixWord, tailWord_7502610, baseEnd_7502610] using wordTrace_append hprefix tailTrace_7502610
  have hstable : (prefixWord ++ tailWord_7502610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502610).length < 2 ^ (prefixWord ++ tailWord_7502610).sum := by decide
  have hdescent : baseEnd_7502610 < baseStart_7502610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502666 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_7502666 : Nat := 118140960795 + 7502666 * 2 ^ 59
def prefixEnd_7502666 : Nat := 4983230072969 + 3 ^ 40 * 7502666 * 2
def baseEnd_7502666 : Nat := 3852473848145648018470873

theorem tailTrace_7502666 : CollatzResearch.WordTrace tailWord_7502666 prefixEnd_7502666 3852473848145648018470873 := by
  unfold tailWord_7502666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68411177459282477546039963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182429806558086606789439901 68411177459282477546039963)
  ·
    refine ⟨102616766188923716319059945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68411177459282477546039963 102616766188923716319059945)
    ·
      refine ⟨76962574641692787239294959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102616766188923716319059945 76962574641692787239294959)
      ·
        refine ⟨115443861962539180858942439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76962574641692787239294959 115443861962539180858942439)
        ·
          refine ⟨173165792943808771288413659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115443861962539180858942439 173165792943808771288413659)
          ·
            refine ⟨259748689415713156932620489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173165792943808771288413659 259748689415713156932620489)
            ·
              refine ⟨194811517061784867699465367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259748689415713156932620489 194811517061784867699465367)
              ·
                refine ⟨292217275592677301549198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194811517061784867699465367 292217275592677301549198051)
                ·
                  refine ⟨438325913389015952323797077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292217275592677301549198051 438325913389015952323797077)
                  ·
                    refine ⟨5136631797527530691294497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 438325913389015952323797077 5136631797527530691294497)
                    ·
                      refine ⟨3852473848145648018470873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136631797527530691294497 3852473848145648018470873)
                      ·
                        rfl

theorem cell23_7502666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_7502666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502666 prefixEnd_7502666 := by exact prefixLift 7502666
  have htrace : WordTrace (prefixWord ++ tailWord_7502666) baseStart_7502666 baseEnd_7502666 := by
    simpa [prefixWord, tailWord_7502666, baseEnd_7502666] using wordTrace_append hprefix tailTrace_7502666
  have hstable : (prefixWord ++ tailWord_7502666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502666).length < 2 ^ (prefixWord ++ tailWord_7502666).sum := by decide
  have hdescent : baseEnd_7502666 < baseStart_7502666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502693 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_7502693 : Nat := 118140960795 + 7502693 * 2 ^ 59
def prefixEnd_7502693 : Nat := 4983230072969 + 3 ^ 40 * 7502693 * 2
def baseEnd_7502693 : Nat := 1284162570707773137611083

theorem tailTrace_7502693 : CollatzResearch.WordTrace tailWord_7502693 prefixEnd_7502693 1284162570707773137611083 := by
  unfold tailWord_7502693
  simp only [CollatzResearch.WordTrace]
  refine ⟨273645694608032093795392733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182430463072021395863595155 273645694608032093795392733)
  ·
    refine ⟨102617135478012035173272275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273645694608032093795392733 102617135478012035173272275)
    ·
      refine ⟨153925703217018052759908413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102617135478012035173272275 153925703217018052759908413)
      ·
        refine ⟨57722138706381769784965655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153925703217018052759908413 57722138706381769784965655)
        ·
          refine ⟨86583208059572654677448483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57722138706381769784965655 86583208059572654677448483)
          ·
            refine ⟨129874812089358982016172725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86583208059572654677448483 129874812089358982016172725)
            ·
              refine ⟨12175763633377404564016193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129874812089358982016172725 12175763633377404564016193)
              ·
                refine ⟨9131822725033053423012145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12175763633377404564016193 9131822725033053423012145)
                ·
                  refine ⟨6848867043774790067259109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9131822725033053423012145 6848867043774790067259109)
                  ·
                    refine ⟨1284162570707773137611083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6848867043774790067259109 1284162570707773137611083)
                    ·
                      rfl

theorem cell23_7502693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_7502693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502693 prefixEnd_7502693 := by exact prefixLift 7502693
  have htrace : WordTrace (prefixWord ++ tailWord_7502693) baseStart_7502693 baseEnd_7502693 := by
    simpa [prefixWord, tailWord_7502693, baseEnd_7502693] using wordTrace_append hprefix tailTrace_7502693
  have hstable : (prefixWord ++ tailWord_7502693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502693).length < 2 ^ (prefixWord ++ tailWord_7502693).sum := by decide
  have hdescent : baseEnd_7502693 < baseStart_7502693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502700 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_7502700 : Nat := 118140960795 + 7502700 * 2 ^ 59
def prefixEnd_7502700 : Nat := 4983230072969 + 3 ^ 40 * 7502700 * 2
def baseEnd_7502700 : Nat := 3852491306487900885445717

theorem tailTrace_7502700 : CollatzResearch.WordTrace tailWord_7502700 prefixEnd_7502700 3852491306487900885445717 := by
  unfold tailWord_7502700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136822974959503366995448777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182430633279337822660598369 136822974959503366995448777)
  ·
    refine ⟨102617231219627525246586583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136822974959503366995448777 102617231219627525246586583)
    ·
      refine ⟨153925846829441287869879875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102617231219627525246586583 153925846829441287869879875)
      ·
        refine ⟨230888770244161931804819813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153925846829441287869879875 230888770244161931804819813)
        ·
          refine ⟨43291644420780362213403715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230888770244161931804819813 43291644420780362213403715)
          ·
            refine ⟨64937466631170543320105573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43291644420780362213403715 64937466631170543320105573)
            ·
              refine ⟨12175774993344476872519795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64937466631170543320105573 12175774993344476872519795)
              ·
                refine ⟨18263662490016715308779693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175774993344476872519795 18263662490016715308779693)
                ·
                  refine ⟨6848873433756268240792385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18263662490016715308779693 6848873433756268240792385)
                  ·
                    refine ⟨5136655075317201180594289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6848873433756268240792385 5136655075317201180594289)
                    ·
                      refine ⟨3852491306487900885445717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136655075317201180594289 3852491306487900885445717)
                      ·
                        rfl

theorem cell23_7502700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_7502700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502700 prefixEnd_7502700 := by exact prefixLift 7502700
  have htrace : WordTrace (prefixWord ++ tailWord_7502700) baseStart_7502700 baseEnd_7502700 := by
    simpa [prefixWord, tailWord_7502700, baseEnd_7502700] using wordTrace_append hprefix tailTrace_7502700
  have hstable : (prefixWord ++ tailWord_7502700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502700).length < 2 ^ (prefixWord ++ tailWord_7502700).sum := by decide
  have hdescent : baseEnd_7502700 < baseStart_7502700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502710 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_7502710 : Nat := 118140960795 + 7502710 * 2 ^ 59
def prefixEnd_7502710 : Nat := 4983230072969 + 3 ^ 40 * 7502710 * 2
def baseEnd_7502710 : Nat := 1284165480431481948773557

theorem tailTrace_7502710 : CollatzResearch.WordTrace tailWord_7502710 prefixEnd_7502710 1284165480431481948773557 := by
  unfold tailWord_7502710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102894665560656606172599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182430876432647003799174389 17102894665560656606172599)
  ·
    refine ⟨25654341998340984909258899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17102894665560656606172599 25654341998340984909258899)
    ·
      refine ⟨38481512997511477363888349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25654341998340984909258899 38481512997511477363888349)
      ·
        refine ⟨14430567374066804011458131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38481512997511477363888349 14430567374066804011458131)
        ·
          refine ⟨21645851061100206017187197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14430567374066804011458131 21645851061100206017187197)
          ·
            refine ⟨8117194147912577256445199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21645851061100206017187197 8117194147912577256445199)
            ·
              refine ⟨12175791221868865884667799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117194147912577256445199 12175791221868865884667799)
              ·
                refine ⟨18263686832803298827001699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175791221868865884667799 18263686832803298827001699)
                ·
                  refine ⟨27395530249204948240502549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18263686832803298827001699 27395530249204948240502549)
                  ·
                    refine ⟨1284165480431481948773557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27395530249204948240502549 1284165480431481948773557)
                    ·
                      rfl

theorem cell23_7502710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_7502710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502710 prefixEnd_7502710 := by exact prefixLift 7502710
  have htrace : WordTrace (prefixWord ++ tailWord_7502710) baseStart_7502710 baseEnd_7502710 := by
    simpa [prefixWord, tailWord_7502710, baseEnd_7502710] using wordTrace_append hprefix tailTrace_7502710
  have hstable : (prefixWord ++ tailWord_7502710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502710).length < 2 ^ (prefixWord ++ tailWord_7502710).sum := by decide
  have hdescent : baseEnd_7502710 < baseStart_7502710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502713 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_7502713 : Nat := 118140960795 + 7502713 * 2 ^ 59
def prefixEnd_7502713 : Nat := 4983230072969 + 3 ^ 40 * 7502713 * 2
def baseEnd_7502713 : Nat := 3852497981736409334583157

theorem tailTrace_7502713 : CollatzResearch.WordTrace tailWord_7502713 prefixEnd_7502713 3852497981736409334583157 := by
  unfold tailWord_7502713
  simp only [CollatzResearch.WordTrace]
  refine ⟨273646424067959637211120793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182430949378639758140747195 273646424067959637211120793)
  ·
    refine ⟨205234818050969727908340595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273646424067959637211120793 205234818050969727908340595)
    ·
      refine ⟨307852227076454591862510893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205234818050969727908340595 307852227076454591862510893)
      ·
        refine ⟨115444585153670471948441585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307852227076454591862510893 115444585153670471948441585)
        ·
          refine ⟨86583438865252853961331189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115444585153670471948441585 86583438865252853961331189)
          ·
            refine ⟨8117197393617455058874799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86583438865252853961331189 8117197393617455058874799)
            ·
              refine ⟨12175796090426182588312199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117197393617455058874799 12175796090426182588312199)
              ·
                refine ⟨18263694135639273882468299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12175796090426182588312199 18263694135639273882468299)
                ·
                  refine ⟨27395541203458910823702449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18263694135639273882468299 27395541203458910823702449)
                  ·
                    refine ⟨20546655902594183117776837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27395541203458910823702449 20546655902594183117776837)
                    ·
                      refine ⟨3852497981736409334583157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20546655902594183117776837 3852497981736409334583157)
                      ·
                        rfl

theorem cell23_7502713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_7502713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502713 prefixEnd_7502713 := by exact prefixLift 7502713
  have htrace : WordTrace (prefixWord ++ tailWord_7502713) baseStart_7502713 baseEnd_7502713 := by
    simpa [prefixWord, tailWord_7502713, baseEnd_7502713] using wordTrace_append hprefix tailTrace_7502713
  have hstable : (prefixWord ++ tailWord_7502713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502713).length < 2 ^ (prefixWord ++ tailWord_7502713).sum := by decide
  have hdescent : baseEnd_7502713 < baseStart_7502713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502719 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 7]
def baseStart_7502719 : Nat := 118140960795 + 7502719 * 2 ^ 59
def prefixEnd_7502719 : Nat := 4983230072969 + 3 ^ 40 * 7502719 * 2
def baseEnd_7502719 : Nat := 1284167020873445437036043

theorem tailTrace_7502719 : CollatzResearch.WordTrace tailWord_7502719 prefixEnd_7502719 1284167020873445437036043 := by
  unfold tailWord_7502719
  simp only [CollatzResearch.WordTrace]
  refine ⟨273646642905937900235839211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182431095270625266823892807 273646642905937900235839211)
  ·
    refine ⟨410469964358906850353758817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273646642905937900235839211 410469964358906850353758817)
    ·
      refine ⟨307852473269180137765319113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410469964358906850353758817 307852473269180137765319113)
      ·
        refine ⟨230889354951885103323989335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307852473269180137765319113 230889354951885103323989335)
        ·
          refine ⟨346334032427827654985984003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230889354951885103323989335 346334032427827654985984003)
          ·
            refine ⟨519501048641741482478976005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346334032427827654985984003 519501048641741482478976005)
            ·
              refine ⟨97406446620326527964808001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519501048641741482478976005 97406446620326527964808001)
              ·
                refine ⟨73054834965244895973606001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97406446620326527964808001 73054834965244895973606001)
                ·
                  refine ⟨54791126223933671980204501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73054834965244895973606001 54791126223933671980204501)
                  ·
                    refine ⟨1284167020873445437036043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54791126223933671980204501 1284167020873445437036043)
                    ·
                      rfl

theorem cell23_7502719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_7502719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502719 prefixEnd_7502719 := by exact prefixLift 7502719
  have htrace : WordTrace (prefixWord ++ tailWord_7502719) baseStart_7502719 baseEnd_7502719 := by
    simpa [prefixWord, tailWord_7502719, baseEnd_7502719] using wordTrace_append hprefix tailTrace_7502719
  have hstable : (prefixWord ++ tailWord_7502719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502719).length < 2 ^ (prefixWord ++ tailWord_7502719).sum := by decide
  have hdescent : baseEnd_7502719 < baseStart_7502719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502756 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_7502756 : Nat := 118140960795 + 7502756 * 2 ^ 59
def prefixEnd_7502756 : Nat := 4983230072969 + 3 ^ 40 * 7502756 * 2
def baseEnd_7502756 : Nat := 3852520061404552666345459

theorem tailTrace_7502756 : CollatzResearch.WordTrace tailWord_7502756 prefixEnd_7502756 3852520061404552666345459 := by
  unfold tailWord_7502756
  simp only [CollatzResearch.WordTrace]
  refine ⟨136823996203401927777468061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182431994937869237036624081 136823996203401927777468061)
  ·
    refine ⟨51308998576275722916550523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136823996203401927777468061 51308998576275722916550523)
    ·
      refine ⟨76963497864413584374825785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51308998576275722916550523 76963497864413584374825785)
      ·
        refine ⟨57722623398310188281119339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76963497864413584374825785 57722623398310188281119339)
        ·
          refine ⟨86583935097465282421679009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57722623398310188281119339 86583935097465282421679009)
          ·
            refine ⟨64937951323098961816259257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86583935097465282421679009 64937951323098961816259257)
            ·
              refine ⟨48703463492324221362194443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64937951323098961816259257 48703463492324221362194443)
              ·
                refine ⟨73055195238486332043291665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48703463492324221362194443 73055195238486332043291665)
                ·
                  refine ⟨54791396428864749032468749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73055195238486332043291665 54791396428864749032468749)
                  ·
                    refine ⟨20546773660824280887175781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54791396428864749032468749 20546773660824280887175781)
                    ·
                      refine ⟨3852520061404552666345459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20546773660824280887175781 3852520061404552666345459)
                      ·
                        rfl

theorem cell23_7502756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_7502756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502756 prefixEnd_7502756 := by exact prefixLift 7502756
  have htrace : WordTrace (prefixWord ++ tailWord_7502756) baseStart_7502756 baseEnd_7502756 := by
    simpa [prefixWord, tailWord_7502756, baseEnd_7502756] using wordTrace_append hprefix tailTrace_7502756
  have hstable : (prefixWord ++ tailWord_7502756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502756).length < 2 ^ (prefixWord ++ tailWord_7502756).sum := by decide
  have hdescent : baseEnd_7502756 < baseStart_7502756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502776 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_7502776 : Nat := 118140960795 + 7502776 * 2 ^ 59
def prefixEnd_7502776 : Nat := 4983230072969 + 3 ^ 40 * 7502776 * 2
def baseEnd_7502776 : Nat := 3852530331017642588095367

theorem tailTrace_7502776 : CollatzResearch.WordTrace tailWord_7502776 prefixEnd_7502776 3852530331017642588095367 := by
  unfold tailWord_7502776
  simp only [CollatzResearch.WordTrace]
  refine ⟨136824360933365699485332091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182432481244487599313776121 136824360933365699485332091)
  ·
    refine ⟨205236541400048549227998137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136824360933365699485332091 205236541400048549227998137)
    ·
      refine ⟨153927406050036411920998603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205236541400048549227998137 153927406050036411920998603)
      ·
        refine ⟨230891109075054617881497905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153927406050036411920998603 230891109075054617881497905)
        ·
          refine ⟨173168331806290963411123429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230891109075054617881497905 173168331806290963411123429)
          ·
            refine ⟨32469062213679555639585643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173168331806290963411123429 32469062213679555639585643)
            ·
              refine ⟨48703593320519333459378465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32469062213679555639585643 48703593320519333459378465)
              ·
                refine ⟨36527694990389500094533849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48703593320519333459378465 36527694990389500094533849)
                ·
                  refine ⟨27395771242792125070900387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36527694990389500094533849 27395771242792125070900387)
                  ·
                    refine ⟨41093656864188187606350581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27395771242792125070900387 41093656864188187606350581)
                    ·
                      refine ⟨3852530331017642588095367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41093656864188187606350581 3852530331017642588095367)
                      ·
                        rfl

theorem cell23_7502776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_7502776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502776 prefixEnd_7502776 := by exact prefixLift 7502776
  have htrace : WordTrace (prefixWord ++ tailWord_7502776) baseStart_7502776 baseEnd_7502776 := by
    simpa [prefixWord, tailWord_7502776, baseEnd_7502776] using wordTrace_append hprefix tailTrace_7502776
  have hstable : (prefixWord ++ tailWord_7502776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502776).length < 2 ^ (prefixWord ++ tailWord_7502776).sum := by decide
  have hdescent : baseEnd_7502776 < baseStart_7502776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502777 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7502777 : Nat := 118140960795 + 7502777 * 2 ^ 59
def prefixEnd_7502777 : Nat := 4983230072969 + 3 ^ 40 * 7502777 * 2
def baseEnd_7502777 : Nat := 3852530844498297084182863

theorem tailTrace_7502777 : CollatzResearch.WordTrace tailWord_7502777 prefixEnd_7502777 3852530844498297084182863 := by
  unfold tailWord_7502777
  simp only [CollatzResearch.WordTrace]
  refine ⟨273648758339727776141450585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182432505559818517427633723 273648758339727776141450585)
  ·
    refine ⟨205236568754795832106087939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273648758339727776141450585 205236568754795832106087939)
    ·
      refine ⟨307854853132193748159131909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205236568754795832106087939 307854853132193748159131909)
      ·
        refine ⟨57722784962286327779837233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307854853132193748159131909 57722784962286327779837233)
        ·
          refine ⟨43292088721714745834877925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57722784962286327779837233 43292088721714745834877925)
          ·
            refine ⟨8117266635321514844039611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43292088721714745834877925 8117266635321514844039611)
            ·
              refine ⟨12175899952982272266059417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117266635321514844039611 12175899952982272266059417)
              ·
                refine ⟨9131924964736704199544563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12175899952982272266059417 9131924964736704199544563)
                ·
                  refine ⟨13697887447105056299316845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131924964736704199544563 13697887447105056299316845)
                  ·
                    refine ⟨5136707792664396112243817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13697887447105056299316845 5136707792664396112243817)
                    ·
                      refine ⟨3852530844498297084182863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136707792664396112243817 3852530844498297084182863)
                      ·
                        rfl

theorem cell23_7502777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7502777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502777 prefixEnd_7502777 := by exact prefixLift 7502777
  have htrace : WordTrace (prefixWord ++ tailWord_7502777) baseStart_7502777 baseEnd_7502777 := by
    simpa [prefixWord, tailWord_7502777, baseEnd_7502777] using wordTrace_append hprefix tailTrace_7502777
  have hstable : (prefixWord ++ tailWord_7502777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502777).length < 2 ^ (prefixWord ++ tailWord_7502777).sum := by decide
  have hdescent : baseEnd_7502777 < baseStart_7502777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502823 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_7502823 : Nat := 118140960795 + 7502823 * 2 ^ 59
def prefixEnd_7502823 : Nat := 4983230072969 + 3 ^ 40 * 7502823 * 2
def baseEnd_7502823 : Nat := 3852554464608403904207651

theorem tailTrace_7502823 : CollatzResearch.WordTrace tailWord_7502823 prefixEnd_7502823 3852554464608403904207651 := by
  unfold tailWord_7502823
  simp only [CollatzResearch.WordTrace]
  refine ⟨273650436097561125997625123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182433624065040750665083415 273650436097561125997625123)
  ·
    refine ⟨410475654146341688996437685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273650436097561125997625123 410475654146341688996437685)
    ·
      refine ⟨38482092576219533343416033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410475654146341688996437685 38482092576219533343416033)
      ·
        refine ⟨28861569432164650007562025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38482092576219533343416033 28861569432164650007562025)
        ·
          refine ⟨21646177074123487505671519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28861569432164650007562025 21646177074123487505671519)
          ·
            refine ⟨32469265611185231258507279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21646177074123487505671519 32469265611185231258507279)
            ·
              refine ⟨48703898416777846887760919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32469265611185231258507279 48703898416777846887760919)
              ·
                refine ⟨73055847625166770331641379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48703898416777846887760919 73055847625166770331641379)
                ·
                  refine ⟨109583771437750155497462069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73055847625166770331641379 109583771437750155497462069)
                  ·
                    refine ⟨10273478572289077077887069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109583771437750155497462069 10273478572289077077887069)
                    ·
                      refine ⟨3852554464608403904207651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10273478572289077077887069 3852554464608403904207651)
                      ·
                        rfl

theorem cell23_7502823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_7502823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502823 prefixEnd_7502823 := by exact prefixLift 7502823
  have htrace : WordTrace (prefixWord ++ tailWord_7502823) baseStart_7502823 baseEnd_7502823 := by
    simpa [prefixWord, tailWord_7502823, baseEnd_7502823] using wordTrace_append hprefix tailTrace_7502823
  have hstable : (prefixWord ++ tailWord_7502823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502823).length < 2 ^ (prefixWord ++ tailWord_7502823).sum := by decide
  have hdescent : baseEnd_7502823 < baseStart_7502823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502873 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_7502873 : Nat := 118140960795 + 7502873 * 2 ^ 59
def prefixEnd_7502873 : Nat := 4983230072969 + 3 ^ 40 * 7502873 * 2
def baseEnd_7502873 : Nat := 1284193379547042902860807

theorem tailTrace_7502873 : CollatzResearch.WordTrace tailWord_7502873 prefixEnd_7502873 1284193379547042902860807 := by
  unfold tailWord_7502873
  simp only [CollatzResearch.WordTrace]
  refine ⟨273652259747379984536945273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182434839831586656357963515 273652259747379984536945273)
  ·
    refine ⟨205239194810534988402708955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273652259747379984536945273 205239194810534988402708955)
    ·
      refine ⟨307858792215802482604063433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205239194810534988402708955 307858792215802482604063433)
      ·
        refine ⟨230894094161851861953047575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307858792215802482604063433 230894094161851861953047575)
        ·
          refine ⟨346341141242777792929571363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230894094161851861953047575 346341141242777792929571363)
          ·
            refine ⟨519511711864166689394357045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346341141242777792929571363 519511711864166689394357045)
            ·
              refine ⟨48704222987265627130720973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519511711864166689394357045 48704222987265627130720973)
              ·
                refine ⟨18264083620224610174020365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48704222987265627130720973 18264083620224610174020365)
                ·
                  refine ⟨6849031357584228815257637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18264083620224610174020365 6849031357584228815257637)
                  ·
                    refine ⟨1284193379547042902860807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849031357584228815257637 1284193379547042902860807)
                    ·
                      rfl

theorem cell23_7502873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_7502873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502873 prefixEnd_7502873 := by exact prefixLift 7502873
  have htrace : WordTrace (prefixWord ++ tailWord_7502873) baseStart_7502873 baseEnd_7502873 := by
    simpa [prefixWord, tailWord_7502873, baseEnd_7502873] using wordTrace_append hprefix tailTrace_7502873
  have hstable : (prefixWord ++ tailWord_7502873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502873).length < 2 ^ (prefixWord ++ tailWord_7502873).sum := by decide
  have hdescent : baseEnd_7502873 < baseStart_7502873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502883 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3]
def baseStart_7502883 : Nat := 118140960795 + 7502883 * 2 ^ 59
def prefixEnd_7502883 : Nat := 4983230072969 + 3 ^ 40 * 7502883 * 2
def baseEnd_7502883 : Nat := 3852585273447673669457375

theorem tailTrace_7502883 : CollatzResearch.WordTrace tailWord_7502883 prefixEnd_7502883 3852585273447673669457375 := by
  unfold tailWord_7502883
  simp only [CollatzResearch.WordTrace]
  refine ⟨273652624477343756244809303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182435082984895837496539535 273652624477343756244809303)
  ·
    refine ⟨410478936716015634367213955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273652624477343756244809303 410478936716015634367213955)
    ·
      refine ⟨615718405074023451550820933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410478936716015634367213955 615718405074023451550820933)
      ·
        refine ⟨115447200951379397165778925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615718405074023451550820933 115447200951379397165778925)
        ·
          refine ⟨43292700356767273937167097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115447200951379397165778925 43292700356767273937167097)
          ·
            refine ⟨32469525267575455452875323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43292700356767273937167097 32469525267575455452875323)
            ·
              refine ⟨48704287901363183179312985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32469525267575455452875323 48704287901363183179312985)
              ·
                refine ⟨36528215926022387384484739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48704287901363183179312985 36528215926022387384484739)
                ·
                  refine ⟨54792323889033581076727109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36528215926022387384484739 54792323889033581076727109)
                  ·
                    refine ⟨10273560729193796451886333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54792323889033581076727109 10273560729193796451886333)
                    ·
                      refine ⟨3852585273447673669457375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10273560729193796451886333 3852585273447673669457375)
                      ·
                        rfl

theorem cell23_7502883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_7502883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502883 prefixEnd_7502883 := by exact prefixLift 7502883
  have htrace : WordTrace (prefixWord ++ tailWord_7502883) baseStart_7502883 baseEnd_7502883 := by
    simpa [prefixWord, tailWord_7502883, baseEnd_7502883] using wordTrace_append hprefix tailTrace_7502883
  have hstable : (prefixWord ++ tailWord_7502883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502883).length < 2 ^ (prefixWord ++ tailWord_7502883).sum := by decide
  have hdescent : baseEnd_7502883 < baseStart_7502883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502933 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7502933 : Nat := 118140960795 + 7502933 * 2 ^ 59
def prefixEnd_7502933 : Nat := 4983230072969 + 3 ^ 40 * 7502933 * 2
def baseEnd_7502933 : Nat := 1284203649160132824610715

theorem tailTrace_7502933 : CollatzResearch.WordTrace tailWord_7502933 prefixEnd_7502933 1284203649160132824610715 := by
  unfold tailWord_7502933
  simp only [CollatzResearch.WordTrace]
  refine ⟨273654448127162614784129453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182436298751441743189419635 273654448127162614784129453)
  ·
    refine ⟨102620418047685980544048545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273654448127162614784129453 102620418047685980544048545)
    ·
      refine ⟨76965313535764485408036409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102620418047685980544048545 76965313535764485408036409)
      ·
        refine ⟨57723985151823364056027307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76965313535764485408036409 57723985151823364056027307)
        ·
          refine ⟨86585977727735046084040961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57723985151823364056027307 86585977727735046084040961)
          ·
            refine ⟨64939483295801284563030721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86585977727735046084040961 64939483295801284563030721)
            ·
              refine ⟨48704612471850963422273041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64939483295801284563030721 48704612471850963422273041)
              ·
                refine ⟨36528459353888222566704781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48704612471850963422273041 36528459353888222566704781)
                ·
                  refine ⟨13698172257708083462514293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36528459353888222566704781 13698172257708083462514293)
                  ·
                    refine ⟨1284203649160132824610715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13698172257708083462514293 1284203649160132824610715)
                    ·
                      rfl

theorem cell23_7502933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7502933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502933 prefixEnd_7502933 := by exact prefixLift 7502933
  have htrace : WordTrace (prefixWord ++ tailWord_7502933) baseStart_7502933 baseEnd_7502933 := by
    simpa [prefixWord, tailWord_7502933, baseEnd_7502933] using wordTrace_append hprefix tailTrace_7502933
  have hstable : (prefixWord ++ tailWord_7502933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502933).length < 2 ^ (prefixWord ++ tailWord_7502933).sum := by decide
  have hdescent : baseEnd_7502933 < baseStart_7502933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502957 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7502957 : Nat := 118140960795 + 7502957 * 2 ^ 59
def prefixEnd_7502957 : Nat := 4983230072969 + 3 ^ 40 * 7502957 * 2
def baseEnd_7502957 : Nat := 3852623271016106379932035

theorem tailTrace_7502957 : CollatzResearch.WordTrace tailWord_7502957 prefixEnd_7502957 3852623271016106379932035 := by
  unfold tailWord_7502957
  simp only [CollatzResearch.WordTrace]
  refine ⟨273655323479075666883003125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182436882319383777922002083 273655323479075666883003125)
  ·
    refine ⟨25655186576163343770281543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273655323479075666883003125 25655186576163343770281543)
    ·
      refine ⟨38482779864245015655422315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25655186576163343770281543 38482779864245015655422315)
      ·
        refine ⟨57724169796367523483133473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38482779864245015655422315 57724169796367523483133473)
        ·
          refine ⟨43293127347275642612350105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57724169796367523483133473 43293127347275642612350105)
          ·
            refine ⟨32469845510456731959262579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43293127347275642612350105 32469845510456731959262579)
            ·
              refine ⟨48704768265685097938893869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32469845510456731959262579 48704768265685097938893869)
              ·
                refine ⟨18264288099631911727085201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48704768265685097938893869 18264288099631911727085201)
                ·
                  refine ⟨13698216074723933795313901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18264288099631911727085201 13698216074723933795313901)
                  ·
                    refine ⟨5136831028021475173242713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698216074723933795313901 5136831028021475173242713)
                    ·
                      refine ⟨3852623271016106379932035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136831028021475173242713 3852623271016106379932035)
                      ·
                        rfl

theorem cell23_7502957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7502957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502957 prefixEnd_7502957 := by exact prefixLift 7502957
  have htrace : WordTrace (prefixWord ++ tailWord_7502957) baseStart_7502957 baseEnd_7502957 := by
    simpa [prefixWord, tailWord_7502957, baseEnd_7502957] using wordTrace_append hprefix tailTrace_7502957
  have hstable : (prefixWord ++ tailWord_7502957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502957).length < 2 ^ (prefixWord ++ tailWord_7502957).sum := by decide
  have hdescent : baseEnd_7502957 < baseStart_7502957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7502983 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_7502983 : Nat := 118140960795 + 7502983 * 2 ^ 59
def prefixEnd_7502983 : Nat := 4983230072969 + 3 ^ 40 * 7502983 * 2
def baseEnd_7502983 : Nat := 3852636621513123278206915

theorem tailTrace_7502983 : CollatzResearch.WordTrace tailWord_7502983 prefixEnd_7502983 3852636621513123278206915 := by
  unfold tailWord_7502983
  simp only [CollatzResearch.WordTrace]
  refine ⟨273656271776981473323449603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182437514517987648882299735 273656271776981473323449603)
  ·
    refine ⟨410484407665472209985174405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273656271776981473323449603 410484407665472209985174405)
    ·
      refine ⟨76965826437276039372220201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410484407665472209985174405 76965826437276039372220201)
      ·
        refine ⟨57724369827957029529165151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76965826437276039372220201 57724369827957029529165151)
        ·
          refine ⟨86586554741935544293747727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57724369827957029529165151 86586554741935544293747727)
          ·
            refine ⟨129879832112903316440621591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86586554741935544293747727 129879832112903316440621591)
            ·
              refine ⟨194819748169354974660932387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129879832112903316440621591 194819748169354974660932387)
              ·
                refine ⟨292229622254032461991398581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194819748169354974660932387 292229622254032461991398581)
                ·
                  refine ⟨27396527086315543311693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292229622254032461991398581 27396527086315543311693617)
                  ·
                    refine ⟨20547395314736657483770213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27396527086315543311693617 20547395314736657483770213)
                    ·
                      refine ⟨3852636621513123278206915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20547395314736657483770213 3852636621513123278206915)
                      ·
                        rfl

theorem cell23_7502983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_7502983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7502983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7502983 prefixEnd_7502983 := by exact prefixLift 7502983
  have htrace : WordTrace (prefixWord ++ tailWord_7502983) baseStart_7502983 baseEnd_7502983 := by
    simpa [prefixWord, tailWord_7502983, baseEnd_7502983] using wordTrace_append hprefix tailTrace_7502983
  have hstable : (prefixWord ++ tailWord_7502983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7502983).length < 2 ^ (prefixWord ++ tailWord_7502983).sum := by decide
  have hdescent : baseEnd_7502983 < baseStart_7502983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7502983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503000 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7503000 : Nat := 118140960795 + 7503000 * 2 ^ 59
def prefixEnd_7503000 : Nat := 4983230072969 + 3 ^ 40 * 7503000 * 2
def baseEnd_7503000 : Nat := 3852645350684249711694337

theorem tailTrace_7503000 : CollatzResearch.WordTrace tailWord_7503000 prefixEnd_7503000 3852645350684249711694337 := by
  unfold tailWord_7503000
  simp only [CollatzResearch.WordTrace]
  refine ⟨136828445908959942613409227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182437927878613256817878969 136828445908959942613409227)
  ·
    refine ⟨205242668863439913920113841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136828445908959942613409227 205242668863439913920113841)
    ·
      refine ⟨153932001647579935440085381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205242668863439913920113841 153932001647579935440085381)
      ·
        refine ⟨28862250308921237895016009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153932001647579935440085381 28862250308921237895016009)
        ·
          refine ⟨21646687731690928421262007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28862250308921237895016009 21646687731690928421262007)
          ·
            refine ⟨32470031597536392631893011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21646687731690928421262007 32470031597536392631893011)
            ·
              refine ⟨48705047396304588947839517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32470031597536392631893011 48705047396304588947839517)
              ·
                refine ⟨18264392773614220855439819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48705047396304588947839517 18264392773614220855439819)
                ·
                  refine ⟨27396589160421331283159729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18264392773614220855439819 27396589160421331283159729)
                  ·
                    refine ⟨20547441870315998462369797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27396589160421331283159729 20547441870315998462369797)
                    ·
                      refine ⟨3852645350684249711694337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20547441870315998462369797 3852645350684249711694337)
                      ·
                        rfl

theorem cell23_7503000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7503000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503000 prefixEnd_7503000 := by exact prefixLift 7503000
  have htrace : WordTrace (prefixWord ++ tailWord_7503000) baseStart_7503000 baseEnd_7503000 := by
    simpa [prefixWord, tailWord_7503000, baseEnd_7503000] using wordTrace_append hprefix tailTrace_7503000
  have hstable : (prefixWord ++ tailWord_7503000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503000).length < 2 ^ (prefixWord ++ tailWord_7503000).sum := by decide
  have hdescent : baseEnd_7503000 < baseStart_7503000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503004 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_7503004 : Nat := 118140960795 + 7503004 * 2 ^ 59
def prefixEnd_7503004 : Nat := 4983230072969 + 3 ^ 40 * 7503004 * 2
def baseEnd_7503004 : Nat := 3852647404606867696044319

theorem tailTrace_7503004 : CollatzResearch.WordTrace tailWord_7503004 prefixEnd_7503004 3852647404606867696044319 := by
  unfold tailWord_7503004
  simp only [CollatzResearch.WordTrace]
  refine ⟨136828518854952696954982033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182438025139936929273309377 136828518854952696954982033)
  ·
    refine ⟨102621389141214522716236525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136828518854952696954982033 102621389141214522716236525)
    ·
      refine ⟨38483020927955446018588697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102621389141214522716236525 38483020927955446018588697)
      ·
        refine ⟨28862265695966584513941523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38483020927955446018588697 28862265695966584513941523)
        ·
          refine ⟨43293398543949876770912285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28862265695966584513941523 43293398543949876770912285)
          ·
            refine ⟨16235024453981203789092107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43293398543949876770912285 16235024453981203789092107)
            ·
              refine ⟨24352536680971805683638161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235024453981203789092107 24352536680971805683638161)
              ·
                refine ⟨18264402510728854262728621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24352536680971805683638161 18264402510728854262728621)
                ·
                  refine ⟨6849150941523320348523233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18264402510728854262728621 6849150941523320348523233)
                  ·
                    refine ⟨5136863206142490261392425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849150941523320348523233 5136863206142490261392425)
                    ·
                      refine ⟨3852647404606867696044319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136863206142490261392425 3852647404606867696044319)
                      ·
                        rfl

theorem cell23_7503004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_7503004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503004 prefixEnd_7503004 := by exact prefixLift 7503004
  have htrace : WordTrace (prefixWord ++ tailWord_7503004) baseStart_7503004 baseEnd_7503004 := by
    simpa [prefixWord, tailWord_7503004, baseEnd_7503004] using wordTrace_append hprefix tailTrace_7503004
  have hstable : (prefixWord ++ tailWord_7503004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503004).length < 2 ^ (prefixWord ++ tailWord_7503004).sum := by decide
  have hdescent : baseEnd_7503004 < baseStart_7503004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503021 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_7503021 : Nat := 118140960795 + 7503021 * 2 ^ 59
def prefixEnd_7503021 : Nat := 4983230072969 + 3 ^ 40 * 7503021 * 2
def baseEnd_7503021 : Nat := 3852656133777994129531741

theorem tailTrace_7503021 : CollatzResearch.WordTrace tailWord_7503021 prefixEnd_7503021 3852656133777994129531741 := by
  unfold tailWord_7503021
  simp only [CollatzResearch.WordTrace]
  refine ⟨273657657750843805813332917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182438438500562537208888611 273657657750843805813332917)
  ·
    refine ⟨25655405414141606794999961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273657657750843805813332917 25655405414141606794999961)
    ·
      refine ⟨19241554060606205096249971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25655405414141606794999961 19241554060606205096249971)
      ·
        refine ⟨28862331090909307644374957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19241554060606205096249971 28862331090909307644374957)
        ·
          refine ⟨10823374159090990366640609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28862331090909307644374957 10823374159090990366640609)
          ·
            refine ⟨8117530619318242774980457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10823374159090990366640609 8117530619318242774980457)
            ·
              refine ⟨6088147964488682081235343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8117530619318242774980457 6088147964488682081235343)
              ·
                refine ⟨9132221946733023121853015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088147964488682081235343 9132221946733023121853015)
                ·
                  refine ⟨13698332920099534682779523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132221946733023121853015 13698332920099534682779523)
                  ·
                    refine ⟨20547499380149302024169285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13698332920099534682779523 20547499380149302024169285)
                    ·
                      refine ⟨3852656133777994129531741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20547499380149302024169285 3852656133777994129531741)
                      ·
                        rfl

theorem cell23_7503021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_7503021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503021 prefixEnd_7503021 := by exact prefixLift 7503021
  have htrace : WordTrace (prefixWord ++ tailWord_7503021) baseStart_7503021 baseEnd_7503021 := by
    simpa [prefixWord, tailWord_7503021, baseEnd_7503021] using wordTrace_append hprefix tailTrace_7503021
  have hstable : (prefixWord ++ tailWord_7503021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503021).length < 2 ^ (prefixWord ++ tailWord_7503021).sum := by decide
  have hdescent : baseEnd_7503021 < baseStart_7503021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503043 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_7503043 : Nat := 118140960795 + 7503043 * 2 ^ 59
def prefixEnd_7503043 : Nat := 4983230072969 + 3 ^ 40 * 7503043 * 2
def baseEnd_7503043 : Nat := 3852667430352393043456639

theorem tailTrace_7503043 : CollatzResearch.WordTrace tailWord_7503043 prefixEnd_7503043 3852667430352393043456639 := by
  unfold tailWord_7503043
  simp only [CollatzResearch.WordTrace]
  refine ⟨273658460156764103570633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182438973437842735713755855 273658460156764103570633783)
  ·
    refine ⟨410487690235146155355950675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273658460156764103570633783 410487690235146155355950675)
    ·
      refine ⟨615731535352719233033926013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410487690235146155355950675 615731535352719233033926013)
      ·
        refine ⟨230899325757269712387722255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615731535352719233033926013 230899325757269712387722255)
        ·
          refine ⟨346348988635904568581583383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230899325757269712387722255 346348988635904568581583383)
          ·
            refine ⟨519523482953856852872375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346348988635904568581583383 519523482953856852872375075)
            ·
              refine ⟨779285224430785279308562613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519523482953856852872375075 779285224430785279308562613)
              ·
                refine ⟨73057989790386119935177745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779285224430785279308562613 73057989790386119935177745)
                ·
                  refine ⟨54793492342789589951383309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73057989790386119935177745 54793492342789589951383309)
                  ·
                    refine ⟨20547559628546096231768741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54793492342789589951383309 20547559628546096231768741)
                    ·
                      refine ⟨3852667430352393043456639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20547559628546096231768741 3852667430352393043456639)
                      ·
                        rfl

theorem cell23_7503043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_7503043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503043 prefixEnd_7503043 := by exact prefixLift 7503043
  have htrace : WordTrace (prefixWord ++ tailWord_7503043) baseStart_7503043 baseEnd_7503043 := by
    simpa [prefixWord, tailWord_7503043, baseEnd_7503043] using wordTrace_append hprefix tailTrace_7503043
  have hstable : (prefixWord ++ tailWord_7503043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503043).length < 2 ^ (prefixWord ++ tailWord_7503043).sum := by decide
  have hdescent : baseEnd_7503043 < baseStart_7503043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503054 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_7503054 : Nat := 118140960795 + 7503054 * 2 ^ 59
def prefixEnd_7503054 : Nat := 4983230072969 + 3 ^ 40 * 7503054 * 2
def baseEnd_7503054 : Nat := 3852673078639592500419089

theorem tailTrace_7503054 : CollatzResearch.WordTrace tailWord_7503054 prefixEnd_7503054 3852673078639592500419089 := by
  unfold tailWord_7503054
  simp only [CollatzResearch.WordTrace]
  refine ⟨34207357669965531556160527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182439240906482834966189477 34207357669965531556160527)
  ·
    refine ⟨51311036504948297334240791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34207357669965531556160527 51311036504948297334240791)
    ·
      refine ⟨76966554757422446001361187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51311036504948297334240791 76966554757422446001361187)
      ·
        refine ⟨115449832136133669002041781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76966554757422446001361187 115449832136133669002041781)
        ·
          refine ⟨10823421762762531468941417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115449832136133669002041781 10823421762762531468941417)
          ·
            refine ⟨8117566322071898601706063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10823421762762531468941417 8117566322071898601706063)
            ·
              refine ⟨12176349483107847902559095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117566322071898601706063 12176349483107847902559095)
              ·
                refine ⟨18264524224661771853838643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176349483107847902559095 18264524224661771853838643)
                ·
                  refine ⟨27396786336992657780757965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18264524224661771853838643 27396786336992657780757965)
                  ·
                    refine ⟨10273794876372246667784237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27396786336992657780757965 10273794876372246667784237)
                    ·
                      refine ⟨3852673078639592500419089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10273794876372246667784237 3852673078639592500419089)
                      ·
                        rfl

theorem cell23_7503054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_7503054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503054 prefixEnd_7503054 := by exact prefixLift 7503054
  have htrace : WordTrace (prefixWord ++ tailWord_7503054) baseStart_7503054 baseEnd_7503054 := by
    simpa [prefixWord, tailWord_7503054, baseEnd_7503054] using wordTrace_append hprefix tailTrace_7503054
  have hstable : (prefixWord ++ tailWord_7503054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503054).length < 2 ^ (prefixWord ++ tailWord_7503054).sum := by decide
  have hdescent : baseEnd_7503054 < baseStart_7503054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503080 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7503080 : Nat := 118140960795 + 7503080 * 2 ^ 59
def prefixEnd_7503080 : Nat := 4983230072969 + 3 ^ 40 * 7503080 * 2
def baseEnd_7503080 : Nat := 3852686429136609398693969

theorem tailTrace_7503080 : CollatzResearch.WordTrace tailWord_7503080 prefixEnd_7503080 3852686429136609398693969 := by
  unfold tailWord_7503080
  simp only [CollatzResearch.WordTrace]
  refine ⟨136829904828815029444865347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182439873105086705926487129 136829904828815029444865347)
  ·
    refine ⟨205244857243222544167298021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136829904828815029444865347 205244857243222544167298021)
    ·
      refine ⟨38483410733104227031368379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205244857243222544167298021 38483410733104227031368379)
      ·
        refine ⟨57725116099656340547052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38483410733104227031368379 57725116099656340547052569)
        ·
          refine ⟨43293837074742255410289427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57725116099656340547052569 43293837074742255410289427)
          ·
            refine ⟨64940755612113383115434141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43293837074742255410289427 64940755612113383115434141)
            ·
              refine ⟨24352783354542518668287803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64940755612113383115434141 24352783354542518668287803)
              ·
                refine ⟨36529175031813778002431705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24352783354542518668287803 36529175031813778002431705)
                ·
                  refine ⟨27396881273860333501823779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36529175031813778002431705 27396881273860333501823779)
                  ·
                    refine ⟨41095321910790500252735669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27396881273860333501823779 41095321910790500252735669)
                    ·
                      refine ⟨3852686429136609398693969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41095321910790500252735669 3852686429136609398693969)
                      ·
                        rfl

theorem cell23_7503080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7503080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503080 prefixEnd_7503080 := by exact prefixLift 7503080
  have htrace : WordTrace (prefixWord ++ tailWord_7503080) baseStart_7503080 baseEnd_7503080 := by
    simpa [prefixWord, tailWord_7503080, baseEnd_7503080] using wordTrace_append hprefix tailTrace_7503080
  have hstable : (prefixWord ++ tailWord_7503080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503080).length < 2 ^ (prefixWord ++ tailWord_7503080).sum := by decide
  have hdescent : baseEnd_7503080 < baseStart_7503080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503140 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7503140 : Nat := 118140960795 + 7503140 * 2 ^ 59
def prefixEnd_7503140 : Nat := 4983230072969 + 3 ^ 40 * 7503140 * 2
def baseEnd_7503140 : Nat := 3852717237975879163943693

theorem tailTrace_7503140 : CollatzResearch.WordTrace tailWord_7503140 prefixEnd_7503140 3852717237975879163943693 := by
  unfold tailWord_7503140
  simp only [CollatzResearch.WordTrace]
  refine ⟨136830999018706344568457437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182441332024941792757943249 136830999018706344568457437)
  ·
    refine ⟨51311624632014879213171539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136830999018706344568457437 51311624632014879213171539)
    ·
      refine ⟨76967436948022318819757309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51311624632014879213171539 76967436948022318819757309)
      ·
        refine ⟨28862788855508369557408991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76967436948022318819757309 28862788855508369557408991)
        ·
          refine ⟨43294183283262554336113487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28862788855508369557408991 43294183283262554336113487)
          ·
            refine ⟨64941274924893831504170231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43294183283262554336113487 64941274924893831504170231)
            ·
              refine ⟨97411912387340747256255347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64941274924893831504170231 97411912387340747256255347)
              ·
                refine ⟨146117868581011120884383021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97411912387340747256255347 146117868581011120884383021)
                ·
                  refine ⟨54794200717879170331643633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146117868581011120884383021 54794200717879170331643633)
                  ·
                    refine ⟨41095650538409377748732725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54794200717879170331643633 41095650538409377748732725)
                    ·
                      refine ⟨3852717237975879163943693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41095650538409377748732725 3852717237975879163943693)
                      ·
                        rfl

theorem cell23_7503140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7503140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503140 prefixEnd_7503140 := by exact prefixLift 7503140
  have htrace : WordTrace (prefixWord ++ tailWord_7503140) baseStart_7503140 baseEnd_7503140 := by
    simpa [prefixWord, tailWord_7503140, baseEnd_7503140] using wordTrace_append hprefix tailTrace_7503140
  have hstable : (prefixWord ++ tailWord_7503140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503140).length < 2 ^ (prefixWord ++ tailWord_7503140).sum := by decide
  have hdescent : baseEnd_7503140 < baseStart_7503140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503167 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 6, 2]
def baseStart_7503167 : Nat := 118140960795 + 7503167 * 2 ^ 59
def prefixEnd_7503167 : Nat := 4983230072969 + 3 ^ 40 * 7503167 * 2
def baseEnd_7503167 : Nat := 3852731101953550558306069

theorem tailTrace_7503167 : CollatzResearch.WordTrace tailWord_7503167 prefixEnd_7503167 3852731101953550558306069 := by
  unfold tailWord_7503167
  simp only [CollatzResearch.WordTrace]
  refine ⟨273662982808314872748147755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182441988538876581832098503 273662982808314872748147755)
  ·
    refine ⟨410494474212472309122221633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273662982808314872748147755 410494474212472309122221633)
    ·
      refine ⟨307870855659354231841666225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410494474212472309122221633 307870855659354231841666225)
      ·
        refine ⟨230903141744515673881249669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307870855659354231841666225 230903141744515673881249669)
        ·
          refine ⟨43294339077096688852734313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230903141744515673881249669 43294339077096688852734313)
          ·
            refine ⟨32470754307822516639550735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43294339077096688852734313 32470754307822516639550735)
            ·
              refine ⟨48706131461733774959326103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32470754307822516639550735 48706131461733774959326103)
              ·
                refine ⟨73059197192600662438989155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48706131461733774959326103 73059197192600662438989155)
                ·
                  refine ⟨109588795788900993658483733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73059197192600662438989155 109588795788900993658483733)
                  ·
                    refine ⟨5136974802604734077741425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109588795788900993658483733 5136974802604734077741425)
                    ·
                      refine ⟨3852731101953550558306069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5136974802604734077741425 3852731101953550558306069)
                      ·
                        rfl

theorem cell23_7503167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_7503167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503167 prefixEnd_7503167 := by exact prefixLift 7503167
  have htrace : WordTrace (prefixWord ++ tailWord_7503167) baseStart_7503167 baseEnd_7503167 := by
    simpa [prefixWord, tailWord_7503167, baseEnd_7503167] using wordTrace_append hprefix tailTrace_7503167
  have hstable : (prefixWord ++ tailWord_7503167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503167).length < 2 ^ (prefixWord ++ tailWord_7503167).sum := by decide
  have hdescent : baseEnd_7503167 < baseStart_7503167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503194 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_7503194 : Nat := 118140960795 + 7503194 * 2 ^ 59
def prefixEnd_7503194 : Nat := 4983230072969 + 3 ^ 40 * 7503194 * 2
def baseEnd_7503194 : Nat := 1284248321977073984222815

theorem tailTrace_7503194 : CollatzResearch.WordTrace tailWord_7503194 prefixEnd_7503194 1284248321977073984222815 := by
  unfold tailWord_7503194
  simp only [CollatzResearch.WordTrace]
  refine ⟨68415991894804264089845159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182442645052811370906253757 68415991894804264089845159)
  ·
    refine ⟨102623987842206396134767739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68415991894804264089845159 102623987842206396134767739)
    ·
      refine ⟨153935981763309594202151609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102623987842206396134767739 153935981763309594202151609)
      ·
        refine ⟨115451986322482195651613707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153935981763309594202151609 115451986322482195651613707)
        ·
          refine ⟨173177979483723293477420561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115451986322482195651613707 173177979483723293477420561)
          ·
            refine ⟨129883484612792470108065421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173177979483723293477420561 129883484612792470108065421)
            ·
              refine ⟨48706306729797176290524533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129883484612792470108065421 48706306729797176290524533)
              ·
                refine ⟨4566216255918485277236675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48706306729797176290524533 4566216255918485277236675)
                ·
                  refine ⟨6849324383877727915855013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566216255918485277236675 6849324383877727915855013)
                  ·
                    refine ⟨1284248321977073984222815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849324383877727915855013 1284248321977073984222815)
                    ·
                      rfl

theorem cell23_7503194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_7503194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503194 prefixEnd_7503194 := by exact prefixLift 7503194
  have htrace : WordTrace (prefixWord ++ tailWord_7503194) baseStart_7503194 baseEnd_7503194 := by
    simpa [prefixWord, tailWord_7503194, baseEnd_7503194] using wordTrace_append hprefix tailTrace_7503194
  have hstable : (prefixWord ++ tailWord_7503194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503194).length < 2 ^ (prefixWord ++ tailWord_7503194).sum := by decide
  have hdescent : baseEnd_7503194 < baseStart_7503194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503207 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 8]
def baseStart_7503207 : Nat := 118140960795 + 7503207 * 2 ^ 59
def prefixEnd_7503207 : Nat := 4983230072969 + 3 ^ 40 * 7503207 * 2
def baseEnd_7503207 : Nat := 428083515686636711311765

theorem tailTrace_7503207 : CollatzResearch.WordTrace tailWord_7503207 prefixEnd_7503207 428083515686636711311765 := by
  unfold tailWord_7503207
  simp only [CollatzResearch.WordTrace]
  refine ⟨273664441728169959579603875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182442961152113306386402583 273664441728169959579603875)
  ·
    refine ⟨410496662592254939369405813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273664441728169959579603875 410496662592254939369405813)
    ·
      refine ⟨38484062118023900565881795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410496662592254939369405813 38484062118023900565881795)
      ·
        refine ⟨57726093177035850848822693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38484062118023900565881795 57726093177035850848822693)
        ·
          refine ⟨10823642470694222034154255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57726093177035850848822693 10823642470694222034154255)
          ·
            refine ⟨16235463706041333051231383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823642470694222034154255 16235463706041333051231383)
            ·
              refine ⟨24353195559061999576847075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235463706041333051231383 24353195559061999576847075)
              ·
                refine ⟨36529793338592999365270613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353195559061999576847075 36529793338592999365270613)
                ·
                  refine ⟨428083515686636711311765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36529793338592999365270613 428083515686636711311765)
                  ·
                    rfl

theorem cell23_7503207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 8].length) (baseStart_7503207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503207 prefixEnd_7503207 := by exact prefixLift 7503207
  have htrace : WordTrace (prefixWord ++ tailWord_7503207) baseStart_7503207 baseEnd_7503207 := by
    simpa [prefixWord, tailWord_7503207, baseEnd_7503207] using wordTrace_append hprefix tailTrace_7503207
  have hstable : (prefixWord ++ tailWord_7503207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503207).length < 2 ^ (prefixWord ++ tailWord_7503207).sum := by decide
  have hdescent : baseEnd_7503207 < baseStart_7503207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503227 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 5, 2]
def baseStart_7503227 : Nat := 118140960795 + 7503227 * 2 ^ 59
def prefixEnd_7503227 : Nat := 4983230072969 + 3 ^ 40 * 7503227 * 2
def baseEnd_7503227 : Nat := 3852761910792820323555793

theorem tailTrace_7503227 : CollatzResearch.WordTrace tailWord_7503227 prefixEnd_7503227 3852761910792820323555793 := by
  unfold tailWord_7503227
  simp only [CollatzResearch.WordTrace]
  refine ⟨273665171188097502995331935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182443447458731668663554623 273665171188097502995331935)
  ·
    refine ⟨410497756782146254492997903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273665171188097502995331935 410497756782146254492997903)
    ·
      refine ⟨615746635173219381739496855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410497756782146254492997903 615746635173219381739496855)
      ·
        refine ⟨923619952759829072609245283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615746635173219381739496855 923619952759829072609245283)
        ·
          refine ⟨1385429929139743608913867925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923619952759829072609245283 1385429929139743608913867925)
          ·
            refine ⟨64942027928425481667837559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1385429929139743608913867925 64942027928425481667837559)
            ·
              refine ⟨97413041892638222501756339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64942027928425481667837559 97413041892638222501756339)
              ·
                refine ⟨146119562838957333752634509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97413041892638222501756339 146119562838957333752634509)
                ·
                  refine ⟨54794836064609000157237941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146119562838957333752634509 54794836064609000157237941)
                  ·
                    refine ⟨5137015881057093764741057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54794836064609000157237941 5137015881057093764741057)
                    ·
                      refine ⟨3852761910792820323555793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137015881057093764741057 3852761910792820323555793)
                      ·
                        rfl

theorem cell23_7503227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5, 2].length) (baseStart_7503227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503227 prefixEnd_7503227 := by exact prefixLift 7503227
  have htrace : WordTrace (prefixWord ++ tailWord_7503227) baseStart_7503227 baseEnd_7503227 := by
    simpa [prefixWord, tailWord_7503227, baseEnd_7503227] using wordTrace_append hprefix tailTrace_7503227
  have hstable : (prefixWord ++ tailWord_7503227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503227).length < 2 ^ (prefixWord ++ tailWord_7503227).sum := by decide
  have hdescent : baseEnd_7503227 < baseStart_7503227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503237 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_7503237 : Nat := 118140960795 + 7503237 * 2 ^ 59
def prefixEnd_7503237 : Nat := 4983230072969 + 3 ^ 40 * 7503237 * 2
def baseEnd_7503237 : Nat := 1284255681866455094810249

theorem tailTrace_7503237 : CollatzResearch.WordTrace tailWord_7503237 prefixEnd_7503237 1284255681866455094810249 := by
  unfold tailWord_7503237
  simp only [CollatzResearch.WordTrace]
  refine ⟨273665535918061274703195965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182443690612040849802130643 273665535918061274703195965)
  ·
    refine ⟨102624575969272978013698487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273665535918061274703195965 102624575969272978013698487)
    ·
      refine ⟨153936863953909467020547731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102624575969272978013698487 153936863953909467020547731)
      ·
        refine ⟨230905295930864200530821597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153936863953909467020547731 230905295930864200530821597)
        ·
          refine ⟨86589485974074075199058099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230905295930864200530821597 86589485974074075199058099)
          ·
            refine ⟨129884228961111112798587149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86589485974074075199058099 129884228961111112798587149)
            ·
              refine ⟨48706585860416667299470181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129884228961111112798587149 48706585860416667299470181)
              ·
                refine ⟨9132484848828125118650659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48706585860416667299470181 9132484848828125118650659)
                ·
                  refine ⟨13698727273242187677975989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132484848828125118650659 13698727273242187677975989)
                  ·
                    refine ⟨1284255681866455094810249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13698727273242187677975989 1284255681866455094810249)
                    ·
                      rfl

theorem cell23_7503237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_7503237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503237 prefixEnd_7503237 := by exact prefixLift 7503237
  have htrace : WordTrace (prefixWord ++ tailWord_7503237) baseStart_7503237 baseEnd_7503237 := by
    simpa [prefixWord, tailWord_7503237, baseEnd_7503237] using wordTrace_append hprefix tailTrace_7503237
  have hstable : (prefixWord ++ tailWord_7503237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503237).length < 2 ^ (prefixWord ++ tailWord_7503237).sum := by decide
  have hdescent : baseEnd_7503237 < baseStart_7503237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503244 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_7503244 : Nat := 118140960795 + 7503244 * 2 ^ 59
def prefixEnd_7503244 : Nat := 4983230072969 + 3 ^ 40 * 7503244 * 2
def baseEnd_7503244 : Nat := 3852770639963946757043215

theorem tailTrace_7503244 : CollatzResearch.WordTrace tailWord_7503244 prefixEnd_7503244 3852770639963946757043215 := by
  unfold tailWord_7503244
  simp only [CollatzResearch.WordTrace]
  refine ⟨136832895614517957449350393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182443860819357276599133857 136832895614517957449350393)
  ·
    refine ⟨102624671710888468087012795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136832895614517957449350393 102624671710888468087012795)
    ·
      refine ⟨153937007566332702130519193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102624671710888468087012795 153937007566332702130519193)
      ·
        refine ⟨115452755674749526597889395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153937007566332702130519193 115452755674749526597889395)
        ·
          refine ⟨173179133512124289896834093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115452755674749526597889395 173179133512124289896834093)
          ·
            refine ⟨64942175067046608711312785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173179133512124289896834093 64942175067046608711312785)
            ·
              refine ⟨48706631300284956533484589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64942175067046608711312785 48706631300284956533484589)
              ·
                refine ⟨18264986737606858700056721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48706631300284956533484589 18264986737606858700056721)
                ·
                  refine ⟨13698740053205144025042541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18264986737606858700056721 13698740053205144025042541)
                  ·
                    refine ⟨5137027519951929009390953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698740053205144025042541 5137027519951929009390953)
                    ·
                      refine ⟨3852770639963946757043215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137027519951929009390953 3852770639963946757043215)
                      ·
                        rfl

theorem cell23_7503244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_7503244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503244 prefixEnd_7503244 := by exact prefixLift 7503244
  have htrace : WordTrace (prefixWord ++ tailWord_7503244) baseStart_7503244 baseEnd_7503244 := by
    simpa [prefixWord, tailWord_7503244, baseEnd_7503244] using wordTrace_append hprefix tailTrace_7503244
  have hstable : (prefixWord ++ tailWord_7503244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503244).length < 2 ^ (prefixWord ++ tailWord_7503244).sum := by decide
  have hdescent : baseEnd_7503244 < baseStart_7503244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503261 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_7503261 : Nat := 118140960795 + 7503261 * 2 ^ 59
def prefixEnd_7503261 : Nat := 4983230072969 + 3 ^ 40 * 7503261 * 2
def baseEnd_7503261 : Nat := 3852779369135073190530637

theorem tailTrace_7503261 : CollatzResearch.WordTrace tailWord_7503261 prefixEnd_7503261 3852779369135073190530637 := by
  unfold tailWord_7503261
  simp only [CollatzResearch.WordTrace]
  refine ⟨273666411269974326802069637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182444274179982884534713091 273666411269974326802069637)
  ·
    refine ⟨51312452113120186275388057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273666411269974326802069637 51312452113120186275388057)
    ·
      refine ⟨38484339084840139706541043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51312452113120186275388057 38484339084840139706541043)
      ·
        refine ⟨57726508627260209559811565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38484339084840139706541043 57726508627260209559811565)
        ·
          refine ⟨21647440735222578584929337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57726508627260209559811565 21647440735222578584929337)
          ·
            refine ⟨16235580551416933938697003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21647440735222578584929337 16235580551416933938697003)
            ·
              refine ⟨24353370827125400908045505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235580551416933938697003 24353370827125400908045505)
              ·
                refine ⟨18265028120344050681034129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24353370827125400908045505 18265028120344050681034129)
                ·
                  refine ⟨13698771090258038010775597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18265028120344050681034129 13698771090258038010775597)
                  ·
                    refine ⟨5137039158846764254040849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698771090258038010775597 5137039158846764254040849)
                    ·
                      refine ⟨3852779369135073190530637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137039158846764254040849 3852779369135073190530637)
                      ·
                        rfl

theorem cell23_7503261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_7503261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503261 prefixEnd_7503261 := by exact prefixLift 7503261
  have htrace : WordTrace (prefixWord ++ tailWord_7503261) baseStart_7503261 baseEnd_7503261 := by
    simpa [prefixWord, tailWord_7503261, baseEnd_7503261] using wordTrace_append hprefix tailTrace_7503261
  have hstable : (prefixWord ++ tailWord_7503261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503261).length < 2 ^ (prefixWord ++ tailWord_7503261).sum := by decide
  have hdescent : baseEnd_7503261 < baseStart_7503261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503267 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 4, 4]
def baseStart_7503267 : Nat := 118140960795 + 7503267 * 2 ^ 59
def prefixEnd_7503267 : Nat := 4983230072969 + 3 ^ 40 * 7503267 * 2
def baseEnd_7503267 : Nat := 1284260816673000055685203

theorem tailTrace_7503267 : CollatzResearch.WordTrace tailWord_7503267 prefixEnd_7503267 1284260816673000055685203 := by
  unfold tailWord_7503267
  simp only [CollatzResearch.WordTrace]
  refine ⟨273666630107952589826788055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182444420071968393217858703 273666630107952589826788055)
  ·
    refine ⟨410499945161928884740182083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273666630107952589826788055 410499945161928884740182083)
    ·
      refine ⟨615749917742893327110273125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410499945161928884740182083 615749917742893327110273125)
      ·
        refine ⟨115453109576792498833176211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615749917742893327110273125 115453109576792498833176211)
        ·
          refine ⟨173179664365188748249764317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115453109576792498833176211 173179664365188748249764317)
          ·
            refine ⟨64942374136945780593661619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173179664365188748249764317 64942374136945780593661619)
            ·
              refine ⟨97413561205418670890492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64942374136945780593661619 97413561205418670890492429)
              ·
                refine ⟨36530085452032001583934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97413561205418670890492429 36530085452032001583934661)
                ·
                  refine ⟨6849391022256000296987749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36530085452032001583934661 6849391022256000296987749)
                  ·
                    refine ⟨1284260816673000055685203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849391022256000296987749 1284260816673000055685203)
                    ·
                      rfl

theorem cell23_7503267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 4].length) (baseStart_7503267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503267 prefixEnd_7503267 := by exact prefixLift 7503267
  have htrace : WordTrace (prefixWord ++ tailWord_7503267) baseStart_7503267 baseEnd_7503267 := by
    simpa [prefixWord, tailWord_7503267, baseEnd_7503267] using wordTrace_append hprefix tailTrace_7503267
  have hstable : (prefixWord ++ tailWord_7503267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503267).length < 2 ^ (prefixWord ++ tailWord_7503267).sum := by decide
  have hdescent : baseEnd_7503267 < baseStart_7503267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503287 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_7503287 : Nat := 118140960795 + 7503287 * 2 ^ 59
def prefixEnd_7503287 : Nat := 4983230072969 + 3 ^ 40 * 7503287 * 2
def baseEnd_7503287 : Nat := 3852792719632090088805517

theorem tailTrace_7503287 : CollatzResearch.WordTrace tailWord_7503287 prefixEnd_7503287 3852792719632090088805517 := by
  unfold tailWord_7503287
  simp only [CollatzResearch.WordTrace]
  refine ⟨273667359567880133242516115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182444906378586755495010743 273667359567880133242516115)
  ·
    refine ⟨410501039351820199863774173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273667359567880133242516115 410501039351820199863774173)
    ·
      refine ⟨153937889756932574948915315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410501039351820199863774173 153937889756932574948915315)
      ·
        refine ⟨230906834635398862423372973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153937889756932574948915315 230906834635398862423372973)
        ·
          refine ⟨86590062988274573408764865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230906834635398862423372973 86590062988274573408764865)
          ·
            refine ⟨64942547241205930056573649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86590062988274573408764865 64942547241205930056573649)
            ·
              refine ⟨48706910430904447542430237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64942547241205930056573649 48706910430904447542430237)
              ·
                refine ⟨18265091411589167828411339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48706910430904447542430237 18265091411589167828411339)
                ·
                  refine ⟨27397637117383751742617009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18265091411589167828411339 27397637117383751742617009)
                  ·
                    refine ⟨20548227838037813806962757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27397637117383751742617009 20548227838037813806962757)
                    ·
                      refine ⟨3852792719632090088805517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20548227838037813806962757 3852792719632090088805517)
                      ·
                        rfl

theorem cell23_7503287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_7503287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503287 prefixEnd_7503287 := by exact prefixLift 7503287
  have htrace : WordTrace (prefixWord ++ tailWord_7503287) baseStart_7503287 baseEnd_7503287 := by
    simpa [prefixWord, tailWord_7503287, baseEnd_7503287] using wordTrace_append hprefix tailTrace_7503287
  have hstable : (prefixWord ++ tailWord_7503287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503287).length < 2 ^ (prefixWord ++ tailWord_7503287).sum := by decide
  have hdescent : baseEnd_7503287 < baseStart_7503287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503307 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3]
def baseStart_7503307 : Nat := 118140960795 + 7503307 * 2 ^ 59
def prefixEnd_7503307 : Nat := 4983230072969 + 3 ^ 40 * 7503307 * 2
def baseEnd_7503307 : Nat := 3852802989245180010555425

theorem tailTrace_7503307 : CollatzResearch.WordTrace tailWord_7503307 prefixEnd_7503307 3852802989245180010555425 := by
  unfold tailWord_7503307
  simp only [CollatzResearch.WordTrace]
  refine ⟨273668089027807676658244175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182445392685205117772162783 273668089027807676658244175)
  ·
    refine ⟨410502133541711514987366263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273668089027807676658244175 410502133541711514987366263)
    ·
      refine ⟨615753200312567272481049395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410502133541711514987366263 615753200312567272481049395)
      ·
        refine ⟨923629800468850908721574093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615753200312567272481049395 923629800468850908721574093)
        ·
          refine ⟨346361175175819090770590285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 923629800468850908721574093 346361175175819090770590285)
          ·
            refine ⟨129885440690932159038971357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346361175175819090770590285 129885440690932159038971357)
            ·
              refine ⟨48707040259099559639614259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129885440690932159038971357 48707040259099559639614259)
              ·
                refine ⟨73060560388649339459421389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48707040259099559639614259 73060560388649339459421389)
                ·
                  refine ⟨27397710145743502297283021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73060560388649339459421389 27397710145743502297283021)
                  ·
                    refine ⟨10274141304653813361481133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27397710145743502297283021 10274141304653813361481133)
                    ·
                      refine ⟨3852802989245180010555425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10274141304653813361481133 3852802989245180010555425)
                      ·
                        rfl

theorem cell23_7503307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].length) (baseStart_7503307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503307 prefixEnd_7503307 := by exact prefixLift 7503307
  have htrace : WordTrace (prefixWord ++ tailWord_7503307) baseStart_7503307 baseEnd_7503307 := by
    simpa [prefixWord, tailWord_7503307, baseEnd_7503307] using wordTrace_append hprefix tailTrace_7503307
  have hstable : (prefixWord ++ tailWord_7503307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503307).length < 2 ^ (prefixWord ++ tailWord_7503307).sum := by decide
  have hdescent : baseEnd_7503307 < baseStart_7503307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503318 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7503318 : Nat := 118140960795 + 7503318 * 2 ^ 59
def prefixEnd_7503318 : Nat := 4983230072969 + 3 ^ 40 * 7503318 * 2
def baseEnd_7503318 : Nat := 1284269545844126489172625

theorem tailTrace_7503318 : CollatzResearch.WordTrace tailWord_7503318 prefixEnd_7503318 1284269545844126489172625 := by
  unfold tailWord_7503318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104280639422989096055913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182445660153845217024596405 17104280639422989096055913)
  ·
    refine ⟨12828210479567241822041935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17104280639422989096055913 12828210479567241822041935)
    ·
      refine ⟨19242315719350862733062903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828210479567241822041935 19242315719350862733062903)
      ·
        refine ⟨28863473579026294099594355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242315719350862733062903 28863473579026294099594355)
        ·
          refine ⟨43295210368539441149391533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28863473579026294099594355 43295210368539441149391533)
          ·
            refine ⟨16235703888202290431021825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43295210368539441149391533 16235703888202290431021825)
            ·
              refine ⟨12176777916151717823266369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16235703888202290431021825 12176777916151717823266369)
              ·
                refine ⟨9132583437113788367449777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12176777916151717823266369 9132583437113788367449777)
                ·
                  refine ⟨6849437577835341275587333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9132583437113788367449777 6849437577835341275587333)
                  ·
                    refine ⟨1284269545844126489172625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6849437577835341275587333 1284269545844126489172625)
                    ·
                      rfl

theorem cell23_7503318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7503318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503318 prefixEnd_7503318 := by exact prefixLift 7503318
  have htrace : WordTrace (prefixWord ++ tailWord_7503318) baseStart_7503318 baseEnd_7503318 := by
    simpa [prefixWord, tailWord_7503318, baseEnd_7503318] using wordTrace_append hprefix tailTrace_7503318
  have hstable : (prefixWord ++ tailWord_7503318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503318).length < 2 ^ (prefixWord ++ tailWord_7503318).sum := by decide
  have hdescent : baseEnd_7503318 < baseStart_7503318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503325 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_7503325 : Nat := 118140960795 + 7503325 * 2 ^ 59
def prefixEnd_7503325 : Nat := 4983230072969 + 3 ^ 40 * 7503325 * 2
def baseEnd_7503325 : Nat := 3852812231896960940130343

theorem tailTrace_7503325 : CollatzResearch.WordTrace tailWord_7503325 prefixEnd_7503325 3852812231896960940130343 := by
  unfold tailWord_7503325
  simp only [CollatzResearch.WordTrace]
  refine ⟨273668745541742465732399429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182445830361161643821599619 273668745541742465732399429)
  ·
    refine ⟨51312889789076712324824893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273668745541742465732399429 51312889789076712324824893)
    ·
      refine ⟨19242333670903767121809335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51312889789076712324824893 19242333670903767121809335)
      ·
        refine ⟨28863500506355650682714003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19242333670903767121809335 28863500506355650682714003)
        ·
          refine ⟨43295250759533476024071005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28863500506355650682714003 43295250759533476024071005)
          ·
            refine ⟨16235719034825053509026627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43295250759533476024071005 16235719034825053509026627)
            ·
              refine ⟨24353578552237580263539941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16235719034825053509026627 24353578552237580263539941)
              ·
                refine ⟨4566295978544546299413739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24353578552237580263539941 4566295978544546299413739)
                ·
                  refine ⟨6849443967816819449120609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566295978544546299413739 6849443967816819449120609)
                  ·
                    refine ⟨5137082975862614586840457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849443967816819449120609 5137082975862614586840457)
                    ·
                      refine ⟨3852812231896960940130343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137082975862614586840457 3852812231896960940130343)
                      ·
                        rfl

theorem cell23_7503325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_7503325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503325 prefixEnd_7503325 := by exact prefixLift 7503325
  have htrace : WordTrace (prefixWord ++ tailWord_7503325) baseStart_7503325 baseEnd_7503325 := by
    simpa [prefixWord, tailWord_7503325, baseEnd_7503325] using wordTrace_append hprefix tailTrace_7503325
  have hstable : (prefixWord ++ tailWord_7503325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503325).length < 2 ^ (prefixWord ++ tailWord_7503325).sum := by decide
  have hdescent : baseEnd_7503325 < baseStart_7503325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503368 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_7503368 : Nat := 118140960795 + 7503368 * 2 ^ 59
def prefixEnd_7503368 : Nat := 4983230072969 + 3 ^ 40 * 7503368 * 2
def baseEnd_7503368 : Nat := 3852834311565104271892645

theorem tailTrace_7503368 : CollatzResearch.WordTrace tailWord_7503368 prefixEnd_7503368 3852834311565104271892645 := by
  unfold tailWord_7503368
  simp only [CollatzResearch.WordTrace]
  refine ⟨136835156940293342038107379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182446875920391122717476505 136835156940293342038107379)
  ·
    refine ⟨205252735410440013057161069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136835156940293342038107379 205252735410440013057161069)
    ·
      refine ⟨76969775778915004896435401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205252735410440013057161069 76969775778915004896435401)
      ·
        refine ⟨57727331834186253672326551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76969775778915004896435401 57727331834186253672326551)
        ·
          refine ⟨86590997751279380508489827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57727331834186253672326551 86590997751279380508489827)
          ·
            refine ⟨129886496626919070762734741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86590997751279380508489827 129886496626919070762734741)
            ·
              refine ⟨6088429529386831442003191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129886496626919070762734741 6088429529386831442003191)
              ·
                refine ⟨9132644294080247163004787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6088429529386831442003191 9132644294080247163004787)
                ·
                  refine ⟨13698966441120370744507181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132644294080247163004787 13698966441120370744507181)
                  ·
                    refine ⟨5137112415420139029190193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13698966441120370744507181 5137112415420139029190193)
                    ·
                      refine ⟨3852834311565104271892645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137112415420139029190193 3852834311565104271892645)
                      ·
                        rfl

theorem cell23_7503368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_7503368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503368 prefixEnd_7503368 := by exact prefixLift 7503368
  have htrace : WordTrace (prefixWord ++ tailWord_7503368) baseStart_7503368 baseEnd_7503368 := by
    simpa [prefixWord, tailWord_7503368, baseEnd_7503368] using wordTrace_append hprefix tailTrace_7503368
  have hstable : (prefixWord ++ tailWord_7503368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503368).length < 2 ^ (prefixWord ++ tailWord_7503368).sum := by decide
  have hdescent : baseEnd_7503368 < baseStart_7503368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503377 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_7503377 : Nat := 118140960795 + 7503377 * 2 ^ 59
def prefixEnd_7503377 : Nat := 4983230072969 + 3 ^ 40 * 7503377 * 2
def baseEnd_7503377 : Nat := 3852838932890994736680103

theorem tailTrace_7503377 : CollatzResearch.WordTrace tailWord_7503377 prefixEnd_7503377 3852838932890994736680103 := by
  unfold tailWord_7503377
  simp only [CollatzResearch.WordTrace]
  refine ⟨273670642137554078613292385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182447094758369385742194923 273670642137554078613292385)
  ·
    refine ⟨205252981603165558959969289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273670642137554078613292385 205252981603165558959969289)
    ·
      refine ⟨153939736202374169219976967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205252981603165558959969289 153939736202374169219976967)
      ·
        refine ⟨230909604303561253829965451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153939736202374169219976967 230909604303561253829965451)
        ·
          refine ⟨346364406455341880744948177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230909604303561253829965451 346364406455341880744948177)
          ·
            refine ⟨259773304841506410558711133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346364406455341880744948177 259773304841506410558711133)
            ·
              refine ⟨97414989315564903959516675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259773304841506410558711133 97414989315564903959516675)
              ·
                refine ⟨146122483973347355939275013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97414989315564903959516675 146122483973347355939275013)
                ·
                  refine ⟨27397965745002629238614065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146122483973347355939275013 27397965745002629238614065)
                  ·
                    refine ⟨20548474308751971928960549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27397965745002629238614065 20548474308751971928960549)
                    ·
                      refine ⟨3852838932890994736680103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20548474308751971928960549 3852838932890994736680103)
                      ·
                        rfl

theorem cell23_7503377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_7503377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503377 prefixEnd_7503377 := by exact prefixLift 7503377
  have htrace : WordTrace (prefixWord ++ tailWord_7503377) baseStart_7503377 baseEnd_7503377 := by
    simpa [prefixWord, tailWord_7503377, baseEnd_7503377] using wordTrace_append hprefix tailTrace_7503377
  have hstable : (prefixWord ++ tailWord_7503377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503377).length < 2 ^ (prefixWord ++ tailWord_7503377).sum := by decide
  have hdescent : baseEnd_7503377 < baseStart_7503377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503394 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_7503394 : Nat := 118140960795 + 7503394 * 2 ^ 59
def prefixEnd_7503394 : Nat := 4983230072969 + 3 ^ 40 * 7503394 * 2
def baseEnd_7503394 : Nat := 3852847662062121170167525

theorem tailTrace_7503394 : CollatzResearch.WordTrace tailWord_7503394 prefixEnd_7503394 3852847662062121170167525 := by
  unfold tailWord_7503394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68417815544623122629165309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182447508118994993677774157 68417815544623122629165309)
  ·
    refine ⟨25656680829233670985936991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68417815544623122629165309 25656680829233670985936991)
    ·
      refine ⟨38485021243850506478905487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25656680829233670985936991 38485021243850506478905487)
      ·
        refine ⟨57727531865775759718358231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38485021243850506478905487 57727531865775759718358231)
        ·
          refine ⟨86591297798663639577537347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57727531865775759718358231 86591297798663639577537347)
          ·
            refine ⟨129886946697995459366306021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86591297798663639577537347 129886946697995459366306021)
            ·
              refine ⟨24353802505874148631182379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129886946697995459366306021 24353802505874148631182379)
              ·
                refine ⟨36530703758811222946773569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353802505874148631182379 36530703758811222946773569)
                ·
                  refine ⟨27398027819108417210080177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36530703758811222946773569 27398027819108417210080177)
                  ·
                    refine ⟨20548520864331312907560133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27398027819108417210080177 20548520864331312907560133)
                    ·
                      refine ⟨3852847662062121170167525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20548520864331312907560133 3852847662062121170167525)
                      ·
                        rfl

theorem cell23_7503394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_7503394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503394 prefixEnd_7503394 := by exact prefixLift 7503394
  have htrace : WordTrace (prefixWord ++ tailWord_7503394) baseStart_7503394 baseEnd_7503394 := by
    simpa [prefixWord, tailWord_7503394, baseEnd_7503394] using wordTrace_append hprefix tailTrace_7503394
  have hstable : (prefixWord ++ tailWord_7503394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503394).length < 2 ^ (prefixWord ++ tailWord_7503394).sum := by decide
  have hdescent : baseEnd_7503394 < baseStart_7503394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503424 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2]
def baseStart_7503424 : Nat := 118140960795 + 7503424 * 2 ^ 59
def prefixEnd_7503424 : Nat := 4983230072969 + 3 ^ 40 * 7503424 * 2
def baseEnd_7503424 : Nat := 3852863066481756052792387

theorem tailTrace_7503424 : CollatzResearch.WordTrace tailWord_7503424 prefixEnd_7503424 3852863066481756052792387 := by
  unfold tailWord_7503424
  simp only [CollatzResearch.WordTrace]
  refine ⟨136836178184191902820126663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182448237578922537093502217 136836178184191902820126663)
  ·
    refine ⟨205254267276287854230189995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136836178184191902820126663 205254267276287854230189995)
    ·
      refine ⟨307881400914431781345284993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205254267276287854230189995 307881400914431781345284993)
      ·
        refine ⟨230911050685823836008963745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307881400914431781345284993 230911050685823836008963745)
        ·
          refine ⟨173183288014367877006722809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230911050685823836008963745 173183288014367877006722809)
          ·
            refine ⟨129887466010775907755042107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173183288014367877006722809 129887466010775907755042107)
            ·
              refine ⟨194831199016163861632563161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129887466010775907755042107 194831199016163861632563161)
              ·
                refine ⟨146123399262122896224422371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194831199016163861632563161 146123399262122896224422371)
                ·
                  refine ⟨219185098893184344336633557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146123399262122896224422371 219185098893184344336633557)
                  ·
                    refine ⟨5137150755309008070389849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219185098893184344336633557 5137150755309008070389849)
                    ·
                      refine ⟨3852863066481756052792387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137150755309008070389849 3852863066481756052792387)
                      ·
                        rfl

theorem cell23_7503424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_7503424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503424 prefixEnd_7503424 := by exact prefixLift 7503424
  have htrace : WordTrace (prefixWord ++ tailWord_7503424) baseStart_7503424 baseEnd_7503424 := by
    simpa [prefixWord, tailWord_7503424, baseEnd_7503424] using wordTrace_append hprefix tailTrace_7503424
  have hstable : (prefixWord ++ tailWord_7503424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503424).length < 2 ^ (prefixWord ++ tailWord_7503424).sum := by decide
  have hdescent : baseEnd_7503424 < baseStart_7503424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503434 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_7503434 : Nat := 118140960795 + 7503434 * 2 ^ 59
def prefixEnd_7503434 : Nat := 4983230072969 + 3 ^ 40 * 7503434 * 2
def baseEnd_7503434 : Nat := 1284289400429433671222447

theorem tailTrace_7503434 : CollatzResearch.WordTrace tailWord_7503434 prefixEnd_7503434 1284289400429433671222447 := by
  unfold tailWord_7503434
  simp only [CollatzResearch.WordTrace]
  refine ⟨68418180274586894337029339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182448480732231718232078237 68418180274586894337029339)
  ·
    refine ⟨102627270411880341505544009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68418180274586894337029339 102627270411880341505544009)
    ·
      refine ⟨76970452808910256129158007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102627270411880341505544009 76970452808910256129158007)
      ·
        refine ⟨115455679213365384193737011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76970452808910256129158007 115455679213365384193737011)
        ·
          refine ⟨173183518820048076290605517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115455679213365384193737011 173183518820048076290605517)
          ·
            refine ⟨64943819557518028608977069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173183518820048076290605517 64943819557518028608977069)
            ·
              refine ⟨24353932334069260728366401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64943819557518028608977069 24353932334069260728366401)
              ·
                refine ⟨18265449250551945546274801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24353932334069260728366401 18265449250551945546274801)
                ·
                  refine ⟨13699086937913959159706101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18265449250551945546274801 13699086937913959159706101)
                  ·
                    refine ⟨1284289400429433671222447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13699086937913959159706101 1284289400429433671222447)
                    ·
                      rfl

theorem cell23_7503434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_7503434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503434 prefixEnd_7503434 := by exact prefixLift 7503434
  have htrace : WordTrace (prefixWord ++ tailWord_7503434) baseStart_7503434 baseEnd_7503434 := by
    simpa [prefixWord, tailWord_7503434, baseEnd_7503434] using wordTrace_append hprefix tailTrace_7503434
  have hstable : (prefixWord ++ tailWord_7503434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503434).length < 2 ^ (prefixWord ++ tailWord_7503434).sum := by decide
  have hdescent : baseEnd_7503434 < baseStart_7503434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503444 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_7503444 : Nat := 118140960795 + 7503444 * 2 ^ 59
def prefixEnd_7503444 : Nat := 4983230072969 + 3 ^ 40 * 7503444 * 2
def baseEnd_7503444 : Nat := 3852873336094845974542295

theorem tailTrace_7503444 : CollatzResearch.WordTrace tailWord_7503444 prefixEnd_7503444 3852873336094845974542295 := by
  unfold tailWord_7503444
  simp only [CollatzResearch.WordTrace]
  refine ⟨136836542914155674527990693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182448723885540899370654257 136836542914155674527990693)
  ·
    refine ⟨25656851796404188973998255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136836542914155674527990693 25656851796404188973998255)
    ·
      refine ⟨38485277694606283460997383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25656851796404188973998255 38485277694606283460997383)
      ·
        refine ⟨57727916541909425191496075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38485277694606283460997383 57727916541909425191496075)
        ·
          refine ⟨86591874812864137787244113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57727916541909425191496075 86591874812864137787244113)
          ·
            refine ⟨64943906109648103340433085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86591874812864137787244113 64943906109648103340433085)
            ·
              refine ⟨24353964791118038752662407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64943906109648103340433085 24353964791118038752662407)
              ·
                refine ⟨36530947186677058128993611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24353964791118038752662407 36530947186677058128993611)
                ·
                  refine ⟨54796420780015587193490417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36530947186677058128993611 54796420780015587193490417)
                  ·
                    refine ⟨41097315585011690395117813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54796420780015587193490417 41097315585011690395117813)
                    ·
                      refine ⟨3852873336094845974542295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41097315585011690395117813 3852873336094845974542295)
                      ·
                        rfl

theorem cell23_7503444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_7503444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503444 prefixEnd_7503444 := by exact prefixLift 7503444
  have htrace : WordTrace (prefixWord ++ tailWord_7503444) baseStart_7503444 baseEnd_7503444 := by
    simpa [prefixWord, tailWord_7503444, baseEnd_7503444] using wordTrace_append hprefix tailTrace_7503444
  have hstable : (prefixWord ++ tailWord_7503444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503444).length < 2 ^ (prefixWord ++ tailWord_7503444).sum := by decide
  have hdescent : baseEnd_7503444 < baseStart_7503444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503507 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 11]
def baseStart_7503507 : Nat := 118140960795 + 7503507 * 2 ^ 59
def prefixEnd_7503507 : Nat := 4983230072969 + 3 ^ 40 * 7503507 * 2
def baseEnd_7503507 : Nat := 1284301895125359742684835

theorem tailTrace_7503507 : CollatzResearch.WordTrace tailWord_7503507 prefixEnd_7503507 1284301895125359742684835 := by
  unfold tailWord_7503507
  simp only [CollatzResearch.WordTrace]
  refine ⟨273675383627083110815524775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182450255751388740543683183 273675383627083110815524775)
  ·
    refine ⟨410513075440624666223287163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273675383627083110815524775 410513075440624666223287163)
    ·
      refine ⟨615769613160936999334930745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410513075440624666223287163 615769613160936999334930745)
      ·
        refine ⟨461827209870702749501198059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615769613160936999334930745 461827209870702749501198059)
        ·
          refine ⟨692740814806054124251797089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461827209870702749501198059 692740814806054124251797089)
          ·
            refine ⟨519555611104540593188847817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692740814806054124251797089 519555611104540593188847817)
            ·
              refine ⟨389666708328405444891635863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519555611104540593188847817 389666708328405444891635863)
              ·
                refine ⟨584500062492608167337453795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389666708328405444891635863 584500062492608167337453795)
                ·
                  refine ⟨876750093738912251006180693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584500062492608167337453795 876750093738912251006180693)
                  ·
                    refine ⟨1284301895125359742684835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 876750093738912251006180693 1284301895125359742684835)
                    ·
                      rfl

theorem cell23_7503507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_7503507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503507 prefixEnd_7503507 := by exact prefixLift 7503507
  have htrace : WordTrace (prefixWord ++ tailWord_7503507) baseStart_7503507 baseEnd_7503507 := by
    simpa [prefixWord, tailWord_7503507, baseEnd_7503507] using wordTrace_append hprefix tailTrace_7503507
  have hstable : (prefixWord ++ tailWord_7503507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503507).length < 2 ^ (prefixWord ++ tailWord_7503507).sum := by decide
  have hdescent : baseEnd_7503507 < baseStart_7503507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503522 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7503522 : Nat := 118140960795 + 7503522 * 2 ^ 59
def prefixEnd_7503522 : Nat := 4983230072969 + 3 ^ 40 * 7503522 * 2
def baseEnd_7503522 : Nat := 3852913387585896669366937

theorem tailTrace_7503522 : CollatzResearch.WordTrace tailWord_7503522 prefixEnd_7503522 3852913387585896669366937 := by
  unfold tailWord_7503522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68418982680507192094330205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182450620481352512251547213 68418982680507192094330205)
  ·
    refine ⟨25657118505190197035373827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68418982680507192094330205 25657118505190197035373827)
    ·
      refine ⟨38485677757785295553060741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25657118505190197035373827 38485677757785295553060741)
      ·
        refine ⟨7216064579584742916198889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38485677757785295553060741 7216064579584742916198889)
        ·
          refine ⟨5412048434688557187149167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216064579584742916198889 5412048434688557187149167)
          ·
            refine ⟨8118072652032835780723751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412048434688557187149167 8118072652032835780723751)
            ·
              refine ⟨12177108978049253671085627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118072652032835780723751 12177108978049253671085627)
              ·
                refine ⟨18265663467073880506628441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12177108978049253671085627 18265663467073880506628441)
                ·
                  refine ⟨13699247600305410379971331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18265663467073880506628441 13699247600305410379971331)
                  ·
                    refine ⟨20548871400458115569956997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13699247600305410379971331 20548871400458115569956997)
                    ·
                      refine ⟨3852913387585896669366937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20548871400458115569956997 3852913387585896669366937)
                      ·
                        rfl

theorem cell23_7503522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7503522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503522 prefixEnd_7503522 := by exact prefixLift 7503522
  have htrace : WordTrace (prefixWord ++ tailWord_7503522) baseStart_7503522 baseEnd_7503522 := by
    simpa [prefixWord, tailWord_7503522, baseEnd_7503522] using wordTrace_append hprefix tailTrace_7503522
  have hstable : (prefixWord ++ tailWord_7503522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503522).length < 2 ^ (prefixWord ++ tailWord_7503522).sum := by decide
  have hdescent : baseEnd_7503522 < baseStart_7503522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503565 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7503565 : Nat := 118140960795 + 7503565 * 2 ^ 59
def prefixEnd_7503565 : Nat := 4983230072969 + 3 ^ 40 * 7503565 * 2
def baseEnd_7503565 : Nat := 3852935467254040001129239

theorem tailTrace_7503565 : CollatzResearch.WordTrace tailWord_7503565 prefixEnd_7503565 3852935467254040001129239 := by
  unfold tailWord_7503565
  simp only [CollatzResearch.WordTrace]
  refine ⟨273677499060872986721136149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182451666040581991147424099 273677499060872986721136149)
  ·
    refine ⟨12828632768478421252553257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273677499060872986721136149 12828632768478421252553257)
    ·
      refine ⟨9621474576358815939414943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828632768478421252553257 9621474576358815939414943)
      ·
        refine ⟨14432211864538223909122415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621474576358815939414943 14432211864538223909122415)
        ·
          refine ⟨21648317796807335863683623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14432211864538223909122415 21648317796807335863683623)
          ·
            refine ⟨32472476695211003795525435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21648317796807335863683623 32472476695211003795525435)
            ·
              refine ⟨48708715042816505693288153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32472476695211003795525435 48708715042816505693288153)
              ·
                refine ⟨36531536282112379269966115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48708715042816505693288153 36531536282112379269966115)
                ·
                  refine ⟨54797304423168568904949173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36531536282112379269966115 54797304423168568904949173)
                  ·
                    refine ⟨5137247289672053334838985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54797304423168568904949173 5137247289672053334838985)
                    ·
                      refine ⟨3852935467254040001129239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137247289672053334838985 3852935467254040001129239)
                      ·
                        rfl

theorem cell23_7503565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7503565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503565 prefixEnd_7503565 := by exact prefixLift 7503565
  have htrace : WordTrace (prefixWord ++ tailWord_7503565) baseStart_7503565 baseEnd_7503565 := by
    simpa [prefixWord, tailWord_7503565, baseEnd_7503565] using wordTrace_append hprefix tailTrace_7503565
  have hstable : (prefixWord ++ tailWord_7503565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503565).length < 2 ^ (prefixWord ++ tailWord_7503565).sum := by decide
  have hdescent : baseEnd_7503565 < baseStart_7503565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503578 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_7503578 : Nat := 118140960795 + 7503578 * 2 ^ 59
def prefixEnd_7503578 : Nat := 4983230072969 + 3 ^ 40 * 7503578 * 2
def baseEnd_7503578 : Nat := 3852942142502548450266679

theorem tailTrace_7503578 : CollatzResearch.WordTrace tailWord_7503578 prefixEnd_7503578 3852942142502548450266679 := by
  unfold tailWord_7503578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68419493302456472485339847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182451982139883926627572925 68419493302456472485339847)
  ·
    refine ⟨102629239953684708728009771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68419493302456472485339847 102629239953684708728009771)
    ·
      refine ⟨153943859930527063092014657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102629239953684708728009771 153943859930527063092014657)
      ·
        refine ⟨115457894947895297319010993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153943859930527063092014657 115457894947895297319010993)
        ·
          refine ⟨86593421210921472989258245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115457894947895297319010993 86593421210921472989258245)
          ·
            refine ⟨16236266477047776185485921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86593421210921472989258245 16236266477047776185485921)
            ·
              refine ⟨12177199857785832139114441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16236266477047776185485921 12177199857785832139114441)
              ·
                refine ⟨9132899893339374104335831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12177199857785832139114441 9132899893339374104335831)
                ·
                  refine ⟨13699349840009061156503747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132899893339374104335831 13699349840009061156503747)
                  ·
                    refine ⟨20549024760013591734755621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13699349840009061156503747 20549024760013591734755621)
                    ·
                      refine ⟨3852942142502548450266679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20549024760013591734755621 3852942142502548450266679)
                      ·
                        rfl

theorem cell23_7503578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_7503578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503578 prefixEnd_7503578 := by exact prefixLift 7503578
  have htrace : WordTrace (prefixWord ++ tailWord_7503578) baseStart_7503578 baseEnd_7503578 := by
    simpa [prefixWord, tailWord_7503578, baseEnd_7503578] using wordTrace_append hprefix tailTrace_7503578
  have hstable : (prefixWord ++ tailWord_7503578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503578).length < 2 ^ (prefixWord ++ tailWord_7503578).sum := by decide
  have hdescent : baseEnd_7503578 < baseStart_7503578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503598 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_7503598 : Nat := 118140960795 + 7503598 * 2 ^ 59
def prefixEnd_7503598 : Nat := 4983230072969 + 3 ^ 40 * 7503598 * 2
def baseEnd_7503598 : Nat := 3852952412115638372016587

theorem tailTrace_7503598 : CollatzResearch.WordTrace tailWord_7503598 prefixEnd_7503598 3852952412115638372016587 := by
  unfold tailWord_7503598
  simp only [CollatzResearch.WordTrace]
  refine ⟨34209837833719179169635931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182452468446502288904724965 34209837833719179169635931)
  ·
    refine ⟨51314756750578768754453897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34209837833719179169635931 51314756750578768754453897)
    ·
      refine ⟨38486067562934076565840423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51314756750578768754453897 38486067562934076565840423)
      ·
        refine ⟨57729101344401114848760635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38486067562934076565840423 57729101344401114848760635)
        ·
          refine ⟨86593652016601672273140953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57729101344401114848760635 86593652016601672273140953)
          ·
            refine ⟨64945239012451254204855715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86593652016601672273140953 64945239012451254204855715)
            ·
              refine ⟨97417858518676881307283573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64945239012451254204855715 97417858518676881307283573)
              ·
                refine ⟨9132924236125957622557835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97417858518676881307283573 9132924236125957622557835)
                ·
                  refine ⟨13699386354188936433836753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9132924236125957622557835 13699386354188936433836753)
                  ·
                    refine ⟨10274539765641702325377565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13699386354188936433836753 10274539765641702325377565)
                    ·
                      refine ⟨3852952412115638372016587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10274539765641702325377565 3852952412115638372016587)
                      ·
                        rfl

theorem cell23_7503598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_7503598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503598 prefixEnd_7503598 := by exact prefixLift 7503598
  have htrace : WordTrace (prefixWord ++ tailWord_7503598) baseStart_7503598 baseEnd_7503598 := by
    simpa [prefixWord, tailWord_7503598, baseEnd_7503598] using wordTrace_append hprefix tailTrace_7503598
  have hstable : (prefixWord ++ tailWord_7503598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503598).length < 2 ^ (prefixWord ++ tailWord_7503598).sum := by decide
  have hdescent : baseEnd_7503598 < baseStart_7503598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503621 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_7503621 : Nat := 118140960795 + 7503621 * 2 ^ 59
def prefixEnd_7503621 : Nat := 4983230072969 + 3 ^ 40 * 7503621 * 2
def baseEnd_7503621 : Nat := 3852964222170691782028981

theorem tailTrace_7503621 : CollatzResearch.WordTrace tailWord_7503621 prefixEnd_7503621 3852964222170691782028981 := by
  unfold tailWord_7503621
  simp only [CollatzResearch.WordTrace]
  refine ⟨273679541548670108285174717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182453027699113405523449811 273679541548670108285174717)
  ·
    refine ⟨102629828080751290606940519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273679541548670108285174717 102629828080751290606940519)
    ·
      refine ⟨153944742121126935910410779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102629828080751290606940519 153944742121126935910410779)
      ·
        refine ⟨230917113181690403865616169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153944742121126935910410779 230917113181690403865616169)
        ·
          refine ⟨173187834886267802899212127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230917113181690403865616169 173187834886267802899212127)
          ·
            refine ⟨259781752329401704348818191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173187834886267802899212127 259781752329401704348818191)
            ·
              refine ⟨389672628494102556523227287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259781752329401704348818191 389672628494102556523227287)
              ·
                refine ⟨584508942741153834784840931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389672628494102556523227287 584508942741153834784840931)
                ·
                  refine ⟨876763414111730752177261397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584508942741153834784840931 876763414111730752177261397)
                  ·
                    refine ⟨5137285629560922376038641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 876763414111730752177261397 5137285629560922376038641)
                    ·
                      refine ⟨3852964222170691782028981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137285629560922376038641 3852964222170691782028981)
                      ·
                        rfl

theorem cell23_7503621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_7503621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503621 prefixEnd_7503621 := by exact prefixLift 7503621
  have htrace : WordTrace (prefixWord ++ tailWord_7503621) baseStart_7503621 baseEnd_7503621 := by
    simpa [prefixWord, tailWord_7503621, baseEnd_7503621] using wordTrace_append hprefix tailTrace_7503621
  have hstable : (prefixWord ++ tailWord_7503621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503621).length < 2 ^ (prefixWord ++ tailWord_7503621).sum := by decide
  have hdescent : baseEnd_7503621 < baseStart_7503621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503629 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7503629 : Nat := 118140960795 + 7503629 * 2 ^ 59
def prefixEnd_7503629 : Nat := 4983230072969 + 3 ^ 40 * 7503629 * 2
def baseEnd_7503629 : Nat := 3852968330015927750728945

theorem tailTrace_7503629 : CollatzResearch.WordTrace tailWord_7503629 prefixEnd_7503629 3852968330015927750728945 := by
  unfold tailWord_7503629
  simp only [CollatzResearch.WordTrace]
  refine ⟨273679833332641125651465941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182453222221760750434310627 273679833332641125651465941)
  ·
    refine ⟨6414371093733776382456233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 273679833332641125651465941 6414371093733776382456233)
    ·
      refine ⟨4810778320300332286842175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6414371093733776382456233 4810778320300332286842175)
      ·
        refine ⟨7216167480450498430263263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810778320300332286842175 7216167480450498430263263)
        ·
          refine ⟨10824251220675747645394895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216167480450498430263263 10824251220675747645394895)
          ·
            refine ⟨16236376831013621468092343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824251220675747645394895 16236376831013621468092343)
            ·
              refine ⟨24354565246520432202138515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236376831013621468092343 24354565246520432202138515)
              ·
                refine ⟨36531847869780648303207773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24354565246520432202138515 36531847869780648303207773)
                ·
                  refine ⟨13699442951167743113702915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36531847869780648303207773 13699442951167743113702915)
                  ·
                    refine ⟨20549164426751614670554373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13699442951167743113702915 20549164426751614670554373)
                    ·
                      refine ⟨3852968330015927750728945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20549164426751614670554373 3852968330015927750728945)
                      ·
                        rfl

theorem cell23_7503629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7503629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503629 prefixEnd_7503629 := by exact prefixLift 7503629
  have htrace : WordTrace (prefixWord ++ tailWord_7503629) baseStart_7503629 baseEnd_7503629 := by
    simpa [prefixWord, tailWord_7503629, baseEnd_7503629] using wordTrace_append hprefix tailTrace_7503629
  have hstable : (prefixWord ++ tailWord_7503629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503629).length < 2 ^ (prefixWord ++ tailWord_7503629).sum := by decide
  have hdescent : baseEnd_7503629 < baseStart_7503629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503664 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_7503664 : Nat := 118140960795 + 7503664 * 2 ^ 59
def prefixEnd_7503664 : Nat := 4983230072969 + 3 ^ 40 * 7503664 * 2
def baseEnd_7503664 : Nat := 3852986301838835113791283

theorem tailTrace_7503664 : CollatzResearch.WordTrace tailWord_7503664 prefixEnd_7503664 3852986301838835113791283 := by
  unfold tailWord_7503664
  simp only [CollatzResearch.WordTrace]
  refine ⟨136840554943757163314495023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182454073258342884419326697 136840554943757163314495023)
  ·
    refine ⟨205260832415635744971742535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136840554943757163314495023 205260832415635744971742535)
    ·
      refine ⟨307891248623453617457613803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205260832415635744971742535 307891248623453617457613803)
      ·
        refine ⟨461836872935180426186420705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307891248623453617457613803 461836872935180426186420705)
        ·
          refine ⟨346377654701385319639815529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461836872935180426186420705 346377654701385319639815529)
          ·
            refine ⟨259783241026038989729861647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346377654701385319639815529 259783241026038989729861647)
            ·
              refine ⟨389674861539058484594792471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259783241026038989729861647 389674861539058484594792471)
              ·
                refine ⟨584512292308587726892188707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389674861539058484594792471 584512292308587726892188707)
                ·
                  refine ⟨876768438462881590338283061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584512292308587726892188707 876768438462881590338283061)
                  ·
                    refine ⟨82197041105895149094214037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 876768438462881590338283061 82197041105895149094214037)
                    ·
                      refine ⟨3852986301838835113791283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82197041105895149094214037 3852986301838835113791283)
                      ·
                        rfl

theorem cell23_7503664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_7503664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503664 prefixEnd_7503664 := by exact prefixLift 7503664
  have htrace : WordTrace (prefixWord ++ tailWord_7503664) baseStart_7503664 baseEnd_7503664 := by
    simpa [prefixWord, tailWord_7503664, baseEnd_7503664] using wordTrace_append hprefix tailTrace_7503664
  have hstable : (prefixWord ++ tailWord_7503664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503664).length < 2 ^ (prefixWord ++ tailWord_7503664).sum := by decide
  have hdescent : baseEnd_7503664 < baseStart_7503664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503668 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7503668 : Nat := 118140960795 + 7503668 * 2 ^ 59
def prefixEnd_7503668 : Nat := 4983230072969 + 3 ^ 40 * 7503668 * 2
def baseEnd_7503668 : Nat := 3852988355761453098141265

theorem tailTrace_7503668 : CollatzResearch.WordTrace tailWord_7503668 prefixEnd_7503668 3852988355761453098141265 := by
  unfold tailWord_7503668
  simp only [CollatzResearch.WordTrace]
  refine ⟨136840627889749917656067829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182454170519666556874757105 136840627889749917656067829)
  ·
    refine ⟨12828808864664054780256359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136840627889749917656067829 12828808864664054780256359)
    ·
      refine ⟨19243213296996082170384539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828808864664054780256359 19243213296996082170384539)
      ·
        refine ⟨28864819945494123255576809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243213296996082170384539 28864819945494123255576809)
        ·
          refine ⟨21648614959120592441682607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28864819945494123255576809 21648614959120592441682607)
          ·
            refine ⟨32472922438680888662523911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21648614959120592441682607 32472922438680888662523911)
            ·
              refine ⟨48709383658021332993785867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32472922438680888662523911 48709383658021332993785867)
              ·
                refine ⟨73064075487031999490678801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48709383658021332993785867 73064075487031999490678801)
                ·
                  refine ⟨54798056615273999618009101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73064075487031999490678801 54798056615273999618009101)
                  ·
                    refine ⟨20549271230727749856753413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54798056615273999618009101 20549271230727749856753413)
                    ·
                      refine ⟨3852988355761453098141265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20549271230727749856753413 3852988355761453098141265)
                      ·
                        rfl

theorem cell23_7503668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7503668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503668 prefixEnd_7503668 := by exact prefixLift 7503668
  have htrace : WordTrace (prefixWord ++ tailWord_7503668) baseStart_7503668 baseEnd_7503668 := by
    simpa [prefixWord, tailWord_7503668, baseEnd_7503668] using wordTrace_append hprefix tailTrace_7503668
  have hstable : (prefixWord ++ tailWord_7503668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503668).length < 2 ^ (prefixWord ++ tailWord_7503668).sum := by decide
  have hdescent : baseEnd_7503668 < baseStart_7503668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503678 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_7503678 : Nat := 118140960795 + 7503678 * 2 ^ 59
def prefixEnd_7503678 : Nat := 4983230072969 + 3 ^ 40 * 7503678 * 2
def baseEnd_7503678 : Nat := 1284331163522666019672073

theorem tailTrace_7503678 : CollatzResearch.WordTrace tailWord_7503678 prefixEnd_7503678 1284331163522666019672073 := by
  unfold tailWord_7503678
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210202563682950877499961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182454413672975738013333125 34210202563682950877499961)
  ·
    refine ⟨25657651922762213158124971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34210202563682950877499961 25657651922762213158124971)
    ·
      refine ⟨38486477884143319737187457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25657651922762213158124971 38486477884143319737187457)
      ·
        refine ⟨28864858413107489802890593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38486477884143319737187457 28864858413107489802890593)
        ·
          refine ⟨21648643809830617352167945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28864858413107489802890593 21648643809830617352167945)
          ·
            refine ⟨16236482857372963014125959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21648643809830617352167945 16236482857372963014125959)
            ·
              refine ⟨24354724286059444521188939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236482857372963014125959 24354724286059444521188939)
              ·
                refine ⟨36532086429089166781783409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24354724286059444521188939 36532086429089166781783409)
                ·
                  refine ⟨27399064821816875086337557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36532086429089166781783409 27399064821816875086337557)
                  ·
                    refine ⟨1284331163522666019672073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27399064821816875086337557 1284331163522666019672073)
                    ·
                      rfl

theorem cell23_7503678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_7503678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503678 prefixEnd_7503678 := by exact prefixLift 7503678
  have htrace : WordTrace (prefixWord ++ tailWord_7503678) baseStart_7503678 baseEnd_7503678 := by
    simpa [prefixWord, tailWord_7503678, baseEnd_7503678] using wordTrace_append hprefix tailTrace_7503678
  have hstable : (prefixWord ++ tailWord_7503678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503678).length < 2 ^ (prefixWord ++ tailWord_7503678).sum := by decide
  have hdescent : baseEnd_7503678 < baseStart_7503678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503685 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_7503685 : Nat := 118140960795 + 7503685 * 2 ^ 59
def prefixEnd_7503685 : Nat := 4983230072969 + 3 ^ 40 * 7503685 * 2
def baseEnd_7503685 : Nat := 3852997084932579531628687

theorem tailTrace_7503685 : CollatzResearch.WordTrace tailWord_7503685 prefixEnd_7503685 3852997084932579531628687 := by
  unfold tailWord_7503685
  simp only [CollatzResearch.WordTrace]
  refine ⟨273681875820438247215504509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182454583880292164810336339 273681875820438247215504509)
  ·
    refine ⟨102630703432664342705814191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273681875820438247215504509 102630703432664342705814191)
    ·
      refine ⟨153946055148996514058721287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102630703432664342705814191 153946055148996514058721287)
      ·
        refine ⟨230919082723494771088081931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153946055148996514058721287 230919082723494771088081931)
        ·
          refine ⟨346378624085242156632122897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230919082723494771088081931 346378624085242156632122897)
          ·
            refine ⟨259783968063931617474092173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346378624085242156632122897 259783968063931617474092173)
            ·
              refine ⟨97418988023974356552784565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259783968063931617474092173 97418988023974356552784565)
              ·
                refine ⟨9133030127247595926823553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97418988023974356552784565 9133030127247595926823553)
                ·
                  refine ⟨6849772595435696945117665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133030127247595926823553 6849772595435696945117665)
                  ·
                    refine ⟨5137329446576772708838249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849772595435696945117665 5137329446576772708838249)
                    ·
                      refine ⟨3852997084932579531628687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137329446576772708838249 3852997084932579531628687)
                      ·
                        rfl

theorem cell23_7503685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_7503685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503685 prefixEnd_7503685 := by exact prefixLift 7503685
  have htrace : WordTrace (prefixWord ++ tailWord_7503685) baseStart_7503685 baseEnd_7503685 := by
    simpa [prefixWord, tailWord_7503685, baseEnd_7503685] using wordTrace_append hprefix tailTrace_7503685
  have hstable : (prefixWord ++ tailWord_7503685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503685).length < 2 ^ (prefixWord ++ tailWord_7503685).sum := by decide
  have hdescent : baseEnd_7503685 < baseStart_7503685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503721 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_7503721 : Nat := 118140960795 + 7503721 * 2 ^ 59
def prefixEnd_7503721 : Nat := 4983230072969 + 3 ^ 40 * 7503721 * 2
def baseEnd_7503721 : Nat := 1284338523412047130259507

theorem tailTrace_7503721 : CollatzResearch.WordTrace tailWord_7503721 prefixEnd_7503721 1284338523412047130259507 := by
  unfold tailWord_7503721
  simp only [CollatzResearch.WordTrace]
  refine ⟨273683188848307825363815017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182455459232205216909210011 273683188848307825363815017)
  ·
    refine ⟨205262391636230869022861263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273683188848307825363815017 205262391636230869022861263)
    ·
      refine ⟨307893587454346303534291895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205262391636230869022861263 307893587454346303534291895)
      ·
        refine ⟨461840381181519455301437843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307893587454346303534291895 461840381181519455301437843)
        ·
          refine ⟨692760571772279182952156765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461840381181519455301437843 692760571772279182952156765)
          ·
            refine ⟨259785214414604693607058787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 692760571772279182952156765 259785214414604693607058787)
            ·
              refine ⟨389677821621907040410588181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259785214414604693607058787 389677821621907040410588181)
              ·
                refine ⟨18266147888526892519246321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 389677821621907040410588181 18266147888526892519246321)
                ·
                  refine ⟨13699610916395169389434741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18266147888526892519246321 13699610916395169389434741)
                  ·
                    refine ⟨1284338523412047130259507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13699610916395169389434741 1284338523412047130259507)
                    ·
                      rfl

theorem cell23_7503721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_7503721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503721 prefixEnd_7503721 := by exact prefixLift 7503721
  have htrace : WordTrace (prefixWord ++ tailWord_7503721) baseStart_7503721 baseEnd_7503721 := by
    simpa [prefixWord, tailWord_7503721, baseEnd_7503721] using wordTrace_append hprefix tailTrace_7503721
  have hstable : (prefixWord ++ tailWord_7503721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503721).length < 2 ^ (prefixWord ++ tailWord_7503721).sum := by decide
  have hdescent : baseEnd_7503721 < baseStart_7503721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503775 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7503775 : Nat := 118140960795 + 7503775 * 2 ^ 59
def prefixEnd_7503775 : Nat := 4983230072969 + 3 ^ 40 * 7503775 * 2
def baseEnd_7503775 : Nat := 3853043298191484179503273

theorem tailTrace_7503775 : CollatzResearch.WordTrace tailWord_7503775 prefixEnd_7503775 3853043298191484179503273 := by
  unfold tailWord_7503775
  simp only [CollatzResearch.WordTrace]
  refine ⟨273685158390112192586280779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182456772260074795057520519 273685158390112192586280779)
  ·
    refine ⟨410527737585168288879421169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273685158390112192586280779 410527737585168288879421169)
    ·
      refine ⟨307895803188876216659565877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410527737585168288879421169 307895803188876216659565877)
      ·
        refine ⟨28865231548957145311834301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 307895803188876216659565877 28865231548957145311834301)
        ·
          refine ⟨10824461830858929491937863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28865231548957145311834301 10824461830858929491937863)
          ·
            refine ⟨16236692746288394237906795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824461830858929491937863 16236692746288394237906795)
            ·
              refine ⟨24355039119432591356860193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236692746288394237906795 24355039119432591356860193)
              ·
                refine ⟨18266279339574443517645145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24355039119432591356860193 18266279339574443517645145)
                ·
                  refine ⟨13699709504680832638233859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18266279339574443517645145 13699709504680832638233859)
                  ·
                    refine ⟨20549564257021248957350789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13699709504680832638233859 20549564257021248957350789)
                    ·
                      refine ⟨3853043298191484179503273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20549564257021248957350789 3853043298191484179503273)
                      ·
                        rfl

theorem cell23_7503775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7503775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503775 prefixEnd_7503775 := by exact prefixLift 7503775
  have htrace : WordTrace (prefixWord ++ tailWord_7503775) baseStart_7503775 baseEnd_7503775 := by
    simpa [prefixWord, tailWord_7503775, baseEnd_7503775] using wordTrace_append hprefix tailTrace_7503775
  have hstable : (prefixWord ++ tailWord_7503775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503775).length < 2 ^ (prefixWord ++ tailWord_7503775).sum := by decide
  have hdescent : baseEnd_7503775 < baseStart_7503775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503871 : List Nat := [1, 1, 2, 2, 1, 2, 1, 13]
def baseStart_7503871 : Nat := 118140960795 + 7503871 * 2 ^ 59
def prefixEnd_7503871 : Nat := 4983230072969 + 3 ^ 40 * 7503871 * 2
def baseEnd_7503871 : Nat := 142707133049419103848253

theorem tailTrace_7503871 : CollatzResearch.WordTrace tailWord_7503871 prefixEnd_7503871 142707133049419103848253 := by
  unfold tailWord_7503871
  simp only [CollatzResearch.WordTrace]
  refine ⟨273688659797764400981775467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182459106531842933987850311 273688659797764400981775467)
  ·
    refine ⟨410532989696646601472663201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273688659797764400981775467 410532989696646601472663201)
    ·
      refine ⟨307899742272484951104497401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410532989696646601472663201 307899742272484951104497401)
      ·
        refine ⟨230924806704363713328373051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307899742272484951104497401 230924806704363713328373051)
        ·
          refine ⟨346387210056545569992559577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230924806704363713328373051 346387210056545569992559577)
          ·
            refine ⟨259790407542409177494419683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346387210056545569992559577 259790407542409177494419683)
            ·
              refine ⟨389685611313613766241629525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259790407542409177494419683 389685611313613766241629525)
              ·
                refine ⟨142707133049419103848253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 389685611313613766241629525 142707133049419103848253)
                ·
                  rfl

theorem cell23_7503871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 13].length) (baseStart_7503871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503871 prefixEnd_7503871 := by exact prefixLift 7503871
  have htrace : WordTrace (prefixWord ++ tailWord_7503871) baseStart_7503871 baseEnd_7503871 := by
    simpa [prefixWord, tailWord_7503871, baseEnd_7503871] using wordTrace_append hprefix tailTrace_7503871
  have hstable : (prefixWord ++ tailWord_7503871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503871).length < 2 ^ (prefixWord ++ tailWord_7503871).sum := by decide
  have hdescent : baseEnd_7503871 < baseStart_7503871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503882 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_7503882 : Nat := 118140960795 + 7503882 * 2 ^ 59
def prefixEnd_7503882 : Nat := 4983230072969 + 3 ^ 40 * 7503882 * 2
def baseEnd_7503882 : Nat := 3853098240621515260865281

theorem tailTrace_7503882 : CollatzResearch.WordTrace tailWord_7503882 prefixEnd_7503882 3853098240621515260865281 := by
  unfold tailWord_7503882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68422265250181137465106475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182459374000483033240283933 68422265250181137465106475)
  ·
    refine ⟨102633397875271706197659713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68422265250181137465106475 102633397875271706197659713)
    ·
      refine ⟨76975048406453779648244785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102633397875271706197659713 76975048406453779648244785)
      ·
        refine ⟨57731286304840334736183589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76975048406453779648244785 57731286304840334736183589)
        ·
          refine ⟨10824616182157562763034423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57731286304840334736183589 10824616182157562763034423)
          ·
            refine ⟨16236924273236344144551635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824616182157562763034423 16236924273236344144551635)
            ·
              refine ⟨24355386409854516216827453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236924273236344144551635 24355386409854516216827453)
              ·
                refine ⟨9133269903695443581310295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24355386409854516216827453 9133269903695443581310295)
                ·
                  refine ⟨13699904855543165371965443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9133269903695443581310295 13699904855543165371965443)
                  ·
                    refine ⟨20549857283314748057948165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13699904855543165371965443 20549857283314748057948165)
                    ·
                      refine ⟨3853098240621515260865281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20549857283314748057948165 3853098240621515260865281)
                      ·
                        rfl

theorem cell23_7503882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_7503882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503882 prefixEnd_7503882 := by exact prefixLift 7503882
  have htrace : WordTrace (prefixWord ++ tailWord_7503882) baseStart_7503882 baseEnd_7503882 := by
    simpa [prefixWord, tailWord_7503882, baseEnd_7503882] using wordTrace_append hprefix tailTrace_7503882
  have hstable : (prefixWord ++ tailWord_7503882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503882).length < 2 ^ (prefixWord ++ tailWord_7503882).sum := by decide
  have hdescent : baseEnd_7503882 < baseStart_7503882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503912 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7503912 : Nat := 118140960795 + 7503912 * 2 ^ 59
def prefixEnd_7503912 : Nat := 4983230072969 + 3 ^ 40 * 7503912 * 2
def baseEnd_7503912 : Nat := 3853113645041150143490143

theorem tailTrace_7503912 : CollatzResearch.WordTrace tailWord_7503912 prefixEnd_7503912 3853113645041150143490143 := by
  unfold tailWord_7503912
  simp only [CollatzResearch.WordTrace]
  refine ⟨136845077595307932492008995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182460103460410576656011993 136845077595307932492008995)
  ·
    refine ⟨205267616392961898738013493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136845077595307932492008995 205267616392961898738013493)
    ·
      refine ⟨19243839036840178006688765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205267616392961898738013493 19243839036840178006688765)
      ·
        refine ⟨7216439638815066752508287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19243839036840178006688765 7216439638815066752508287)
        ·
          refine ⟨10824659458222600128762431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216439638815066752508287 10824659458222600128762431)
          ·
            refine ⟨16236989187333900193143647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824659458222600128762431 16236989187333900193143647)
            ·
              refine ⟨24355483781000850289715471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16236989187333900193143647 24355483781000850289715471)
              ·
                refine ⟨36533225671501275434573207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24355483781000850289715471 36533225671501275434573207)
                ·
                  refine ⟨54799838507251913151859811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36533225671501275434573207 54799838507251913151859811)
                  ·
                    refine ⟨82199757760877869727789717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54799838507251913151859811 82199757760877869727789717)
                    ·
                      refine ⟨3853113645041150143490143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82199757760877869727789717 3853113645041150143490143)
                      ·
                        rfl

theorem cell23_7503912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7503912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503912 prefixEnd_7503912 := by exact prefixLift 7503912
  have htrace : WordTrace (prefixWord ++ tailWord_7503912) baseStart_7503912 baseEnd_7503912 := by
    simpa [prefixWord, tailWord_7503912, baseEnd_7503912] using wordTrace_append hprefix tailTrace_7503912
  have hstable : (prefixWord ++ tailWord_7503912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503912).length < 2 ^ (prefixWord ++ tailWord_7503912).sum := by decide
  have hdescent : baseEnd_7503912 < baseStart_7503912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503948 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_7503948 : Nat := 118140960795 + 7503948 * 2 ^ 59
def prefixEnd_7503948 : Nat := 4983230072969 + 3 ^ 40 * 7503948 * 2
def baseEnd_7503948 : Nat := 1284377376781570667546659

theorem tailTrace_7503948 : CollatzResearch.WordTrace tailWord_7503948 prefixEnd_7503948 1284377376781570667546659 := by
  unfold tailWord_7503948
  simp only [CollatzResearch.WordTrace]
  refine ⟨136845734109242721566164249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182460978812323628754885665 136845734109242721566164249)
  ·
    refine ⟨102634300581932041174623187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136845734109242721566164249 102634300581932041174623187)
    ·
      refine ⟨153951450872898061761934781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102634300581932041174623187 153951450872898061761934781)
      ·
        refine ⟨57731794077336773160725543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153951450872898061761934781 57731794077336773160725543)
        ·
          refine ⟨86597691116005159741088315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57731794077336773160725543 86597691116005159741088315)
          ·
            refine ⟨129896536674007739611632473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86597691116005159741088315 129896536674007739611632473)
            ·
              refine ⟨97422402505505804708724355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129896536674007739611632473 97422402505505804708724355)
              ·
                refine ⟨146133603758258707063086533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97422402505505804708724355 146133603758258707063086533)
                ·
                  refine ⟨27400050704673507574328725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146133603758258707063086533 27400050704673507574328725)
                  ·
                    refine ⟨1284377376781570667546659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27400050704673507574328725 1284377376781570667546659)
                    ·
                      rfl

theorem cell23_7503948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_7503948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503948 prefixEnd_7503948 := by exact prefixLift 7503948
  have htrace : WordTrace (prefixWord ++ tailWord_7503948) baseStart_7503948 baseEnd_7503948 := by
    simpa [prefixWord, tailWord_7503948, baseEnd_7503948] using wordTrace_append hprefix tailTrace_7503948
  have hstable : (prefixWord ++ tailWord_7503948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503948).length < 2 ^ (prefixWord ++ tailWord_7503948).sum := by decide
  have hdescent : baseEnd_7503948 < baseStart_7503948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7503949 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7503949 : Nat := 118140960795 + 7503949 * 2 ^ 59
def prefixEnd_7503949 : Nat := 4983230072969 + 3 ^ 40 * 7503949 * 2
def baseEnd_7503949 : Nat := 3853132643825366498727473

theorem tailTrace_7503949 : CollatzResearch.WordTrace tailWord_7503949 prefixEnd_7503949 3853132643825366498727473 := by
  unfold tailWord_7503949
  simp only [CollatzResearch.WordTrace]
  refine ⟨273691504691481820303114901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182461003127654546868743267 273691504691481820303114901)
  ·
    refine ⟨12829289282413210326708511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273691504691481820303114901 12829289282413210326708511)
    ·
      refine ⟨19243933923619815490062767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829289282413210326708511 19243933923619815490062767)
      ·
        refine ⟨28865900885429723235094151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243933923619815490062767 28865900885429723235094151)
        ·
          refine ⟨43298851328144584852641227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28865900885429723235094151 43298851328144584852641227)
          ·
            refine ⟨64948276992216877278961841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43298851328144584852641227 64948276992216877278961841)
            ·
              refine ⟨48711207744162657959221381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64948276992216877278961841 48711207744162657959221381)
              ·
                refine ⟨9133351452030498367354009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48711207744162657959221381 9133351452030498367354009)
                ·
                  refine ⟨6850013589022873775515507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133351452030498367354009 6850013589022873775515507)
                  ·
                    refine ⟨10275020383534310663273261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850013589022873775515507 10275020383534310663273261)
                    ·
                      refine ⟨3853132643825366498727473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275020383534310663273261 3853132643825366498727473)
                      ·
                        rfl

theorem cell23_7503949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7503949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7503949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7503949 prefixEnd_7503949 := by exact prefixLift 7503949
  have htrace : WordTrace (prefixWord ++ tailWord_7503949) baseStart_7503949 baseEnd_7503949 := by
    simpa [prefixWord, tailWord_7503949, baseEnd_7503949] using wordTrace_append hprefix tailTrace_7503949
  have hstable : (prefixWord ++ tailWord_7503949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7503949).length < 2 ^ (prefixWord ++ tailWord_7503949).sum := by decide
  have hdescent : baseEnd_7503949 < baseStart_7503949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7503949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504048 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_7504048 : Nat := 118140960795 + 7504048 * 2 ^ 59
def prefixEnd_7504048 : Nat := 4983230072969 + 3 ^ 40 * 7504048 * 2
def baseEnd_7504048 : Nat := 3853183478410161611389517

theorem tailTrace_7504048 : CollatzResearch.WordTrace tailWord_7504048 prefixEnd_7504048 3853183478410161611389517 := by
  unfold tailWord_7504048
  simp only [CollatzResearch.WordTrace]
  refine ⟨136847557759061580105484399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182463410345415440140645865 136847557759061580105484399)
  ·
    refine ⟨205271336638592370158226599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136847557759061580105484399 205271336638592370158226599)
    ·
      refine ⟨307907004957888555237339899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205271336638592370158226599 307907004957888555237339899)
      ·
        refine ⟨461860507436832832856009849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307907004957888555237339899 461860507436832832856009849)
        ·
          refine ⟨346395380577624624642007387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461860507436832832856009849 346395380577624624642007387)
          ·
            refine ⟨519593070866436936963011081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346395380577624624642007387 519593070866436936963011081)
            ·
              refine ⟨389694803149827702722258311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519593070866436936963011081 389694803149827702722258311)
              ·
                refine ⟨584542204724741554083387467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389694803149827702722258311 584542204724741554083387467)
                ·
                  refine ⟨876813307087112331125081201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584542204724741554083387467 876813307087112331125081201)
                  ·
                    refine ⟨657609980315334248343810901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 876813307087112331125081201 657609980315334248343810901)
                    ·
                      refine ⟨3853183478410161611389517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 657609980315334248343810901 3853183478410161611389517)
                      ·
                        rfl

theorem cell23_7504048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_7504048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504048 prefixEnd_7504048 := by exact prefixLift 7504048
  have htrace : WordTrace (prefixWord ++ tailWord_7504048) baseStart_7504048 baseEnd_7504048 := by
    simpa [prefixWord, tailWord_7504048, baseEnd_7504048] using wordTrace_append hprefix tailTrace_7504048
  have hstable : (prefixWord ++ tailWord_7504048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504048).length < 2 ^ (prefixWord ++ tailWord_7504048).sum := by decide
  have hdescent : baseEnd_7504048 < baseStart_7504048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504082 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_7504082 : Nat := 118140960795 + 7504082 * 2 ^ 59
def prefixEnd_7504082 : Nat := 4983230072969 + 3 ^ 40 * 7504082 * 2
def baseEnd_7504082 : Nat := 3853200936752414478364361

theorem tailTrace_7504082 : CollatzResearch.WordTrace tailWord_7504082 prefixEnd_7504082 3853200936752414478364361 := by
  unfold tailWord_7504082
  simp only [CollatzResearch.WordTrace]
  refine ⟨68424088899999996004426625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182464237066666656011804333 68424088899999996004426625)
  ·
    refine ⟨51318066674999997003319969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68424088899999996004426625 51318066674999997003319969)
    ·
      refine ⟨38488550006249997752489977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51318066674999997003319969 38488550006249997752489977)
      ·
        refine ⟨28866412504687498314367483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38488550006249997752489977 28866412504687498314367483)
        ·
          refine ⟨43299618757031247471551225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28866412504687498314367483 43299618757031247471551225)
          ·
            refine ⟨32474714067773435603663419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43299618757031247471551225 32474714067773435603663419)
            ·
              refine ⟨48712071101660153405495129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32474714067773435603663419 48712071101660153405495129)
              ·
                refine ⟨36534053326245115054121347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48712071101660153405495129 36534053326245115054121347)
                ·
                  refine ⟨54801079989367672581182021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36534053326245115054121347 54801079989367672581182021)
                  ·
                    refine ⟨10275202498006438608971629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54801079989367672581182021 10275202498006438608971629)
                    ·
                      refine ⟨3853200936752414478364361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275202498006438608971629 3853200936752414478364361)
                      ·
                        rfl

theorem cell23_7504082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_7504082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504082 prefixEnd_7504082 := by exact prefixLift 7504082
  have htrace : WordTrace (prefixWord ++ tailWord_7504082) baseStart_7504082 baseEnd_7504082 := by
    simpa [prefixWord, tailWord_7504082, baseEnd_7504082] using wordTrace_append hprefix tailTrace_7504082
  have hstable : (prefixWord ++ tailWord_7504082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504082).length < 2 ^ (prefixWord ++ tailWord_7504082).sum := by decide
  have hdescent : baseEnd_7504082 < baseStart_7504082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504095 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_7504095 : Nat := 118140960795 + 7504095 * 2 ^ 59
def prefixEnd_7504095 : Nat := 4983230072969 + 3 ^ 40 * 7504095 * 2
def baseEnd_7504095 : Nat := 3853207612000922927501801

theorem tailTrace_7504095 : CollatzResearch.WordTrace tailWord_7504095 prefixEnd_7504095 3853207612000922927501801 := by
  unfold tailWord_7504095
  simp only [CollatzResearch.WordTrace]
  refine ⟨273696829748952887237929739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182464553165968591491953159 273696829748952887237929739)
  ·
    refine ⟨410545244623429330856894609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273696829748952887237929739 410545244623429330856894609)
    ·
      refine ⟨307908933467571998142670957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410545244623429330856894609 307908933467571998142670957)
      ·
        refine ⟨115465850050339499303501609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307908933467571998142670957 115465850050339499303501609)
        ·
          refine ⟨86599387537754624477626207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115465850050339499303501609 86599387537754624477626207)
          ·
            refine ⟨129899081306631936716439311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86599387537754624477626207 129899081306631936716439311)
            ·
              refine ⟨194848621959947905074658967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129899081306631936716439311 194848621959947905074658967)
              ·
                refine ⟨292272932939921857611988451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194848621959947905074658967 292272932939921857611988451)
                ·
                  refine ⟨438409399409882786417982677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292272932939921857611988451 438409399409882786417982677)
                  ·
                    refine ⟨10275220298669127806671469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 438409399409882786417982677 10275220298669127806671469)
                    ·
                      refine ⟨3853207612000922927501801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275220298669127806671469 3853207612000922927501801)
                      ·
                        rfl

theorem cell23_7504095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_7504095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504095 prefixEnd_7504095 := by exact prefixLift 7504095
  have htrace : WordTrace (prefixWord ++ tailWord_7504095) baseStart_7504095 baseEnd_7504095 := by
    simpa [prefixWord, tailWord_7504095, baseEnd_7504095] using wordTrace_append hprefix tailTrace_7504095
  have hstable : (prefixWord ++ tailWord_7504095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504095).length < 2 ^ (prefixWord ++ tailWord_7504095).sum := by decide
  have hdescent : baseEnd_7504095 < baseStart_7504095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504112 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3]
def baseStart_7504112 : Nat := 118140960795 + 7504112 * 2 ^ 59
def prefixEnd_7504112 : Nat := 4983230072969 + 3 ^ 40 * 7504112 * 2
def baseEnd_7504112 : Nat := 3853216341172049360989223

theorem tailTrace_7504112 : CollatzResearch.WordTrace tailWord_7504112 prefixEnd_7504112 3853216341172049360989223 := by
  unfold tailWord_7504112
  simp only [CollatzResearch.WordTrace]
  refine ⟨136848724894945649570649295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182464966526594199427532393 136848724894945649570649295)
  ·
    refine ⟨205273087342418474355973943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136848724894945649570649295 205273087342418474355973943)
    ·
      refine ⟨307909631013627711533960915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205273087342418474355973943 307909631013627711533960915)
      ·
        refine ⟨461864446520441567300941373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307909631013627711533960915 461864446520441567300941373)
        ·
          refine ⟨173199167445165587737853015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461864446520441567300941373 173199167445165587737853015)
          ·
            refine ⟨259798751167748381606779523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173199167445165587737853015 259798751167748381606779523)
            ·
              refine ⟨389698126751622572410169285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259798751167748381606779523 389698126751622572410169285)
              ·
                refine ⟨73068398765929232326906741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389698126751622572410169285 73068398765929232326906741)
                ·
                  refine ⟨6850162384305865530647507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73068398765929232326906741 6850162384305865530647507)
                  ·
                    refine ⟨10275243576458798295971261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850162384305865530647507 10275243576458798295971261)
                    ·
                      refine ⟨3853216341172049360989223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275243576458798295971261 3853216341172049360989223)
                      ·
                        rfl

theorem cell23_7504112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3].length) (baseStart_7504112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504112 prefixEnd_7504112 := by exact prefixLift 7504112
  have htrace : WordTrace (prefixWord ++ tailWord_7504112) baseStart_7504112 baseEnd_7504112 := by
    simpa [prefixWord, tailWord_7504112, baseEnd_7504112] using wordTrace_append hprefix tailTrace_7504112
  have hstable : (prefixWord ++ tailWord_7504112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504112).length < 2 ^ (prefixWord ++ tailWord_7504112).sum := by decide
  have hdescent : baseEnd_7504112 < baseStart_7504112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504152 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_7504152 : Nat := 118140960795 + 7504152 * 2 ^ 59
def prefixEnd_7504152 : Nat := 4983230072969 + 3 ^ 40 * 7504152 * 2
def baseEnd_7504152 : Nat := 3853236880398229204489039

theorem tailTrace_7504152 : CollatzResearch.WordTrace tailWord_7504152 prefixEnd_7504152 3853236880398229204489039 := by
  unfold tailWord_7504152
  simp only [CollatzResearch.WordTrace]
  refine ⟨136849454354873192986377355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182465939139830923981836473 136849454354873192986377355)
  ·
    refine ⟨205274181532309789479566033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136849454354873192986377355 205274181532309789479566033)
    ·
      refine ⟨153955636149232342109674525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205274181532309789479566033 153955636149232342109674525)
      ·
        refine ⟨57733363555962128291127947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153955636149232342109674525 57733363555962128291127947)
        ·
          refine ⟨86600045333943192436691921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57733363555962128291127947 86600045333943192436691921)
          ·
            refine ⟨64950034000457394327518941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86600045333943192436691921 64950034000457394327518941)
            ·
              refine ⟨24356262750171522872819603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64950034000457394327518941 24356262750171522872819603)
              ·
                refine ⟨36534394125257284309229405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24356262750171522872819603 36534394125257284309229405)
                ·
                  refine ⟨13700397796971481615961027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36534394125257284309229405 13700397796971481615961027)
                  ·
                    refine ⟨20550596695457222423941541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13700397796971481615961027 20550596695457222423941541)
                    ·
                      refine ⟨3853236880398229204489039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20550596695457222423941541 3853236880398229204489039)
                      ·
                        rfl

theorem cell23_7504152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_7504152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504152 prefixEnd_7504152 := by exact prefixLift 7504152
  have htrace : WordTrace (prefixWord ++ tailWord_7504152) baseStart_7504152 baseEnd_7504152 := by
    simpa [prefixWord, tailWord_7504152, baseEnd_7504152] using wordTrace_append hprefix tailTrace_7504152
  have hstable : (prefixWord ++ tailWord_7504152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504152).length < 2 ^ (prefixWord ++ tailWord_7504152).sum := by decide
  have hdescent : baseEnd_7504152 < baseStart_7504152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504155 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_7504155 : Nat := 118140960795 + 7504155 * 2 ^ 59
def prefixEnd_7504155 : Nat := 4983230072969 + 3 ^ 40 * 7504155 * 2
def baseEnd_7504155 : Nat := 3853238420840192692751525

theorem tailTrace_7504155 : CollatzResearch.WordTrace tailWord_7504155 prefixEnd_7504155 3853238420840192692751525 := by
  unfold tailWord_7504155
  simp only [CollatzResearch.WordTrace]
  refine ⟨273699018128735517485113919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182466012085823678323409279 273699018128735517485113919)
  ·
    refine ⟨410548527193103276227670879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273699018128735517485113919 410548527193103276227670879)
    ·
      refine ⟨615822790789654914341506319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410548527193103276227670879 615822790789654914341506319)
      ·
        refine ⟨923734186184482371512259479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615822790789654914341506319 923734186184482371512259479)
        ·
          refine ⟨1385601279276723557268389219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923734186184482371512259479 1385601279276723557268389219)
          ·
            refine ⟨2078401918915085335902583829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385601279276723557268389219 2078401918915085335902583829)
            ·
              refine ⟨97425089949144625120433617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2078401918915085335902583829 97425089949144625120433617)
              ·
                refine ⟨73068817461858468840325213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97425089949144625120433617 73068817461858468840325213)
                ·
                  refine ⟨27400806548196925815121955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73068817461858468840325213 27400806548196925815121955)
                  ·
                    refine ⟨41101209822295388722682933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27400806548196925815121955 41101209822295388722682933)
                    ·
                      refine ⟨3853238420840192692751525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41101209822295388722682933 3853238420840192692751525)
                      ·
                        rfl

theorem cell23_7504155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_7504155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504155 prefixEnd_7504155 := by exact prefixLift 7504155
  have htrace : WordTrace (prefixWord ++ tailWord_7504155) baseStart_7504155 baseEnd_7504155 := by
    simpa [prefixWord, tailWord_7504155, baseEnd_7504155] using wordTrace_append hprefix tailTrace_7504155
  have hstable : (prefixWord ++ tailWord_7504155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504155).length < 2 ^ (prefixWord ++ tailWord_7504155).sum := by decide
  have hdescent : baseEnd_7504155 < baseStart_7504155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504162 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7504162 : Nat := 118140960795 + 7504162 * 2 ^ 59
def prefixEnd_7504162 : Nat := 4983230072969 + 3 ^ 40 * 7504162 * 2
def baseEnd_7504162 : Nat := 1284414005068258055121331

theorem tailTrace_7504162 : CollatzResearch.WordTrace tailWord_7504162 prefixEnd_7504162 1284414005068258055121331 := by
  unfold tailWord_7504162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68424818359927539420154685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182466182293140105120412493 68424818359927539420154685)
  ·
    refine ⟨25659306884972827282558007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68424818359927539420154685 25659306884972827282558007)
    ·
      refine ⟨38488960327459240923837011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25659306884972827282558007 38488960327459240923837011)
      ·
        refine ⟨57733440491188861385755517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38488960327459240923837011 57733440491188861385755517)
        ·
          refine ⟨21650040184195823019658319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57733440491188861385755517 21650040184195823019658319)
          ·
            refine ⟨32475060276293734529487479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21650040184195823019658319 32475060276293734529487479)
            ·
              refine ⟨48712590414440601794231219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32475060276293734529487479 48712590414440601794231219)
              ·
                refine ⟨73068885621660902691346829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48712590414440601794231219 73068885621660902691346829)
                ·
                  refine ⟨27400832108122838509255061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73068885621660902691346829 27400832108122838509255061)
                  ·
                    refine ⟨1284414005068258055121331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27400832108122838509255061 1284414005068258055121331)
                    ·
                      rfl

theorem cell23_7504162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7504162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504162 prefixEnd_7504162 := by exact prefixLift 7504162
  have htrace : WordTrace (prefixWord ++ tailWord_7504162) baseStart_7504162 baseEnd_7504162 := by
    simpa [prefixWord, tailWord_7504162, baseEnd_7504162] using wordTrace_append hprefix tailTrace_7504162
  have hstable : (prefixWord ++ tailWord_7504162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504162).length < 2 ^ (prefixWord ++ tailWord_7504162).sum := by decide
  have hdescent : baseEnd_7504162 < baseStart_7504162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504172 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_7504172 : Nat := 118140960795 + 7504172 * 2 ^ 59
def prefixEnd_7504172 : Nat := 4983230072969 + 3 ^ 40 * 7504172 * 2
def baseEnd_7504172 : Nat := 3853247150011319126238947

theorem tailTrace_7504172 : CollatzResearch.WordTrace tailWord_7504172 prefixEnd_7504172 3853247150011319126238947 := by
  unfold tailWord_7504172
  simp only [CollatzResearch.WordTrace]
  refine ⟨136849819084836964694241385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182466425446449286258988513 136849819084836964694241385)
  ·
    refine ⟨102637364313627723520681039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136849819084836964694241385 102637364313627723520681039)
    ·
      refine ⟨153956046470441585281021559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102637364313627723520681039 153956046470441585281021559)
      ·
        refine ⟨230934069705662377921532339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153956046470441585281021559 230934069705662377921532339)
        ·
          refine ⟨346401104558493566882298509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230934069705662377921532339 346401104558493566882298509)
          ·
            refine ⟨129900414209435087580861941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346401104558493566882298509 129900414209435087580861941)
            ·
              refine ⟨12178163832134539460705807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129900414209435087580861941 12178163832134539460705807)
              ·
                refine ⟨18267245748201809191058711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12178163832134539460705807 18267245748201809191058711)
                ·
                  refine ⟨27400868622302713786588067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18267245748201809191058711 27400868622302713786588067)
                  ·
                    refine ⟨41101302933454070679882101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27400868622302713786588067 41101302933454070679882101)
                    ·
                      refine ⟨3853247150011319126238947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41101302933454070679882101 3853247150011319126238947)
                      ·
                        rfl

theorem cell23_7504172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_7504172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504172 prefixEnd_7504172 := by exact prefixLift 7504172
  have htrace : WordTrace (prefixWord ++ tailWord_7504172) baseStart_7504172 baseEnd_7504172 := by
    simpa [prefixWord, tailWord_7504172, baseEnd_7504172] using wordTrace_append hprefix tailTrace_7504172
  have hstable : (prefixWord ++ tailWord_7504172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504172).length < 2 ^ (prefixWord ++ tailWord_7504172).sum := by decide
  have hdescent : baseEnd_7504172 < baseStart_7504172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504179 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 2, 4]
def baseStart_7504179 : Nat := 118140960795 + 7504179 * 2 ^ 59
def prefixEnd_7504179 : Nat := 4983230072969 + 3 ^ 40 * 7504179 * 2
def baseEnd_7504179 : Nat := 1284416914791966866283805

theorem tailTrace_7504179 : CollatzResearch.WordTrace tailWord_7504179 prefixEnd_7504179 1284416914791966866283805 := by
  unfold tailWord_7504179
  simp only [CollatzResearch.WordTrace]
  refine ⟨273699893480648569583987591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182466595653765713055991727 273699893480648569583987591)
  ·
    refine ⟨410549840220972854375981387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273699893480648569583987591 410549840220972854375981387)
    ·
      refine ⟨615824760331459281563972081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410549840220972854375981387 615824760331459281563972081)
      ·
        refine ⟨461868570248594461172979061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615824760331459281563972081 461868570248594461172979061)
        ·
          refine ⟨43300178460805730734966787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461868570248594461172979061 43300178460805730734966787)
          ·
            refine ⟨64950267691208596102450181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43300178460805730734966787 64950267691208596102450181)
            ·
              refine ⟨12178175192101611769209409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64950267691208596102450181 12178175192101611769209409)
              ·
                refine ⟨9133631394076208826907057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12178175192101611769209409 9133631394076208826907057)
                ·
                  refine ⟨6850223545557156620180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133631394076208826907057 6850223545557156620180293)
                  ·
                    refine ⟨1284416914791966866283805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6850223545557156620180293 1284416914791966866283805)
                    ·
                      rfl

theorem cell23_7504179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 4].length) (baseStart_7504179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504179 prefixEnd_7504179 := by exact prefixLift 7504179
  have htrace : WordTrace (prefixWord ++ tailWord_7504179) baseStart_7504179 baseEnd_7504179 := by
    simpa [prefixWord, tailWord_7504179, baseEnd_7504179] using wordTrace_append hprefix tailTrace_7504179
  have hstable : (prefixWord ++ tailWord_7504179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504179).length < 2 ^ (prefixWord ++ tailWord_7504179).sum := by decide
  have hdescent : baseEnd_7504179 < baseStart_7504179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504180 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7504180 : Nat := 118140960795 + 7504180 * 2 ^ 59
def prefixEnd_7504180 : Nat := 4983230072969 + 3 ^ 40 * 7504180 * 2
def baseEnd_7504180 : Nat := 3853251257856555094938911

theorem tailTrace_7504180 : CollatzResearch.WordTrace tailWord_7504180 prefixEnd_7504180 3853251257856555094938911 := by
  unfold tailWord_7504180
  simp only [CollatzResearch.WordTrace]
  refine ⟨136849964976822473377386997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182466619969096631169849329 136849964976822473377386997)
  ·
    refine ⟨12829684216577106879130031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136849964976822473377386997 12829684216577106879130031)
    ·
      refine ⟨19244526324865660318695047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829684216577106879130031 19244526324865660318695047)
      ·
        refine ⟨28866789487298490478042571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244526324865660318695047 28866789487298490478042571)
        ·
          refine ⟨43300184230947735717063857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28866789487298490478042571 43300184230947735717063857)
          ·
            refine ⟨32475138173210801787797893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43300184230947735717063857 32475138173210801787797893)
            ·
              refine ⟨6089088407477025335212105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32475138173210801787797893 6089088407477025335212105)
              ·
                refine ⟨4566816305607769001409079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6089088407477025335212105 4566816305607769001409079)
                ·
                  refine ⟨6850224458411653502113619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566816305607769001409079 6850224458411653502113619)
                  ·
                    refine ⟨10275336687617480253170429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850224458411653502113619 10275336687617480253170429)
                    ·
                      refine ⟨3853251257856555094938911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275336687617480253170429 3853251257856555094938911)
                      ·
                        rfl

theorem cell23_7504180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7504180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504180 prefixEnd_7504180 := by exact prefixLift 7504180
  have htrace : WordTrace (prefixWord ++ tailWord_7504180) baseStart_7504180 baseEnd_7504180 := by
    simpa [prefixWord, tailWord_7504180, baseEnd_7504180] using wordTrace_append hprefix tailTrace_7504180
  have hstable : (prefixWord ++ tailWord_7504180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504180).length < 2 ^ (prefixWord ++ tailWord_7504180).sum := by decide
  have hdescent : baseEnd_7504180 < baseStart_7504180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504195 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_7504195 : Nat := 118140960795 + 7504195 * 2 ^ 59
def prefixEnd_7504195 : Nat := 4983230072969 + 3 ^ 40 * 7504195 * 2
def baseEnd_7504195 : Nat := 3853258960066372536251341

theorem tailTrace_7504195 : CollatzResearch.WordTrace tailWord_7504195 prefixEnd_7504195 3853258960066372536251341 := by
  unfold tailWord_7504195
  simp only [CollatzResearch.WordTrace]
  refine ⟨273700477048590604316570039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182466984699060402877713359 273700477048590604316570039)
  ·
    refine ⟨410550715572885906474855059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273700477048590604316570039 410550715572885906474855059)
    ·
      refine ⟨615826073359328859712282589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410550715572885906474855059 615826073359328859712282589)
      ·
        refine ⟨230934777509748322392105971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615826073359328859712282589 230934777509748322392105971)
        ·
          refine ⟨346402166264622483588158957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230934777509748322392105971 346402166264622483588158957)
          ·
            refine ⟨129900812349233431345559609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346402166264622483588158957 129900812349233431345559609)
            ·
              refine ⟨97425609261925073509169707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129900812349233431345559609 97425609261925073509169707)
              ·
                refine ⟨146138413892887610263754561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97425609261925073509169707 146138413892887610263754561)
                ·
                  refine ⟨109603810419665707697815921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146138413892887610263754561 109603810419665707697815921)
                  ·
                    refine ⟨82202857814749280773361941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109603810419665707697815921 82202857814749280773361941)
                    ·
                      refine ⟨3853258960066372536251341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82202857814749280773361941 3853258960066372536251341)
                      ·
                        rfl

theorem cell23_7504195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_7504195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504195 prefixEnd_7504195 := by exact prefixLift 7504195
  have htrace : WordTrace (prefixWord ++ tailWord_7504195) baseStart_7504195 baseEnd_7504195 := by
    simpa [prefixWord, tailWord_7504195, baseEnd_7504195] using wordTrace_append hprefix tailTrace_7504195
  have hstable : (prefixWord ++ tailWord_7504195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504195).length < 2 ^ (prefixWord ++ tailWord_7504195).sum := by decide
  have hdescent : baseEnd_7504195 < baseStart_7504195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504196 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7504196 : Nat := 118140960795 + 7504196 * 2 ^ 59
def prefixEnd_7504196 : Nat := 4983230072969 + 3 ^ 40 * 7504196 * 2
def baseEnd_7504196 : Nat := 1284419824515675677446279

theorem tailTrace_7504196 : CollatzResearch.WordTrace tailWord_7504196 prefixEnd_7504196 1284419824515675677446279 := by
  unfold tailWord_7504196
  simp only [CollatzResearch.WordTrace]
  refine ⟨136850256760793490743678221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182467009014391320991570961 136850256760793490743678221)
  ·
    refine ⟨51318846285297559028879333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136850256760793490743678221 51318846285297559028879333)
    ·
      refine ⟨9622283678493292317914875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51318846285297559028879333 9622283678493292317914875)
      ·
        refine ⟨14433425517739938476872313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622283678493292317914875 14433425517739938476872313)
        ·
          refine ⟨10825069138304953857654235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14433425517739938476872313 10825069138304953857654235)
          ·
            refine ⟨16237603707457430786481353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825069138304953857654235 16237603707457430786481353)
            ·
              refine ⟨12178202780593073089861015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16237603707457430786481353 12178202780593073089861015)
              ·
                refine ⟨18267304170889609634791523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12178202780593073089861015 18267304170889609634791523)
                ·
                  refine ⟨27400956256334414452187285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18267304170889609634791523 27400956256334414452187285)
                  ·
                    refine ⟨1284419824515675677446279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27400956256334414452187285 1284419824515675677446279)
                    ·
                      rfl

theorem cell23_7504196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7504196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504196 prefixEnd_7504196 := by exact prefixLift 7504196
  have htrace : WordTrace (prefixWord ++ tailWord_7504196) baseStart_7504196 baseEnd_7504196 := by
    simpa [prefixWord, tailWord_7504196, baseEnd_7504196] using wordTrace_append hprefix tailTrace_7504196
  have hstable : (prefixWord ++ tailWord_7504196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504196).length < 2 ^ (prefixWord ++ tailWord_7504196).sum := by decide
  have hdescent : baseEnd_7504196 < baseStart_7504196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504220 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7504220 : Nat := 118140960795 + 7504220 * 2 ^ 59
def prefixEnd_7504220 : Nat := 4983230072969 + 3 ^ 40 * 7504220 * 2
def baseEnd_7504220 : Nat := 3853271797082734938438727

theorem tailTrace_7504220 : CollatzResearch.WordTrace tailWord_7504220 prefixEnd_7504220 3853271797082734938438727 := by
  unfold tailWord_7504220
  simp only [CollatzResearch.WordTrace]
  refine ⟨136850694436750016793115057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182467592582333355724153409 136850694436750016793115057)
  ·
    refine ⟨102638020827562512594836293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136850694436750016793115057 102638020827562512594836293)
    ·
      refine ⟨19244628905167971111531805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102638020827562512594836293 19244628905167971111531805)
      ·
        refine ⟨7216735839437989166824427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19244628905167971111531805 7216735839437989166824427)
        ·
          refine ⟨10825103759156983750236641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216735839437989166824427 10825103759156983750236641)
          ·
            refine ⟨8118827819367737812677481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825103759156983750236641 8118827819367737812677481)
            ·
              refine ⟨6089120864525803359508111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8118827819367737812677481 6089120864525803359508111)
              ·
                refine ⟨9133681296788705039262167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089120864525803359508111 9133681296788705039262167)
                ·
                  refine ⟨13700521945183057558893251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9133681296788705039262167 13700521945183057558893251)
                  ·
                    refine ⟨20550782917774586338339877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13700521945183057558893251 20550782917774586338339877)
                    ·
                      refine ⟨3853271797082734938438727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20550782917774586338339877 3853271797082734938438727)
                      ·
                        rfl

theorem cell23_7504220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7504220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504220 prefixEnd_7504220 := by exact prefixLift 7504220
  have htrace : WordTrace (prefixWord ++ tailWord_7504220) baseStart_7504220 baseEnd_7504220 := by
    simpa [prefixWord, tailWord_7504220, baseEnd_7504220] using wordTrace_append hprefix tailTrace_7504220
  have hstable : (prefixWord ++ tailWord_7504220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504220).length < 2 ^ (prefixWord ++ tailWord_7504220).sum := by decide
  have hdescent : baseEnd_7504220 < baseStart_7504220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504235 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 8]
def baseStart_7504235 : Nat := 118140960795 + 7504235 * 2 ^ 59
def prefixEnd_7504235 : Nat := 4983230072969 + 3 ^ 40 * 7504235 * 2
def baseEnd_7504235 : Nat := 1284426499764184126583719

theorem tailTrace_7504235 : CollatzResearch.WordTrace tailWord_7504235 prefixEnd_7504235 1284426499764184126583719 := by
  unfold tailWord_7504235
  simp only [CollatzResearch.WordTrace]
  refine ⟨273701935968445691148026159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182467957312297127432017439 273701935968445691148026159)
  ·
    refine ⟨410552903952668536722039239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273701935968445691148026159 410552903952668536722039239)
    ·
      refine ⟨615829355929002805083058859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410552903952668536722039239 615829355929002805083058859)
      ·
        refine ⟨923744033893504207624588289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615829355929002805083058859 923744033893504207624588289)
        ·
          refine ⟨692808025420128155718441217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923744033893504207624588289 692808025420128155718441217)
          ·
            refine ⟨519606019065096116788830913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692808025420128155718441217 519606019065096116788830913)
            ·
              refine ⟨389704514298822087591623185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519606019065096116788830913 389704514298822087591623185)
              ·
                refine ⟨292278385724116565693717389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389704514298822087591623185 292278385724116565693717389)
                ·
                  refine ⟨109604394646543712135144021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292278385724116565693717389 109604394646543712135144021)
                  ·
                    refine ⟨1284426499764184126583719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109604394646543712135144021 1284426499764184126583719)
                    ·
                      rfl

theorem cell23_7504235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_7504235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504235 prefixEnd_7504235 := by exact prefixLift 7504235
  have htrace : WordTrace (prefixWord ++ tailWord_7504235) baseStart_7504235 baseEnd_7504235 := by
    simpa [prefixWord, tailWord_7504235, baseEnd_7504235] using wordTrace_append hprefix tailTrace_7504235
  have hstable : (prefixWord ++ tailWord_7504235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504235).length < 2 ^ (prefixWord ++ tailWord_7504235).sum := by decide
  have hdescent : baseEnd_7504235 < baseStart_7504235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504236 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_7504236 : Nat := 118140960795 + 7504236 * 2 ^ 59
def prefixEnd_7504236 : Nat := 4983230072969 + 3 ^ 40 * 7504236 * 2
def baseEnd_7504236 : Nat := 3853280012773206875838653

theorem tailTrace_7504236 : CollatzResearch.WordTrace tailWord_7504236 prefixEnd_7504236 3853280012773206875838653 := by
  unfold tailWord_7504236
  simp only [CollatzResearch.WordTrace]
  refine ⟨136850986220721034159406281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182467981627628045545875041 136850986220721034159406281)
  ·
    refine ⟨102638239665540775619554711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136850986220721034159406281 102638239665540775619554711)
    ·
      refine ⟨153957359498311163429332067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102638239665540775619554711 153957359498311163429332067)
      ·
        refine ⟨230936039247466745143998101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153957359498311163429332067 230936039247466745143998101)
        ·
          refine ⟨10825126839725003678624911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230936039247466745143998101 10825126839725003678624911)
          ·
            refine ⟨16237690259587505517937367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825126839725003678624911 16237690259587505517937367)
            ·
              refine ⟨24356535389381258276906051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16237690259587505517937367 24356535389381258276906051)
              ·
                refine ⟨36534803084071887415359077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24356535389381258276906051 36534803084071887415359077)
                ·
                  refine ⟨6850275578263478890379827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36534803084071887415359077 6850275578263478890379827)
                  ·
                    refine ⟨10275413367395218335569741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850275578263478890379827 10275413367395218335569741)
                    ·
                      refine ⟨3853280012773206875838653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275413367395218335569741 3853280012773206875838653)
                      ·
                        rfl

theorem cell23_7504236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_7504236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504236 prefixEnd_7504236 := by exact prefixLift 7504236
  have htrace : WordTrace (prefixWord ++ tailWord_7504236) baseStart_7504236 baseEnd_7504236 := by
    simpa [prefixWord, tailWord_7504236, baseEnd_7504236] using wordTrace_append hprefix tailTrace_7504236
  have hstable : (prefixWord ++ tailWord_7504236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504236).length < 2 ^ (prefixWord ++ tailWord_7504236).sum := by decide
  have hdescent : baseEnd_7504236 < baseStart_7504236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504253 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_7504253 : Nat := 118140960795 + 7504253 * 2 ^ 59
def prefixEnd_7504253 : Nat := 4983230072969 + 3 ^ 40 * 7504253 * 2
def baseEnd_7504253 : Nat := 3853288741944333309326075

theorem tailTrace_7504253 : CollatzResearch.WordTrace tailWord_7504253 prefixEnd_7504253 3853288741944333309326075 := by
  unfold tailWord_7504253
  simp only [CollatzResearch.WordTrace]
  refine ⟨273702592482380480222181413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182468394988253653481454275 273702592482380480222181413)
  ·
    refine ⟨51319236090446340041659015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273702592482380480222181413 51319236090446340041659015)
    ·
      refine ⟨76978854135669510062488523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51319236090446340041659015 76978854135669510062488523)
      ·
        refine ⟨115468281203504265093732785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76978854135669510062488523 115468281203504265093732785)
        ·
          refine ⟨86601210902628198820299589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115468281203504265093732785 86601210902628198820299589)
          ·
            refine ⟨16237727044242787278806173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86601210902628198820299589 16237727044242787278806173)
            ·
              refine ⟨6089147641591045229552315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16237727044242787278806173 6089147641591045229552315)
              ·
                refine ⟨9133721462386567844328473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089147641591045229552315 9133721462386567844328473)
                ·
                  refine ⟨6850291096789925883246355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9133721462386567844328473 6850291096789925883246355)
                  ·
                    refine ⟨10275436645184888824869533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850291096789925883246355 10275436645184888824869533)
                    ·
                      refine ⟨3853288741944333309326075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275436645184888824869533 3853288741944333309326075)
                      ·
                        rfl

theorem cell23_7504253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_7504253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504253 prefixEnd_7504253 := by exact prefixLift 7504253
  have htrace : WordTrace (prefixWord ++ tailWord_7504253) baseStart_7504253 baseEnd_7504253 := by
    simpa [prefixWord, tailWord_7504253, baseEnd_7504253] using wordTrace_append hprefix tailTrace_7504253
  have hstable : (prefixWord ++ tailWord_7504253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504253).length < 2 ^ (prefixWord ++ tailWord_7504253).sum := by decide
  have hdescent : baseEnd_7504253 < baseStart_7504253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504312 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_7504312 : Nat := 118140960795 + 7504312 * 2 ^ 59
def prefixEnd_7504312 : Nat := 4983230072969 + 3 ^ 40 * 7504312 * 2
def baseEnd_7504312 : Nat := 1284439679100982859496101

theorem tailTrace_7504312 : CollatzResearch.WordTrace tailWord_7504312 prefixEnd_7504312 1284439679100982859496101 := by
  unfold tailWord_7504312
  simp only [CollatzResearch.WordTrace]
  refine ⟨136852372194583366649289595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182469829592777822199052793 136852372194583366649289595)
  ·
    refine ⟨205278558291875049973934393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136852372194583366649289595 205278558291875049973934393)
    ·
      refine ⟨153958918718906287480450795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205278558291875049973934393 153958918718906287480450795)
      ·
        refine ⟨230938378078359431220676193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153958918718906287480450795 230938378078359431220676193)
        ·
          refine ⟨173203783558769573415507145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230938378078359431220676193 173203783558769573415507145)
          ·
            refine ⟨129902837669077180061630359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173203783558769573415507145 129902837669077180061630359)
            ·
              refine ⟨194854256503615770092445539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129902837669077180061630359 194854256503615770092445539)
              ·
                refine ⟨292281384755423655138668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194854256503615770092445539 292281384755423655138668309)
                ·
                  refine ⟨13700689910410483834625077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292281384755423655138668309 13700689910410483834625077)
                  ·
                    refine ⟨1284439679100982859496101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13700689910410483834625077 1284439679100982859496101)
                    ·
                      rfl

theorem cell23_7504312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_7504312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504312 prefixEnd_7504312 := by exact prefixLift 7504312
  have htrace : WordTrace (prefixWord ++ tailWord_7504312) baseStart_7504312 baseEnd_7504312 := by
    simpa [prefixWord, tailWord_7504312, baseEnd_7504312] using wordTrace_append hprefix tailTrace_7504312
  have hstable : (prefixWord ++ tailWord_7504312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504312).length < 2 ^ (prefixWord ++ tailWord_7504312).sum := by decide
  have hdescent : baseEnd_7504312 < baseStart_7504312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504352 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_7504352 : Nat := 118140960795 + 7504352 * 2 ^ 59
def prefixEnd_7504352 : Nat := 4983230072969 + 3 ^ 40 * 7504352 * 2
def baseEnd_7504352 : Nat := 3853339576529128421988119

theorem tailTrace_7504352 : CollatzResearch.WordTrace tailWord_7504352 prefixEnd_7504352 3853339576529128421988119 := by
  unfold tailWord_7504352
  simp only [CollatzResearch.WordTrace]
  refine ⟨136853101654510910065017655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182470802206014546753356873 136853101654510910065017655)
  ·
    refine ⟨205279652481766365097526483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136853101654510910065017655 205279652481766365097526483)
    ·
      refine ⟨307919478722649547646289725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205279652481766365097526483 307919478722649547646289725)
      ·
        refine ⟨115469804520993580367358647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307919478722649547646289725 115469804520993580367358647)
        ·
          refine ⟨173204706781490370551037971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115469804520993580367358647 173204706781490370551037971)
          ·
            refine ⟨259807060172235555826556957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173204706781490370551037971 259807060172235555826556957)
            ·
              refine ⟨97427647564588333434958859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259807060172235555826556957 97427647564588333434958859)
              ·
                refine ⟨146141471346882500152438289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97427647564588333434958859 146141471346882500152438289)
                ·
                  refine ⟨109606103510161875114328717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146141471346882500152438289 109606103510161875114328717)
                  ·
                    refine ⟨41102288816310703167873269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109606103510161875114328717 41102288816310703167873269)
                    ·
                      refine ⟨3853339576529128421988119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41102288816310703167873269 3853339576529128421988119)
                      ·
                        rfl

theorem cell23_7504352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_7504352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504352 prefixEnd_7504352 := by exact prefixLift 7504352
  have htrace : WordTrace (prefixWord ++ tailWord_7504352) baseStart_7504352 baseEnd_7504352 := by
    simpa [prefixWord, tailWord_7504352, baseEnd_7504352] using wordTrace_append hprefix tailTrace_7504352
  have hstable : (prefixWord ++ tailWord_7504352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504352).length < 2 ^ (prefixWord ++ tailWord_7504352).sum := by decide
  have hdescent : baseEnd_7504352 < baseStart_7504352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504366 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_7504366 : Nat := 118140960795 + 7504366 * 2 ^ 59
def prefixEnd_7504366 : Nat := 4983230072969 + 3 ^ 40 * 7504366 * 2
def baseEnd_7504366 : Nat := 3853346765258291367213055

theorem tailTrace_7504366 : CollatzResearch.WordTrace tailWord_7504366 prefixEnd_7504366 3853346765258291367213055 := by
  unfold tailWord_7504366
  simp only [CollatzResearch.WordTrace]
  refine ⟨34213339241371387565130619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182471142620647400347363301 34213339241371387565130619)
  ·
    refine ⟨51320008862057081347695929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34213339241371387565130619 51320008862057081347695929)
    ·
      refine ⟨38490006646542811010771947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51320008862057081347695929 38490006646542811010771947)
      ·
        refine ⟨57735009969814216516157921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38490006646542811010771947 57735009969814216516157921)
        ·
          refine ⟨43301257477360662387118441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57735009969814216516157921 43301257477360662387118441)
          ·
            refine ⟨32475943108020496790338831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43301257477360662387118441 32475943108020496790338831)
            ·
              refine ⟨48713914662030745185508247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32475943108020496790338831 48713914662030745185508247)
              ·
                refine ⟨73070871993046117778262371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48713914662030745185508247 73070871993046117778262371)
                ·
                  refine ⟨109606307989569176667393557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73070871993046117778262371 109606307989569176667393557)
                  ·
                    refine ⟨5137795687011055156284073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109606307989569176667393557 5137795687011055156284073)
                    ·
                      refine ⟨3853346765258291367213055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137795687011055156284073 3853346765258291367213055)
                      ·
                        rfl

theorem cell23_7504366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_7504366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504366 prefixEnd_7504366 := by exact prefixLift 7504366
  have htrace : WordTrace (prefixWord ++ tailWord_7504366) baseStart_7504366 baseEnd_7504366 := by
    simpa [prefixWord, tailWord_7504366, baseEnd_7504366] using wordTrace_append hprefix tailTrace_7504366
  have hstable : (prefixWord ++ tailWord_7504366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504366).length < 2 ^ (prefixWord ++ tailWord_7504366).sum := by decide
  have hdescent : baseEnd_7504366 < baseStart_7504366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504369 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_7504369 : Nat := 118140960795 + 7504369 * 2 ^ 59
def prefixEnd_7504369 : Nat := 4983230072969 + 3 ^ 40 * 7504369 * 2
def baseEnd_7504369 : Nat := 3853348305700254855475541

theorem tailTrace_7504369 : CollatzResearch.WordTrace tailWord_7504369 prefixEnd_7504369 3853348305700254855475541 := by
  unfold tailWord_7504369
  simp only [CollatzResearch.WordTrace]
  refine ⟨273706823349960232033404161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182471215566640154688936107 273706823349960232033404161)
  ·
    refine ⟨205280117512470174025053121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273706823349960232033404161 205280117512470174025053121)
    ·
      refine ⟨153960088134352630518789841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205280117512470174025053121 153960088134352630518789841)
      ·
        refine ⟨115470066100764472889092381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153960088134352630518789841 115470066100764472889092381)
        ·
          refine ⟨43301274787786677333409643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115470066100764472889092381 43301274787786677333409643)
          ·
            refine ⟨64951912181680016000114465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43301274787786677333409643 64951912181680016000114465)
            ·
              refine ⟨48713934136260012000085849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64951912181680016000114465 48713934136260012000085849)
              ·
                refine ⟨36535450602195009000064387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48713934136260012000085849 36535450602195009000064387)
                ·
                  refine ⟨54803175903292513500096581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36535450602195009000064387 54803175903292513500096581)
                  ·
                    refine ⟨10275595481867346281268109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54803175903292513500096581 10275595481867346281268109)
                    ·
                      refine ⟨3853348305700254855475541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275595481867346281268109 3853348305700254855475541)
                      ·
                        rfl

theorem cell23_7504369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_7504369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504369 prefixEnd_7504369 := by exact prefixLift 7504369
  have htrace : WordTrace (prefixWord ++ tailWord_7504369) baseStart_7504369 baseEnd_7504369 := by
    simpa [prefixWord, tailWord_7504369, baseEnd_7504369] using wordTrace_append hprefix tailTrace_7504369
  have hstable : (prefixWord ++ tailWord_7504369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504369).length < 2 ^ (prefixWord ++ tailWord_7504369).sum := by decide
  have hdescent : baseEnd_7504369 < baseStart_7504369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504459 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_7504459 : Nat := 118140960795 + 7504459 * 2 ^ 59
def prefixEnd_7504459 : Nat := 4983230072969 + 3 ^ 40 * 7504459 * 2
def baseEnd_7504459 : Nat := 3853394518959159503350127

theorem tailTrace_7504459 : CollatzResearch.WordTrace tailWord_7504459 prefixEnd_7504459 3853394518959159503350127 := by
  unfold tailWord_7504459
  simp only [CollatzResearch.WordTrace]
  refine ⟨273710105919634177404180431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182473403946422784936120287 273710105919634177404180431)
  ·
    refine ⟨410565158879451266106270647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273710105919634177404180431 410565158879451266106270647)
    ·
      refine ⟨615847738319176899159405971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410565158879451266106270647 615847738319176899159405971)
      ·
        refine ⟨923771607478765348739108957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615847738319176899159405971 923771607478765348739108957)
        ·
          refine ⟨346414352804537005777165859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 923771607478765348739108957 346414352804537005777165859)
          ·
            refine ⟨519621529206805508665748789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346414352804537005777165859 519621529206805508665748789)
            ·
              refine ⟨48714518363138016437413949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519621529206805508665748789 48714518363138016437413949)
              ·
                refine ⟨18267944386176756164030231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48714518363138016437413949 18267944386176756164030231)
                ·
                  refine ⟨27401916579265134246045347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18267944386176756164030231 27401916579265134246045347)
                  ·
                    refine ⟨41102874868897701369068021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27401916579265134246045347 41102874868897701369068021)
                    ·
                      refine ⟨3853394518959159503350127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41102874868897701369068021 3853394518959159503350127)
                      ·
                        rfl

theorem cell23_7504459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_7504459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504459 prefixEnd_7504459 := by exact prefixLift 7504459
  have htrace : WordTrace (prefixWord ++ tailWord_7504459) baseStart_7504459 baseEnd_7504459 := by
    simpa [prefixWord, tailWord_7504459, baseEnd_7504459] using wordTrace_append hprefix tailTrace_7504459
  have hstable : (prefixWord ++ tailWord_7504459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504459).length < 2 ^ (prefixWord ++ tailWord_7504459).sum := by decide
  have hdescent : baseEnd_7504459 < baseStart_7504459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504466 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_7504466 : Nat := 118140960795 + 7504466 * 2 ^ 59
def prefixEnd_7504466 : Nat := 4983230072969 + 3 ^ 40 * 7504466 * 2
def baseEnd_7504466 : Nat := 1284466037774580325320865

theorem tailTrace_7504466 : CollatzResearch.WordTrace tailWord_7504466 prefixEnd_7504466 1284466037774580325320865 := by
  unfold tailWord_7504466
  simp only [CollatzResearch.WordTrace]
  refine ⟨68427590307652204399921313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182473574153739211733123501 68427590307652204399921313)
  ·
    refine ⟨51320692730739153299940985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68427590307652204399921313 51320692730739153299940985)
    ·
      refine ⟨38490519548054364974955739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51320692730739153299940985 38490519548054364974955739)
      ·
        refine ⟨57735779322081547462433609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38490519548054364974955739 57735779322081547462433609)
        ·
          refine ⟨43301834491561160596825207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57735779322081547462433609 43301834491561160596825207)
          ·
            refine ⟨64952751737341740895237811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43301834491561160596825207 64952751737341740895237811)
            ·
              refine ⟨97429127606012611342856717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64952751737341740895237811 97429127606012611342856717)
              ·
                refine ⟨36535922852254729253571269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97429127606012611342856717 36535922852254729253571269)
                ·
                  refine ⟨6850485534797761735044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36535922852254729253571269 6850485534797761735044613)
                  ·
                    refine ⟨1284466037774580325320865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6850485534797761735044613 1284466037774580325320865)
                    ·
                      rfl

theorem cell23_7504466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_7504466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504466 prefixEnd_7504466 := by exact prefixLift 7504466
  have htrace : WordTrace (prefixWord ++ tailWord_7504466) baseStart_7504466 baseEnd_7504466 := by
    simpa [prefixWord, tailWord_7504466, baseEnd_7504466] using wordTrace_append hprefix tailTrace_7504466
  have hstable : (prefixWord ++ tailWord_7504466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504466).length < 2 ^ (prefixWord ++ tailWord_7504466).sum := by decide
  have hdescent : baseEnd_7504466 < baseStart_7504466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504469 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7504469 : Nat := 118140960795 + 7504469 * 2 ^ 59
def prefixEnd_7504469 : Nat := 4983230072969 + 3 ^ 40 * 7504469 * 2
def baseEnd_7504469 : Nat := 3853399653765704464225081

theorem tailTrace_7504469 : CollatzResearch.WordTrace tailWord_7504469 prefixEnd_7504469 3853399653765704464225081 := by
  unfold tailWord_7504469
  simp only [CollatzResearch.WordTrace]
  refine ⟨273710470649597949112044461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182473647099731966074696307 273710470649597949112044461)
  ·
    refine ⟨102641426493599230917016673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273710470649597949112044461 102641426493599230917016673)
    ·
      refine ⟨76981069870199423187762505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102641426493599230917016673 76981069870199423187762505)
      ·
        refine ⟨57735802402649567390821879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76981069870199423187762505 57735802402649567390821879)
        ·
          refine ⟨86603703603974351086232819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57735802402649567390821879 86603703603974351086232819)
          ·
            refine ⟨129905555405961526629349229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86603703603974351086232819 129905555405961526629349229)
            ·
              refine ⟨48714583277235572486005961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129905555405961526629349229 48714583277235572486005961)
              ·
                refine ⟨36535937457926679364504471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48714583277235572486005961 36535937457926679364504471)
                ·
                  refine ⟨54803906186890019046756707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36535937457926679364504471 54803906186890019046756707)
                  ·
                    refine ⟨82205859280335028570135061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54803906186890019046756707 82205859280335028570135061)
                    ·
                      refine ⟨3853399653765704464225081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82205859280335028570135061 3853399653765704464225081)
                      ·
                        rfl

theorem cell23_7504469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7504469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504469 prefixEnd_7504469 := by exact prefixLift 7504469
  have htrace : WordTrace (prefixWord ++ tailWord_7504469) baseStart_7504469 baseEnd_7504469 := by
    simpa [prefixWord, tailWord_7504469, baseEnd_7504469] using wordTrace_append hprefix tailTrace_7504469
  have hstable : (prefixWord ++ tailWord_7504469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504469).length < 2 ^ (prefixWord ++ tailWord_7504469).sum := by decide
  have hdescent : baseEnd_7504469 < baseStart_7504469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504493 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7504493 : Nat := 118140960795 + 7504493 * 2 ^ 59
def prefixEnd_7504493 : Nat := 4983230072969 + 3 ^ 40 * 7504493 * 2
def baseEnd_7504493 : Nat := 3853411977301412370324971

theorem tailTrace_7504493 : CollatzResearch.WordTrace tailWord_7504493 prefixEnd_7504493 3853411977301412370324971 := by
  unfold tailWord_7504493
  simp only [CollatzResearch.WordTrace]
  refine ⟨273711346001511001210918133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182474230667674000807278755 273711346001511001210918133)
  ·
    refine ⟨25660438687641656363523575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273711346001511001210918133 25660438687641656363523575)
    ·
      refine ⟨38490658031462484545285363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25660438687641656363523575 38490658031462484545285363)
      ·
        refine ⟨57735987047193726817928045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38490658031462484545285363 57735987047193726817928045)
        ·
          refine ⟨21650995142697647556723017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57735987047193726817928045 21650995142697647556723017)
          ·
            refine ⟨16238246357023235667542263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21650995142697647556723017 16238246357023235667542263)
            ·
              refine ⟨24357369535534853501313395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16238246357023235667542263 24357369535534853501313395)
              ·
                refine ⟨36536054303302280251970093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24357369535534853501313395 36536054303302280251970093)
                ·
                  refine ⟨13701020363738355094488785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36536054303302280251970093 13701020363738355094488785)
                  ·
                    refine ⟨10275765272803766320866589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13701020363738355094488785 10275765272803766320866589)
                    ·
                      refine ⟨3853411977301412370324971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275765272803766320866589 3853411977301412370324971)
                      ·
                        rfl

theorem cell23_7504493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7504493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504493 prefixEnd_7504493 := by exact prefixLift 7504493
  have htrace : WordTrace (prefixWord ++ tailWord_7504493) baseStart_7504493 baseEnd_7504493 := by
    simpa [prefixWord, tailWord_7504493, baseEnd_7504493] using wordTrace_append hprefix tailTrace_7504493
  have hstable : (prefixWord ++ tailWord_7504493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504493).length < 2 ^ (prefixWord ++ tailWord_7504493).sum := by decide
  have hdescent : baseEnd_7504493 < baseStart_7504493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504540 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_7504540 : Nat := 118140960795 + 7504540 * 2 ^ 59
def prefixEnd_7504540 : Nat := 4983230072969 + 3 ^ 40 * 7504540 * 2
def baseEnd_7504540 : Nat := 3853436110892173686437255

theorem tailTrace_7504540 : CollatzResearch.WordTrace tailWord_7504540 prefixEnd_7504540 3853436110892173686437255 := by
  unfold tailWord_7504540
  simp only [CollatzResearch.WordTrace]
  refine ⟨136856530116170364118939537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182475373488227152158586049 136856530116170364118939537)
  ·
    refine ⟨102642397587127773089204653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136856530116170364118939537 102642397587127773089204653)
    ·
      refine ⟨38490899095172914908451745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102642397587127773089204653 38490899095172914908451745)
      ·
        refine ⟨28868174321379686181338809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38490899095172914908451745 28868174321379686181338809)
        ·
          refine ⟨21651130741034764636004107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28868174321379686181338809 21651130741034764636004107)
          ·
            refine ⟨32476696111552146954006161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21651130741034764636004107 32476696111552146954006161)
            ·
              refine ⟨24357522083664110215504621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32476696111552146954006161 24357522083664110215504621)
              ·
                refine ⟨9134070781374041330814233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24357522083664110215504621 9134070781374041330814233)
                ·
                  refine ⟨6850553086030530998110675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9134070781374041330814233 6850553086030530998110675)
                  ·
                    refine ⟨10275829629045796497166013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850553086030530998110675 10275829629045796497166013)
                    ·
                      refine ⟨3853436110892173686437255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10275829629045796497166013 3853436110892173686437255)
                      ·
                        rfl

theorem cell23_7504540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_7504540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504540 prefixEnd_7504540 := by exact prefixLift 7504540
  have htrace : WordTrace (prefixWord ++ tailWord_7504540) baseStart_7504540 baseEnd_7504540 := by
    simpa [prefixWord, tailWord_7504540, baseEnd_7504540] using wordTrace_append hprefix tailTrace_7504540
  have hstable : (prefixWord ++ tailWord_7504540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504540).length < 2 ^ (prefixWord ++ tailWord_7504540).sum := by decide
  have hdescent : baseEnd_7504540 < baseStart_7504540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504563 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 4, 2]
def baseStart_7504563 : Nat := 118140960795 + 7504563 * 2 ^ 59
def prefixEnd_7504563 : Nat := 4983230072969 + 3 ^ 40 * 7504563 * 2
def baseEnd_7504563 : Nat := 3853447920947227096449649

theorem tailTrace_7504563 : CollatzResearch.WordTrace tailWord_7504563 prefixEnd_7504563 3853447920947227096449649 := by
  unfold tailWord_7504563
  simp only [CollatzResearch.WordTrace]
  refine ⟨273713899111257403165966343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182475932740838268777310895 273713899111257403165966343)
  ·
    refine ⟨410570848666886104748949515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273713899111257403165966343 410570848666886104748949515)
    ·
      refine ⟨615856273000329157123424273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410570848666886104748949515 615856273000329157123424273)
      ·
        refine ⟨461892204750246867842568205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615856273000329157123424273 461892204750246867842568205)
        ·
          refine ⟨173209576781342575440963077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461892204750246867842568205 173209576781342575440963077)
          ·
            refine ⟨32476795646501732895180577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173209576781342575440963077 32476795646501732895180577)
            ·
              refine ⟨24357596734876299671385433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32476795646501732895180577 24357596734876299671385433)
              ·
                refine ⟨18268197551157224753539075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24357596734876299671385433 18268197551157224753539075)
                ·
                  refine ⟨27402296326735837130308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18268197551157224753539075 27402296326735837130308613)
                  ·
                    refine ⟨5137930561262969461932865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27402296326735837130308613 5137930561262969461932865)
                    ·
                      refine ⟨3853447920947227096449649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5137930561262969461932865 3853447920947227096449649)
                      ·
                        rfl

theorem cell23_7504563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 4, 2].length) (baseStart_7504563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504563 prefixEnd_7504563 := by exact prefixLift 7504563
  have htrace : WordTrace (prefixWord ++ tailWord_7504563) baseStart_7504563 baseEnd_7504563 := by
    simpa [prefixWord, tailWord_7504563, baseEnd_7504563] using wordTrace_append hprefix tailTrace_7504563
  have hstable : (prefixWord ++ tailWord_7504563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504563).length < 2 ^ (prefixWord ++ tailWord_7504563).sum := by decide
  have hdescent : baseEnd_7504563 < baseStart_7504563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504569 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 11]
def baseStart_7504569 : Nat := 118140960795 + 7504569 * 2 ^ 59
def prefixEnd_7504569 : Nat := 4983230072969 + 3 ^ 40 * 7504569 * 2
def baseEnd_7504569 : Nat := 428161222425683785886069

theorem tailTrace_7504569 : CollatzResearch.WordTrace tailWord_7504569 prefixEnd_7504569 428161222425683785886069 := by
  unfold tailWord_7504569
  simp only [CollatzResearch.WordTrace]
  refine ⟨273714117949235666190684761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182476078632823777460456507 273714117949235666190684761)
  ·
    refine ⟨205285588461926749643013571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273714117949235666190684761 205285588461926749643013571)
    ·
      refine ⟨307928382692890124464520357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205285588461926749643013571 307928382692890124464520357)
      ·
        refine ⟨57736571754916898337097567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307928382692890124464520357 57736571754916898337097567)
        ·
          refine ⟨86604857632375347505646351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57736571754916898337097567 86604857632375347505646351)
          ·
            refine ⟨129907286448563021258469527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86604857632375347505646351 129907286448563021258469527)
            ·
              refine ⟨194860929672844531887704291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129907286448563021258469527 194860929672844531887704291)
              ·
                refine ⟨292291394509266797831556437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194860929672844531887704291 292291394509266797831556437)
                ·
                  refine ⟨428161222425683785886069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 292291394509266797831556437 428161222425683785886069)
                  ·
                    rfl

theorem cell23_7504569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_7504569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504569 prefixEnd_7504569 := by exact prefixLift 7504569
  have htrace : WordTrace (prefixWord ++ tailWord_7504569) baseStart_7504569 baseEnd_7504569 := by
    simpa [prefixWord, tailWord_7504569, baseEnd_7504569] using wordTrace_append hprefix tailTrace_7504569
  have hstable : (prefixWord ++ tailWord_7504569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504569).length < 2 ^ (prefixWord ++ tailWord_7504569).sum := by decide
  have hdescent : baseEnd_7504569 < baseStart_7504569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504576 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_7504576 : Nat := 118140960795 + 7504576 * 2 ^ 59
def prefixEnd_7504576 : Nat := 4983230072969 + 3 ^ 40 * 7504576 * 2
def baseEnd_7504576 : Nat := 3853454596195735545587089

theorem tailTrace_7504576 : CollatzResearch.WordTrace tailWord_7504576 prefixEnd_7504576 3853454596195735545587089 := by
  unfold tailWord_7504576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136857186630105153193094791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182476248840140204257459721 136857186630105153193094791)
  ·
    refine ⟨205285779945157729789642187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136857186630105153193094791 205285779945157729789642187)
    ·
      refine ⟨307928669917736594684463281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205285779945157729789642187 307928669917736594684463281)
      ·
        refine ⟨230946502438302446013347461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307928669917736594684463281 230946502438302446013347461)
        ·
          refine ⟨43302469207181708627502649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230946502438302446013347461 43302469207181708627502649)
          ·
            refine ⟨32476851905386281470626987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43302469207181708627502649 32476851905386281470626987)
            ·
              refine ⟨48715277858079422205940481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32476851905386281470626987 48715277858079422205940481)
              ·
                refine ⟨36536458393559566654455361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48715277858079422205940481 36536458393559566654455361)
                ·
                  refine ⟨27402343795169674990841521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36536458393559566654455361 27402343795169674990841521)
                  ·
                    refine ⟨20551757846377256243131141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27402343795169674990841521 20551757846377256243131141)
                    ·
                      refine ⟨3853454596195735545587089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20551757846377256243131141 3853454596195735545587089)
                      ·
                        rfl

theorem cell23_7504576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_7504576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504576 prefixEnd_7504576 := by exact prefixLift 7504576
  have htrace : WordTrace (prefixWord ++ tailWord_7504576) baseStart_7504576 baseEnd_7504576 := by
    simpa [prefixWord, tailWord_7504576, baseEnd_7504576] using wordTrace_append hprefix tailTrace_7504576
  have hstable : (prefixWord ++ tailWord_7504576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504576).length < 2 ^ (prefixWord ++ tailWord_7504576).sum := by decide
  have hdescent : baseEnd_7504576 < baseStart_7504576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504586 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_7504586 : Nat := 118140960795 + 7504586 * 2 ^ 59
def prefixEnd_7504586 : Nat := 4983230072969 + 3 ^ 40 * 7504586 * 2
def baseEnd_7504586 : Nat := 428162192333586722940227

theorem tailTrace_7504586 : CollatzResearch.WordTrace tailWord_7504586 prefixEnd_7504586 428162192333586722940227 := by
  unfold tailWord_7504586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68428684497543519523513403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182476491993449385396035741 68428684497543519523513403)
  ·
    refine ⟨102643026746315279285270105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68428684497543519523513403 102643026746315279285270105)
    ·
      refine ⟨76982270059736459463952579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102643026746315279285270105 76982270059736459463952579)
      ·
        refine ⟨115473405089604689195928869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76982270059736459463952579 115473405089604689195928869)
        ·
          refine ⟨21651263454300879224236663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115473405089604689195928869 21651263454300879224236663)
          ·
            refine ⟨32476895181451318836354995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21651263454300879224236663 32476895181451318836354995)
            ·
              refine ⟨48715342772176978254532493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32476895181451318836354995 48715342772176978254532493)
              ·
                refine ⟨18268253539566366845449685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48715342772176978254532493 18268253539566366845449685)
                ·
                  refine ⟨428162192333586722940227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18268253539566366845449685 428162192333586722940227)
                  ·
                    rfl

theorem cell23_7504586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_7504586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504586 prefixEnd_7504586 := by exact prefixLift 7504586
  have htrace : WordTrace (prefixWord ++ tailWord_7504586) baseStart_7504586 baseEnd_7504586 := by
    simpa [prefixWord, tailWord_7504586, baseEnd_7504586] using wordTrace_append hprefix tailTrace_7504586
  have hstable : (prefixWord ++ tailWord_7504586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504586).length < 2 ^ (prefixWord ++ tailWord_7504586).sum := by decide
  have hdescent : baseEnd_7504586 < baseStart_7504586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504693 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 6]
def baseStart_7504693 : Nat := 118140960795 + 7504693 * 2 ^ 59
def prefixEnd_7504693 : Nat := 4983230072969 + 3 ^ 40 * 7504693 * 2
def baseEnd_7504693 : Nat := 428168297048034620869339

theorem tailTrace_7504693 : CollatzResearch.WordTrace tailWord_7504693 prefixEnd_7504693 428168297048034620869339 := by
  unfold tailWord_7504693
  simp only [CollatzResearch.WordTrace]
  refine ⟨273718640600786435368198733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182479093733857623578799155 273718640600786435368198733)
  ·
    refine ⟨102644490225294913263074525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273718640600786435368198733 102644490225294913263074525)
    ·
      refine ⟨38491683834485592473652947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102644490225294913263074525 38491683834485592473652947)
      ·
        refine ⟨57737525751728388710479421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38491683834485592473652947 57737525751728388710479421)
        ·
          refine ⟨21651572156898145766429783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57737525751728388710479421 21651572156898145766429783)
          ·
            refine ⟨32477358235347218649644675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21651572156898145766429783 32477358235347218649644675)
            ·
              refine ⟨48716037353020827974467013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32477358235347218649644675 48716037353020827974467013)
              ·
                refine ⟨9134257003691405245212565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48716037353020827974467013 9134257003691405245212565)
                ·
                  refine ⟨428168297048034620869339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9134257003691405245212565 428168297048034620869339)
                  ·
                    rfl

theorem cell23_7504693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_7504693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504693 prefixEnd_7504693 := by exact prefixLift 7504693
  have htrace : WordTrace (prefixWord ++ tailWord_7504693) baseStart_7504693 baseEnd_7504693 := by
    simpa [prefixWord, tailWord_7504693, baseEnd_7504693] using wordTrace_append hprefix tailTrace_7504693
  have hstable : (prefixWord ++ tailWord_7504693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504693).length < 2 ^ (prefixWord ++ tailWord_7504693).sum := by decide
  have hdescent : baseEnd_7504693 < baseStart_7504693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504696 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_7504696 : Nat := 118140960795 + 7504696 * 2 ^ 59
def prefixEnd_7504696 : Nat := 4983230072969 + 3 ^ 40 * 7504696 * 2
def baseEnd_7504696 : Nat := 3853516213874275076086537

theorem tailTrace_7504696 : CollatzResearch.WordTrace tailWord_7504696 prefixEnd_7504696 3853516213874275076086537 := by
  unfold tailWord_7504696
  simp only [CollatzResearch.WordTrace]
  refine ⟨136859375009887783440278971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182479166679850377920371961 136859375009887783440278971)
  ·
    refine ⟨205289062514831675160418457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136859375009887783440278971 205289062514831675160418457)
    ·
      refine ⟨153966796886123756370313843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205289062514831675160418457 153966796886123756370313843)
      ·
        refine ⟨230950195329185634555470765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153966796886123756370313843 230950195329185634555470765)
        ·
          refine ⟨86606323248444612958301537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230950195329185634555470765 86606323248444612958301537)
          ·
            refine ⟨64954742436333459718726153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86606323248444612958301537 64954742436333459718726153)
            ·
              refine ⟨48716056827250094789044615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64954742436333459718726153 48716056827250094789044615)
              ·
                refine ⟨73074085240875142183566923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48716056827250094789044615 73074085240875142183566923)
                ·
                  refine ⟨109611127861312713275350385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73074085240875142183566923 109611127861312713275350385)
                  ·
                    refine ⟨82208345895984534956512789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109611127861312713275350385 82208345895984534956512789)
                    ·
                      refine ⟨3853516213874275076086537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82208345895984534956512789 3853516213874275076086537)
                      ·
                        rfl

theorem cell23_7504696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_7504696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504696 prefixEnd_7504696 := by exact prefixLift 7504696
  have htrace : WordTrace (prefixWord ++ tailWord_7504696) baseStart_7504696 baseEnd_7504696 := by
    simpa [prefixWord, tailWord_7504696, baseEnd_7504696] using wordTrace_append hprefix tailTrace_7504696
  have hstable : (prefixWord ++ tailWord_7504696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504696).length < 2 ^ (prefixWord ++ tailWord_7504696).sum := by decide
  have hdescent : baseEnd_7504696 < baseStart_7504696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504724 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_7504724 : Nat := 118140960795 + 7504724 * 2 ^ 59
def prefixEnd_7504724 : Nat := 4983230072969 + 3 ^ 40 * 7504724 * 2
def baseEnd_7504724 : Nat := 3853530591332600966536409

theorem tailTrace_7504724 : CollatzResearch.WordTrace tailWord_7504724 prefixEnd_7504724 3853530591332600966536409 := by
  unfold tailWord_7504724
  simp only [CollatzResearch.WordTrace]
  refine ⟨136859885631837063831288613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182479847509116085108384817 136859885631837063831288613)
  ·
    refine ⟨25661228555969449468366615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136859885631837063831288613 25661228555969449468366615)
    ·
      refine ⟨38491842833954174202549923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661228555969449468366615 38491842833954174202549923)
      ·
        refine ⟨57737764250931261303824885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38491842833954174202549923 57737764250931261303824885)
        ·
          refine ⟨5412915398524805747233583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57737764250931261303824885 5412915398524805747233583)
          ·
            refine ⟨8119373097787208620850375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412915398524805747233583 8119373097787208620850375)
            ·
              refine ⟨12179059646680812931275563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8119373097787208620850375 12179059646680812931275563)
              ·
                refine ⟨18268589470021219396913345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179059646680812931275563 18268589470021219396913345)
                ·
                  refine ⟨13701442102515914547685009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18268589470021219396913345 13701442102515914547685009)
                  ·
                    refine ⟨10276081576886935910763757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13701442102515914547685009 10276081576886935910763757)
                    ·
                      refine ⟨3853530591332600966536409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276081576886935910763757 3853530591332600966536409)
                      ·
                        rfl

theorem cell23_7504724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_7504724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504724 prefixEnd_7504724 := by exact prefixLift 7504724
  have htrace : WordTrace (prefixWord ++ tailWord_7504724) baseStart_7504724 baseEnd_7504724 := by
    simpa [prefixWord, tailWord_7504724, baseEnd_7504724] using wordTrace_append hprefix tailTrace_7504724
  have hstable : (prefixWord ++ tailWord_7504724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504724).length < 2 ^ (prefixWord ++ tailWord_7504724).sum := by decide
  have hdescent : baseEnd_7504724 < baseStart_7504724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504730 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_7504730 : Nat := 118140960795 + 7504730 * 2 ^ 59
def prefixEnd_7504730 : Nat := 4983230072969 + 3 ^ 40 * 7504730 * 2
def baseEnd_7504730 : Nat := 3853533672216527943061381

theorem tailTrace_7504730 : CollatzResearch.WordTrace tailWord_7504730 prefixEnd_7504730 3853533672216527943061381 := by
  unfold tailWord_7504730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68429997525413097671823911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182479993401101593791530429 68429997525413097671823911)
  ·
    refine ⟨102644996288119646507735867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68429997525413097671823911 102644996288119646507735867)
    ·
      refine ⟨153967494432179469761603801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102644996288119646507735867 153967494432179469761603801)
      ·
        refine ⟨115475620824134602321202851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153967494432179469761603801 115475620824134602321202851)
        ·
          refine ⟨173213431236201903481804277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115475620824134602321202851 173213431236201903481804277)
          ·
            refine ⟨16238759178393928451419151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173213431236201903481804277 16238759178393928451419151)
            ·
              refine ⟨24358138767590892677128727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16238759178393928451419151 24358138767590892677128727)
              ·
                refine ⟨36537208151386339015693091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24358138767590892677128727 36537208151386339015693091)
                ·
                  refine ⟨54805812227079508523539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36537208151386339015693091 54805812227079508523539637)
                  ·
                    refine ⟨5138044896288703924081841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54805812227079508523539637 5138044896288703924081841)
                    ·
                      refine ⟨3853533672216527943061381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138044896288703924081841 3853533672216527943061381)
                      ·
                        rfl

theorem cell23_7504730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_7504730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504730 prefixEnd_7504730 := by exact prefixLift 7504730
  have htrace : WordTrace (prefixWord ++ tailWord_7504730) baseStart_7504730 baseEnd_7504730 := by
    simpa [prefixWord, tailWord_7504730, baseEnd_7504730] using wordTrace_append hprefix tailTrace_7504730
  have hstable : (prefixWord ++ tailWord_7504730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504730).length < 2 ^ (prefixWord ++ tailWord_7504730).sum := by decide
  have hdescent : baseEnd_7504730 < baseStart_7504730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504740 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_7504740 : Nat := 118140960795 + 7504740 * 2 ^ 59
def prefixEnd_7504740 : Nat := 4983230072969 + 3 ^ 40 * 7504740 * 2
def baseEnd_7504740 : Nat := 1284512935674357634645445

theorem tailTrace_7504740 : CollatzResearch.WordTrace tailWord_7504740 prefixEnd_7504740 1284512935674357634645445 := by
  unfold tailWord_7504740
  simp only [CollatzResearch.WordTrace]
  refine ⟨136860177415808081197579837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182480236554410774930106449 136860177415808081197579837)
  ·
    refine ⟨51322566530928030449092439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136860177415808081197579837 51322566530928030449092439)
    ·
      refine ⟨76983849796392045673638659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51322566530928030449092439 76983849796392045673638659)
      ·
        refine ⟨115475774694588068510457989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76983849796392045673638659 115475774694588068510457989)
        ·
          refine ⟨21651707755235262845710873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115475774694588068510457989 21651707755235262845710873)
          ·
            refine ⟨16238780816426447134283155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21651707755235262845710873 16238780816426447134283155)
            ·
              refine ⟨24358171224639670701424733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16238780816426447134283155 24358171224639670701424733)
              ·
                refine ⟨9134314209239876513034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24358171224639670701424733 9134314209239876513034275)
                ·
                  refine ⟨13701471313859814769551413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134314209239876513034275 13701471313859814769551413)
                  ·
                    refine ⟨1284512935674357634645445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13701471313859814769551413 1284512935674357634645445)
                    ·
                      rfl

theorem cell23_7504740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_7504740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504740 prefixEnd_7504740 := by exact prefixLift 7504740
  have htrace : WordTrace (prefixWord ++ tailWord_7504740) baseStart_7504740 baseEnd_7504740 := by
    simpa [prefixWord, tailWord_7504740, baseEnd_7504740] using wordTrace_append hprefix tailTrace_7504740
  have hstable : (prefixWord ++ tailWord_7504740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504740).length < 2 ^ (prefixWord ++ tailWord_7504740).sum := by decide
  have hdescent : baseEnd_7504740 < baseStart_7504740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504763 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3]
def baseStart_7504763 : Nat := 118140960795 + 7504763 * 2 ^ 59
def prefixEnd_7504763 : Nat := 4983230072969 + 3 ^ 40 * 7504763 * 2
def baseEnd_7504763 : Nat := 3853550617078126313948729

theorem tailTrace_7504763 : CollatzResearch.WordTrace tailWord_7504763 prefixEnd_7504763 3853550617078126313948729 := by
  unfold tailWord_7504763
  simp only [CollatzResearch.WordTrace]
  refine ⟨273721193710532837323246943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182480795807021891548831295 273721193710532837323246943)
  ·
    refine ⟨410581790565799255984870415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273721193710532837323246943 410581790565799255984870415)
    ·
      refine ⟨615872685848698883977305623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410581790565799255984870415 615872685848698883977305623)
      ·
        refine ⟨923809028773048325965958435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615872685848698883977305623 923809028773048325965958435)
        ·
          refine ⟨1385713543159572488948937653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923809028773048325965958435 1385713543159572488948937653)
          ·
            refine ⟨129910644671209920838962905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1385713543159572488948937653 129910644671209920838962905)
            ·
              refine ⟨97432983503407440629222179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129910644671209920838962905 97432983503407440629222179)
              ·
                refine ⟨146149475255111160943833269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97432983503407440629222179 146149475255111160943833269)
                ·
                  refine ⟨13701513305166671338484369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146149475255111160943833269 13701513305166671338484369)
                  ·
                    refine ⟨10276134978875003503863277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13701513305166671338484369 10276134978875003503863277)
                    ·
                      refine ⟨3853550617078126313948729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276134978875003503863277 3853550617078126313948729)
                      ·
                        rfl

theorem cell23_7504763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].length) (baseStart_7504763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504763 prefixEnd_7504763 := by exact prefixLift 7504763
  have htrace : WordTrace (prefixWord ++ tailWord_7504763) baseStart_7504763 baseEnd_7504763 := by
    simpa [prefixWord, tailWord_7504763, baseEnd_7504763] using wordTrace_append hprefix tailTrace_7504763
  have hstable : (prefixWord ++ tailWord_7504763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504763).length < 2 ^ (prefixWord ++ tailWord_7504763).sum := by decide
  have hdescent : baseEnd_7504763 < baseStart_7504763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504773 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_7504773 : Nat := 118140960795 + 7504773 * 2 ^ 59
def prefixEnd_7504773 : Nat := 4983230072969 + 3 ^ 40 * 7504773 * 2
def baseEnd_7504773 : Nat := 3853555751884671274823683

theorem tailTrace_7504773 : CollatzResearch.WordTrace tailWord_7504773 prefixEnd_7504773 3853555751884671274823683 := by
  unfold tailWord_7504773
  simp only [CollatzResearch.WordTrace]
  refine ⟨273721558440496609031110973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182481038960331072687407315 273721558440496609031110973)
  ·
    refine ⟨102645584415186228386666615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273721558440496609031110973 102645584415186228386666615)
    ·
      refine ⟨153968376622779342579999923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102645584415186228386666615 153968376622779342579999923)
      ·
        refine ⟨230952564934169013869999885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153968376622779342579999923 230952564934169013869999885)
        ·
          refine ⟨86607211850313380201249957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230952564934169013869999885 86607211850313380201249957)
          ·
            refine ⟨16238852221933758787734367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86607211850313380201249957 16238852221933758787734367)
            ·
              refine ⟨24358278332900638181601551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16238852221933758787734367 24358278332900638181601551)
              ·
                refine ⟨36537417499350957272402327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24358278332900638181601551 36537417499350957272402327)
                ·
                  refine ⟨54806126249026435908603491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36537417499350957272402327 54806126249026435908603491)
                  ·
                    refine ⟨82209189373539653862905237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54806126249026435908603491 82209189373539653862905237)
                    ·
                      refine ⟨3853555751884671274823683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82209189373539653862905237 3853555751884671274823683)
                      ·
                        rfl

theorem cell23_7504773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_7504773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504773 prefixEnd_7504773 := by exact prefixLift 7504773
  have htrace : WordTrace (prefixWord ++ tailWord_7504773) baseStart_7504773 baseEnd_7504773 := by
    simpa [prefixWord, tailWord_7504773, baseEnd_7504773] using wordTrace_append hprefix tailTrace_7504773
  have hstable : (prefixWord ++ tailWord_7504773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504773).length < 2 ^ (prefixWord ++ tailWord_7504773).sum := by decide
  have hdescent : baseEnd_7504773 < baseStart_7504773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504777 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 3, 2, 2]
def baseStart_7504777 : Nat := 118140960795 + 7504777 * 2 ^ 59
def prefixEnd_7504777 : Nat := 4983230072969 + 3 ^ 40 * 7504777 * 2
def baseEnd_7504777 : Nat := 3853557805807289259173665

theorem tailTrace_7504777 : CollatzResearch.WordTrace tailWord_7504777 prefixEnd_7504777 3853557805807289259173665 := by
  unfold tailWord_7504777
  simp only [CollatzResearch.WordTrace]
  refine ⟨273721704332482117714256585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182481136221654745142837723 273721704332482117714256585)
  ·
    refine ⟨205291278249361588285692439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273721704332482117714256585 205291278249361588285692439)
    ·
      refine ⟨307936917374042382428538659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205291278249361588285692439 307936917374042382428538659)
      ·
        refine ⟨461905376061063573642807989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307936917374042382428538659 461905376061063573642807989)
        ·
          refine ⟨43303629005724710029013249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461905376061063573642807989 43303629005724710029013249)
          ·
            refine ⟨32477721754293532521759937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43303629005724710029013249 32477721754293532521759937)
            ·
              refine ⟨24358291315720149391319953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32477721754293532521759937 24358291315720149391319953)
              ·
                refine ⟨18268718486790112043489965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24358291315720149391319953 18268718486790112043489965)
                ·
                  refine ⟨6850769432546292016308737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18268718486790112043489965 6850769432546292016308737)
                  ·
                    refine ⟨5138077074409719012231553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6850769432546292016308737 5138077074409719012231553)
                    ·
                      refine ⟨3853557805807289259173665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138077074409719012231553 3853557805807289259173665)
                      ·
                        rfl

theorem cell23_7504777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 2, 2].length) (baseStart_7504777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504777 prefixEnd_7504777 := by exact prefixLift 7504777
  have htrace : WordTrace (prefixWord ++ tailWord_7504777) baseStart_7504777 baseEnd_7504777 := by
    simpa [prefixWord, tailWord_7504777, baseEnd_7504777] using wordTrace_append hprefix tailTrace_7504777
  have hstable : (prefixWord ++ tailWord_7504777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504777).length < 2 ^ (prefixWord ++ tailWord_7504777).sum := by decide
  have hdescent : baseEnd_7504777 < baseStart_7504777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504780 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_7504780 : Nat := 118140960795 + 7504780 * 2 ^ 59
def prefixEnd_7504780 : Nat := 4983230072969 + 3 ^ 40 * 7504780 * 2
def baseEnd_7504780 : Nat := 3853559346249252747436151

theorem tailTrace_7504780 : CollatzResearch.WordTrace tailWord_7504780 prefixEnd_7504780 3853559346249252747436151 := by
  unfold tailWord_7504780
  simp only [CollatzResearch.WordTrace]
  refine ⟨136860906875735624613307897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182481209167647499484410529 136860906875735624613307897)
  ·
    refine ⟨102645680156801718459980923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136860906875735624613307897 102645680156801718459980923)
    ·
      refine ⟨153968520235202577689971385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102645680156801718459980923 153968520235202577689971385)
      ·
        refine ⟨115476390176401933267478539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153968520235202577689971385 115476390176401933267478539)
        ·
          refine ⟨173214585264602899901217809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115476390176401933267478539 173214585264602899901217809)
          ·
            refine ⟨129910938948452174925913357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173214585264602899901217809 129910938948452174925913357)
            ·
              refine ⟨48716602105669565597217509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129910938948452174925913357 48716602105669565597217509)
              ·
                refine ⟨9134362894813043549478283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48716602105669565597217509 9134362894813043549478283)
                ·
                  refine ⟨13701544342219565324217425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134362894813043549478283 13701544342219565324217425)
                  ·
                    refine ⟨10276158256664673993163069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13701544342219565324217425 10276158256664673993163069)
                    ·
                      refine ⟨3853559346249252747436151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276158256664673993163069 3853559346249252747436151)
                      ·
                        rfl

theorem cell23_7504780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_7504780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504780 prefixEnd_7504780 := by exact prefixLift 7504780
  have htrace : WordTrace (prefixWord ++ tailWord_7504780) baseStart_7504780 baseEnd_7504780 := by
    simpa [prefixWord, tailWord_7504780, baseEnd_7504780] using wordTrace_append hprefix tailTrace_7504780
  have hstable : (prefixWord ++ tailWord_7504780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504780).length < 2 ^ (prefixWord ++ tailWord_7504780).sum := by decide
  have hdescent : baseEnd_7504780 < baseStart_7504780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504793 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_7504793 : Nat := 118140960795 + 7504793 * 2 ^ 59
def prefixEnd_7504793 : Nat := 4983230072969 + 3 ^ 40 * 7504793 * 2
def baseEnd_7504793 : Nat := 3853566021497761196573591

theorem tailTrace_7504793 : CollatzResearch.WordTrace tailWord_7504793 prefixEnd_7504793 3853566021497761196573591 := by
  unfold tailWord_7504793
  simp only [CollatzResearch.WordTrace]
  refine ⟨273722287900424152446839033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182481525266949434964559355 273722287900424152446839033)
  ·
    refine ⟨205291715925318114335129275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273722287900424152446839033 205291715925318114335129275)
    ·
      refine ⟨307937573887977171502693913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205291715925318114335129275 307937573887977171502693913)
      ·
        refine ⟨230953180415982878627020435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307937573887977171502693913 230953180415982878627020435)
        ·
          refine ⟨346429770623974317940530653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230953180415982878627020435 346429770623974317940530653)
          ·
            refine ⟨129911163983990369227698995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346429770623974317940530653 129911163983990369227698995)
            ·
              refine ⟨194866745975985553841548493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129911163983990369227698995 194866745975985553841548493)
              ·
                refine ⟨73075029740994582690580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194866745975985553841548493 73075029740994582690580685)
                ·
                  refine ⟨27403136152872968508967757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73075029740994582690580685 27403136152872968508967757)
                  ·
                    refine ⟨10276176057327363190862909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27403136152872968508967757 10276176057327363190862909)
                    ·
                      refine ⟨3853566021497761196573591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276176057327363190862909 3853566021497761196573591)
                      ·
                        rfl

theorem cell23_7504793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_7504793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504793 prefixEnd_7504793 := by exact prefixLift 7504793
  have htrace : WordTrace (prefixWord ++ tailWord_7504793) baseStart_7504793 baseEnd_7504793 := by
    simpa [prefixWord, tailWord_7504793, baseEnd_7504793] using wordTrace_append hprefix tailTrace_7504793
  have hstable : (prefixWord ++ tailWord_7504793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504793).length < 2 ^ (prefixWord ++ tailWord_7504793).sum := by decide
  have hdescent : baseEnd_7504793 < baseStart_7504793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504907 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 5]
def baseStart_7504907 : Nat := 118140960795 + 7504907 * 2 ^ 59
def prefixEnd_7504907 : Nat := 4983230072969 + 3 ^ 40 * 7504907 * 2
def baseEnd_7504907 : Nat := 428180506476930416727563

theorem tailTrace_7504907 : CollatzResearch.WordTrace tailWord_7504907 prefixEnd_7504907 428180506476930416727563 := by
  unfold tailWord_7504907
  simp only [CollatzResearch.WordTrace]
  refine ⟨273726445822011149916488975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182484297214674099944325983 273726445822011149916488975)
  ·
    refine ⟨410589668733016724874733463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273726445822011149916488975 410589668733016724874733463)
    ·
      refine ⟨615884503099525087312100195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410589668733016724874733463 615884503099525087312100195)
      ·
        refine ⟨923826754649287630968150293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615884503099525087312100195 923826754649287630968150293)
        ·
          refine ⟨43304379124185357701632045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 923826754649287630968150293 43304379124185357701632045)
          ·
            refine ⟨16239142171569509138112017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43304379124185357701632045 16239142171569509138112017)
            ·
              refine ⟨12179356628677131853584013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16239142171569509138112017 12179356628677131853584013)
              ·
                refine ⟨4567258735753924445094005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12179356628677131853584013 4567258735753924445094005)
                ·
                  refine ⟨428180506476930416727563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567258735753924445094005 428180506476930416727563)
                  ·
                    rfl

theorem cell23_7504907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 5].length) (baseStart_7504907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504907 prefixEnd_7504907 := by exact prefixLift 7504907
  have htrace : WordTrace (prefixWord ++ tailWord_7504907) baseStart_7504907 baseEnd_7504907 := by
    simpa [prefixWord, tailWord_7504907, baseEnd_7504907] using wordTrace_append hprefix tailTrace_7504907
  have hstable : (prefixWord ++ tailWord_7504907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504907).length < 2 ^ (prefixWord ++ tailWord_7504907).sum := by decide
  have hdescent : baseEnd_7504907 < baseStart_7504907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504913 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7504913 : Nat := 118140960795 + 7504913 * 2 ^ 59
def prefixEnd_7504913 : Nat := 4983230072969 + 3 ^ 40 * 7504913 * 2
def baseEnd_7504913 : Nat := 3853627639176300727073039

theorem tailTrace_7504913 : CollatzResearch.WordTrace tailWord_7504913 prefixEnd_7504913 3853627639176300727073039 := by
  unfold tailWord_7504913
  simp only [CollatzResearch.WordTrace]
  refine ⟨273726664659989412941207393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182484443106659608627471595 273726664659989412941207393)
  ·
    refine ⟨205294998494992059705905545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273726664659989412941207393 205294998494992059705905545)
    ·
      refine ⟨153971248871244044779429159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205294998494992059705905545 153971248871244044779429159)
      ·
        refine ⟨230956873306866067169143739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153971248871244044779429159 230956873306866067169143739)
        ·
          refine ⟨346435309960299100753715609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230956873306866067169143739 346435309960299100753715609)
          ·
            refine ⟨259826482470224325565286707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346435309960299100753715609 259826482470224325565286707)
            ·
              refine ⟨389739723705336488347930061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259826482470224325565286707 389739723705336488347930061)
              ·
                refine ⟨146152396389501183130473773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389739723705336488347930061 146152396389501183130473773)
                ·
                  refine ⟨54807148646062943673927665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146152396389501183130473773 54807148646062943673927665)
                  ·
                    refine ⟨41105361484547207755445749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54807148646062943673927665 41105361484547207755445749)
                    ·
                      refine ⟨3853627639176300727073039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41105361484547207755445749 3853627639176300727073039)
                      ·
                        rfl

theorem cell23_7504913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7504913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504913 prefixEnd_7504913 := by exact prefixLift 7504913
  have htrace : WordTrace (prefixWord ++ tailWord_7504913) baseStart_7504913 baseEnd_7504913 := by
    simpa [prefixWord, tailWord_7504913, baseEnd_7504913] using wordTrace_append hprefix tailTrace_7504913
  have hstable : (prefixWord ++ tailWord_7504913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504913).length < 2 ^ (prefixWord ++ tailWord_7504913).sum := by decide
  have hdescent : baseEnd_7504913 < baseStart_7504913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504943 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_7504943 : Nat := 118140960795 + 7504943 * 2 ^ 59
def prefixEnd_7504943 : Nat := 4983230072969 + 3 ^ 40 * 7504943 * 2
def baseEnd_7504943 : Nat := 3853643043595935609697901

theorem tailTrace_7504943 : CollatzResearch.WordTrace tailWord_7504943 prefixEnd_7504943 3853643043595935609697901 := by
  unfold tailWord_7504943
  simp only [CollatzResearch.WordTrace]
  refine ⟨273727758849880728064799483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182485172566587152043199655 273727758849880728064799483)
  ·
    refine ⟨410591638274821092097199225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273727758849880728064799483 410591638274821092097199225)
    ·
      refine ⟨307943728706115819072899419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410591638274821092097199225 307943728706115819072899419)
      ·
        refine ⟨461915593059173728609349129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307943728706115819072899419 461915593059173728609349129)
        ·
          refine ⟨346436694794380296457011847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461915593059173728609349129 346436694794380296457011847)
          ·
            refine ⟨519655042191570444685517771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346436694794380296457011847 519655042191570444685517771)
            ·
              refine ⟨779482563287355667028276657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519655042191570444685517771 779482563287355667028276657)
              ·
                refine ⟨584611922465516750271207493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779482563287355667028276657 584611922465516750271207493)
                ·
                  refine ⟨109614735462284390675851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584611922465516750271207493 109614735462284390675851405)
                  ·
                    refine ⟨41105525798356646503444277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109614735462284390675851405 41105525798356646503444277)
                    ·
                      refine ⟨3853643043595935609697901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41105525798356646503444277 3853643043595935609697901)
                      ·
                        rfl

theorem cell23_7504943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_7504943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504943 prefixEnd_7504943 := by exact prefixLift 7504943
  have htrace : WordTrace (prefixWord ++ tailWord_7504943) baseStart_7504943 baseEnd_7504943 := by
    simpa [prefixWord, tailWord_7504943, baseEnd_7504943] using wordTrace_append hprefix tailTrace_7504943
  have hstable : (prefixWord ++ tailWord_7504943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504943).length < 2 ^ (prefixWord ++ tailWord_7504943).sum := by decide
  have hdescent : baseEnd_7504943 < baseStart_7504943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504960 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3]
def baseStart_7504960 : Nat := 118140960795 + 7504960 * 2 ^ 59
def prefixEnd_7504960 : Nat := 4983230072969 + 3 ^ 40 * 7504960 * 2
def baseEnd_7504960 : Nat := 3853651772767062043185323

theorem tailTrace_7504960 : CollatzResearch.WordTrace tailWord_7504960 prefixEnd_7504960 3853651772767062043185323 := by
  unfold tailWord_7504960
  simp only [CollatzResearch.WordTrace]
  refine ⟨136864189445409569984084167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182485585927212759978778889 136864189445409569984084167)
  ·
    refine ⟨205296284168114354976126251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136864189445409569984084167 205296284168114354976126251)
    ·
      refine ⟨307944426252171532464189377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205296284168114354976126251 307944426252171532464189377)
      ·
        refine ⟨230958319689128649348142033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307944426252171532464189377 230958319689128649348142033)
        ·
          refine ⟨173218739766846487011106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230958319689128649348142033 173218739766846487011106525)
          ·
            refine ⟨64957027412567432629164947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173218739766846487011106525 64957027412567432629164947)
            ·
              refine ⟨97435541118851148943747421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64957027412567432629164947 97435541118851148943747421)
              ·
                refine ⟨36538327919569180853905283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97435541118851148943747421 36538327919569180853905283)
                ·
                  refine ⟨54807491879353771280857925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36538327919569180853905283 54807491879353771280857925)
                  ·
                    refine ⟨10276404727378832115160861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54807491879353771280857925 10276404727378832115160861)
                    ·
                      refine ⟨3853651772767062043185323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276404727378832115160861 3853651772767062043185323)
                      ·
                        rfl

theorem cell23_7504960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_7504960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504960 prefixEnd_7504960 := by exact prefixLift 7504960
  have htrace : WordTrace (prefixWord ++ tailWord_7504960) baseStart_7504960 baseEnd_7504960 := by
    simpa [prefixWord, tailWord_7504960, baseEnd_7504960] using wordTrace_append hprefix tailTrace_7504960
  have hstable : (prefixWord ++ tailWord_7504960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504960).length < 2 ^ (prefixWord ++ tailWord_7504960).sum := by decide
  have hdescent : baseEnd_7504960 < baseStart_7504960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504963 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 10]
def baseStart_7504963 : Nat := 118140960795 + 7504963 * 2 ^ 59
def prefixEnd_7504963 : Nat := 4983230072969 + 3 ^ 40 * 7504963 * 2
def baseEnd_7504963 : Nat := 428183701467669503494201

theorem tailTrace_7504963 : CollatzResearch.WordTrace tailWord_7504963 prefixEnd_7504963 428183701467669503494201 := by
  unfold tailWord_7504963
  simp only [CollatzResearch.WordTrace]
  refine ⟨273728488309808271480527543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182485658873205514320351695 273728488309808271480527543)
  ·
    refine ⟨410592732464712407220791315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273728488309808271480527543 410592732464712407220791315)
    ·
      refine ⟨615889098697068610831186973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410592732464712407220791315 615889098697068610831186973)
      ·
        refine ⟨230958412011400729061695115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615889098697068610831186973 230958412011400729061695115)
        ·
          refine ⟨346437618017101093592542673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230958412011400729061695115 346437618017101093592542673)
          ·
            refine ⟨259828213512825820194407005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346437618017101093592542673 259828213512825820194407005)
            ·
              refine ⟨97435580067309682572902627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259828213512825820194407005 97435580067309682572902627)
              ·
                refine ⟨146153370100964523859353941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97435580067309682572902627 146153370100964523859353941)
                ·
                  refine ⟨428183701467669503494201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146153370100964523859353941 428183701467669503494201)
                  ·
                    rfl

theorem cell23_7504963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 10].length) (baseStart_7504963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504963 prefixEnd_7504963 := by exact prefixLift 7504963
  have htrace : WordTrace (prefixWord ++ tailWord_7504963) baseStart_7504963 baseEnd_7504963 := by
    simpa [prefixWord, tailWord_7504963, baseEnd_7504963] using wordTrace_append hprefix tailTrace_7504963
  have hstable : (prefixWord ++ tailWord_7504963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504963).length < 2 ^ (prefixWord ++ tailWord_7504963).sum := by decide
  have hdescent : baseEnd_7504963 < baseStart_7504963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7504980 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 8]
def baseStart_7504980 : Nat := 118140960795 + 7504980 * 2 ^ 59
def prefixEnd_7504980 : Nat := 4983230072969 + 3 ^ 40 * 7504980 * 2
def baseEnd_7504980 : Nat := 428184671375572440548359

theorem tailTrace_7504980 : CollatzResearch.WordTrace tailWord_7504980 prefixEnd_7504980 428184671375572440548359 := by
  unfold tailWord_7504980
  simp only [CollatzResearch.WordTrace]
  refine ⟨136864554175373341691948197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182486072233831122255930929 136864554175373341691948197)
  ·
    refine ⟨25662103907882501567240287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136864554175373341691948197 25662103907882501567240287)
    ·
      refine ⟨38493155861823752350860431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662103907882501567240287 38493155861823752350860431)
      ·
        refine ⟨57739733792735628526290647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38493155861823752350860431 57739733792735628526290647)
        ·
          refine ⟨86609600689103442789435971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57739733792735628526290647 86609600689103442789435971)
          ·
            refine ⟨129914401033655164184153957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86609600689103442789435971 129914401033655164184153957)
            ·
              refine ⟨24358950193810343284528867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129914401033655164184153957 24358950193810343284528867)
              ·
                refine ⟨36538425290715514926793301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24358950193810343284528867 36538425290715514926793301)
                ·
                  refine ⟨428184671375572440548359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36538425290715514926793301 428184671375572440548359)
                  ·
                    rfl

theorem cell23_7504980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_7504980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7504980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7504980 prefixEnd_7504980 := by exact prefixLift 7504980
  have htrace : WordTrace (prefixWord ++ tailWord_7504980) baseStart_7504980 baseEnd_7504980 := by
    simpa [prefixWord, tailWord_7504980, baseEnd_7504980] using wordTrace_append hprefix tailTrace_7504980
  have hstable : (prefixWord ++ tailWord_7504980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7504980).length < 2 ^ (prefixWord ++ tailWord_7504980).sum := by decide
  have hdescent : baseEnd_7504980 < baseStart_7504980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7504980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505007 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_7505007 : Nat := 118140960795 + 7505007 * 2 ^ 59
def prefixEnd_7505007 : Nat := 4983230072969 + 3 ^ 40 * 7505007 * 2
def baseEnd_7505007 : Nat := 3853675906357823359297607

theorem tailTrace_7505007 : CollatzResearch.WordTrace tailWord_7505007 prefixEnd_7505007 3853675906357823359297607 := by
  unfold tailWord_7505007
  simp only [CollatzResearch.WordTrace]
  refine ⟨273730093121648866995129275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182486728747765911330086183 273730093121648866995129275)
  ·
    refine ⟨410595139682473300492693913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273730093121648866995129275 410595139682473300492693913)
    ·
      refine ⟨307946354761854975369520435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410595139682473300492693913 307946354761854975369520435)
      ·
        refine ⟨461919532142782463054280653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307946354761854975369520435 461919532142782463054280653)
        ·
          refine ⟨173219824553543423645355245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461919532142782463054280653 173219824553543423645355245)
          ·
            refine ⟨64957434207578783867008217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173219824553543423645355245 64957434207578783867008217)
            ·
              refine ⟨48718075655684087900256163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64957434207578783867008217 48718075655684087900256163)
              ·
                refine ⟨73077113483526131850384245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48718075655684087900256163 73077113483526131850384245)
                ·
                  refine ⟨6850979389080574860973523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73077113483526131850384245 6850979389080574860973523)
                  ·
                    refine ⟨10276469083620862291460285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850979389080574860973523 10276469083620862291460285)
                    ·
                      refine ⟨3853675906357823359297607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276469083620862291460285 3853675906357823359297607)
                      ·
                        rfl

theorem cell23_7505007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_7505007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505007 prefixEnd_7505007 := by exact prefixLift 7505007
  have htrace : WordTrace (prefixWord ++ tailWord_7505007) baseStart_7505007 baseEnd_7505007 := by
    simpa [prefixWord, tailWord_7505007, baseEnd_7505007] using wordTrace_append hprefix tailTrace_7505007
  have hstable : (prefixWord ++ tailWord_7505007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505007).length < 2 ^ (prefixWord ++ tailWord_7505007).sum := by decide
  have hdescent : baseEnd_7505007 < baseStart_7505007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505034 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_7505034 : Nat := 118140960795 + 7505034 * 2 ^ 59
def prefixEnd_7505034 : Nat := 4983230072969 + 3 ^ 40 * 7505034 * 2
def baseEnd_7505034 : Nat := 3853689770335494753659983

theorem tailTrace_7505034 : CollatzResearch.WordTrace tailWord_7505034 prefixEnd_7505034 3853689770335494753659983 := by
  unfold tailWord_7505034
  simp only [CollatzResearch.WordTrace]
  refine ⟨68432769473137762651590539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182487385261700700404241437 68432769473137762651590539)
  ·
    refine ⟨102649154209706643977385809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68432769473137762651590539 102649154209706643977385809)
    ·
      refine ⟨76986865657279982983039357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102649154209706643977385809 76986865657279982983039357)
      ·
        refine ⟨28870074621479993618639759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76986865657279982983039357 28870074621479993618639759)
        ·
          refine ⟨43305111932219990427959639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28870074621479993618639759 43305111932219990427959639)
          ·
            refine ⟨64957667898329985641939459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43305111932219990427959639 64957667898329985641939459)
            ·
              refine ⟨97436501847494978462909189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64957667898329985641939459 97436501847494978462909189)
              ·
                refine ⟨18269344096405308461795473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97436501847494978462909189 18269344096405308461795473)
                ·
                  refine ⟨13702008072303981346346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18269344096405308461795473 13702008072303981346346605)
                  ·
                    refine ⟨5138253027113993004879977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13702008072303981346346605 5138253027113993004879977)
                    ·
                      refine ⟨3853689770335494753659983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138253027113993004879977 3853689770335494753659983)
                      ·
                        rfl

theorem cell23_7505034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_7505034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505034 prefixEnd_7505034 := by exact prefixLift 7505034
  have htrace : WordTrace (prefixWord ++ tailWord_7505034) baseStart_7505034 baseEnd_7505034 := by
    simpa [prefixWord, tailWord_7505034, baseEnd_7505034] using wordTrace_append hprefix tailTrace_7505034
  have hstable : (prefixWord ++ tailWord_7505034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505034).length < 2 ^ (prefixWord ++ tailWord_7505034).sum := by decide
  have hdescent : baseEnd_7505034 < baseStart_7505034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505047 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_7505047 : Nat := 118140960795 + 7505047 * 2 ^ 59
def prefixEnd_7505047 : Nat := 4983230072969 + 3 ^ 40 * 7505047 * 2
def baseEnd_7505047 : Nat := 3853696445584003202797423

theorem tailTrace_7505047 : CollatzResearch.WordTrace tailWord_7505047 prefixEnd_7505047 3853696445584003202797423 := by
  unfold tailWord_7505047
  simp only [CollatzResearch.WordTrace]
  refine ⟨273731552041503953826585395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182487701361002635884390263 273731552041503953826585395)
  ·
    refine ⟨410597328062255930739878093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273731552041503953826585395 410597328062255930739878093)
    ·
      refine ⟨153973998023345974027454285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410597328062255930739878093 153973998023345974027454285)
      ·
        refine ⟨57740249258754740260295357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153973998023345974027454285 57740249258754740260295357)
        ·
          refine ⟨21652593472033027597610759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57740249258754740260295357 21652593472033027597610759)
          ·
            refine ⟨32478890208049541396416139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21652593472033027597610759 32478890208049541396416139)
            ·
              refine ⟨48718335312074312094624209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478890208049541396416139 48718335312074312094624209)
              ·
                refine ⟨36538751484055734070968157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48718335312074312094624209 36538751484055734070968157)
                ·
                  refine ⟨13702031806520900276613059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36538751484055734070968157 13702031806520900276613059)
                  ·
                    refine ⟨20553047709781350414919589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13702031806520900276613059 20553047709781350414919589)
                    ·
                      refine ⟨3853696445584003202797423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20553047709781350414919589 3853696445584003202797423)
                      ·
                        rfl

theorem cell23_7505047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_7505047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505047 prefixEnd_7505047 := by exact prefixLift 7505047
  have htrace : WordTrace (prefixWord ++ tailWord_7505047) baseStart_7505047 baseEnd_7505047 := by
    simpa [prefixWord, tailWord_7505047, baseEnd_7505047] using wordTrace_append hprefix tailTrace_7505047
  have hstable : (prefixWord ++ tailWord_7505047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505047).length < 2 ^ (prefixWord ++ tailWord_7505047).sum := by decide
  have hdescent : baseEnd_7505047 < baseStart_7505047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505057 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_7505057 : Nat := 118140960795 + 7505057 * 2 ^ 59
def prefixEnd_7505057 : Nat := 4983230072969 + 3 ^ 40 * 7505057 * 2
def baseEnd_7505057 : Nat := 1284567193463516054557459

theorem tailTrace_7505057 : CollatzResearch.WordTrace tailWord_7505057 prefixEnd_7505057 1284567193463516054557459 := by
  unfold tailWord_7505057
  simp only [CollatzResearch.WordTrace]
  refine ⟨273731916771467725534449425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182487944514311817022966283 273731916771467725534449425)
  ·
    refine ⟨205298937578600794150837069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273731916771467725534449425 205298937578600794150837069)
    ·
      refine ⟨76987101591975297806563901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205298937578600794150837069 76987101591975297806563901)
      ·
        refine ⟨28870163096990736677461463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76987101591975297806563901 28870163096990736677461463)
        ·
          refine ⟨43305244645486105016192195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28870163096990736677461463 43305244645486105016192195)
          ·
            refine ⟨64957866968229157524288293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43305244645486105016192195 64957866968229157524288293)
            ·
              refine ⟨12179600056542967035804055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64957866968229157524288293 12179600056542967035804055)
              ·
                refine ⟨18269400084814450553706083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179600056542967035804055 18269400084814450553706083)
                ·
                  refine ⟨27404100127221675830559125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18269400084814450553706083 27404100127221675830559125)
                  ·
                    refine ⟨1284567193463516054557459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27404100127221675830559125 1284567193463516054557459)
                    ·
                      rfl

theorem cell23_7505057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_7505057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505057 prefixEnd_7505057 := by exact prefixLift 7505057
  have htrace : WordTrace (prefixWord ++ tailWord_7505057) baseStart_7505057 baseEnd_7505057 := by
    simpa [prefixWord, tailWord_7505057, baseEnd_7505057] using wordTrace_append hprefix tailTrace_7505057
  have hstable : (prefixWord ++ tailWord_7505057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505057).length < 2 ^ (prefixWord ++ tailWord_7505057).sum := by decide
  have hdescent : baseEnd_7505057 < baseStart_7505057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505078 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7505078 : Nat := 118140960795 + 7505078 * 2 ^ 59
def prefixEnd_7505078 : Nat := 4983230072969 + 3 ^ 40 * 7505078 * 2
def baseEnd_7505078 : Nat := 1284570787828097527169927

theorem tailTrace_7505078 : CollatzResearch.WordTrace tailWord_7505078 prefixEnd_7505078 1284570787828097527169927 := by
  unfold tailWord_7505078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108292669024477882560243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182488455136261097413975925 17108292669024477882560243)
  ·
    refine ⟨25662439003536716823840365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108292669024477882560243 25662439003536716823840365)
    ·
      refine ⟨9623414626326268808940137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25662439003536716823840365 9623414626326268808940137)
      ·
        refine ⟨7217560969744701606705103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9623414626326268808940137 7217560969744701606705103)
        ·
          refine ⟨10826341454617052410057655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217560969744701606705103 10826341454617052410057655)
          ·
            refine ⟨16239512181925578615086483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826341454617052410057655 16239512181925578615086483)
            ·
              refine ⟨24359268272888367922629725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239512181925578615086483 24359268272888367922629725)
              ·
                refine ⟨9134725602333137970986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24359268272888367922629725 9134725602333137970986147)
                ·
                  refine ⟨13702088403499706956479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134725602333137970986147 13702088403499706956479221)
                  ·
                    refine ⟨1284570787828097527169927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13702088403499706956479221 1284570787828097527169927)
                    ·
                      rfl

theorem cell23_7505078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7505078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505078 prefixEnd_7505078 := by exact prefixLift 7505078
  have htrace : WordTrace (prefixWord ++ tailWord_7505078) baseStart_7505078 baseEnd_7505078 := by
    simpa [prefixWord, tailWord_7505078, baseEnd_7505078] using wordTrace_append hprefix tailTrace_7505078
  have hstable : (prefixWord ++ tailWord_7505078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505078).length < 2 ^ (prefixWord ++ tailWord_7505078).sum := by decide
  have hdescent : baseEnd_7505078 < baseStart_7505078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505081 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7505081 : Nat := 118140960795 + 7505081 * 2 ^ 59
def prefixEnd_7505081 : Nat := 4983230072969 + 3 ^ 40 * 7505081 * 2
def baseEnd_7505081 : Nat := 3853713903926256069772267

theorem tailTrace_7505081 : CollatzResearch.WordTrace tailWord_7505081 prefixEnd_7505081 3853713903926256069772267 := by
  unfold tailWord_7505081
  simp only [CollatzResearch.WordTrace]
  refine ⟨273732792123380777633323097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182488528082253851755548731 273732792123380777633323097)
  ·
    refine ⟨205299594092535583224992323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273732792123380777633323097 205299594092535583224992323)
    ·
      refine ⟨307949391138803374837488485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205299594092535583224992323 307949391138803374837488485)
      ·
        refine ⟨57740510838525632782029091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307949391138803374837488485 57740510838525632782029091)
        ·
          refine ⟨86610766257788449173043637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57740510838525632782029091 86610766257788449173043637)
          ·
            refine ⟨8119759336667667109972841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86610766257788449173043637 8119759336667667109972841)
            ·
              refine ⟨6089819502500750332479631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119759336667667109972841 6089819502500750332479631)
              ·
                refine ⟨9134729253751125498719447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089819502500750332479631 9134729253751125498719447)
                ·
                  refine ⟨13702093880626688248079171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134729253751125498719447 13702093880626688248079171)
                  ·
                    refine ⟨20553140820940032372118757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13702093880626688248079171 20553140820940032372118757)
                    ·
                      refine ⟨3853713903926256069772267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20553140820940032372118757 3853713903926256069772267)
                      ·
                        rfl

theorem cell23_7505081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7505081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505081 prefixEnd_7505081 := by exact prefixLift 7505081
  have htrace : WordTrace (prefixWord ++ tailWord_7505081) baseStart_7505081 baseEnd_7505081 := by
    simpa [prefixWord, tailWord_7505081, baseEnd_7505081] using wordTrace_append hprefix tailTrace_7505081
  have hstable : (prefixWord ++ tailWord_7505081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505081).length < 2 ^ (prefixWord ++ tailWord_7505081).sum := by decide
  have hdescent : baseEnd_7505081 < baseStart_7505081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505098 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_7505098 : Nat := 118140960795 + 7505098 * 2 ^ 59
def prefixEnd_7505098 : Nat := 4983230072969 + 3 ^ 40 * 7505098 * 2
def baseEnd_7505098 : Nat := 3853722633097382503259689

theorem tailTrace_7505098 : CollatzResearch.WordTrace tailWord_7505098 prefixEnd_7505098 3853722633097382503259689 := by
  unfold tailWord_7505098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68433353041079797384172987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182488941442879459691127965 68433353041079797384172987)
  ·
    refine ⟨102650029561619696076259481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68433353041079797384172987 102650029561619696076259481)
    ·
      refine ⟨76987522171214772057194611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102650029561619696076259481 76987522171214772057194611)
      ·
        refine ⟨115481283256822158085791917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76987522171214772057194611 115481283256822158085791917)
        ·
          refine ⟨43305481221308309282171969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115481283256822158085791917 43305481221308309282171969)
          ·
            refine ⟨32479110915981231961628977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43305481221308309282171969 32479110915981231961628977)
            ·
              refine ⟨24359333186985923971221733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32479110915981231961628977 24359333186985923971221733)
              ·
                refine ⟨4567374972559860744604075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24359333186985923971221733 4567374972559860744604075)
                ·
                  refine ⟨6851062458839791116906113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567374972559860744604075 6851062458839791116906113)
                  ·
                    refine ⟨5138296844129843337679585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6851062458839791116906113 5138296844129843337679585)
                    ·
                      refine ⟨3853722633097382503259689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138296844129843337679585 3853722633097382503259689)
                      ·
                        rfl

theorem cell23_7505098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_7505098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505098 prefixEnd_7505098 := by exact prefixLift 7505098
  have htrace : WordTrace (prefixWord ++ tailWord_7505098) baseStart_7505098 baseEnd_7505098 := by
    simpa [prefixWord, tailWord_7505098, baseEnd_7505098] using wordTrace_append hprefix tailTrace_7505098
  have hstable : (prefixWord ++ tailWord_7505098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505098).length < 2 ^ (prefixWord ++ tailWord_7505098).sum := by decide
  have hdescent : baseEnd_7505098 < baseStart_7505098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505108 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_7505108 : Nat := 118140960795 + 7505108 * 2 ^ 59
def prefixEnd_7505108 : Nat := 4983230072969 + 3 ^ 40 * 7505108 * 2
def baseEnd_7505108 : Nat := 1284575922634642488044881

theorem tailTrace_7505108 : CollatzResearch.WordTrace tailWord_7505108 prefixEnd_7505108 1284575922634642488044881 := by
  unfold tailWord_7505108
  simp only [CollatzResearch.WordTrace]
  refine ⟨136866888447141480622277989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182489184596188640829703985 136866888447141480622277989)
  ·
    refine ⟨25662541583839027616677123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136866888447141480622277989 25662541583839027616677123)
    ·
      refine ⟨38493812375758541425015685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662541583839027616677123 38493812375758541425015685)
      ·
        refine ⟨7217589820454726517190441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38493812375758541425015685 7217589820454726517190441)
        ·
          refine ⟨5413192365341044887892831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217589820454726517190441 5413192365341044887892831)
          ·
            refine ⟨8119788548011567331839247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413192365341044887892831 8119788548011567331839247)
            ·
              refine ⟨12179682822017350997758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8119788548011567331839247 12179682822017350997758871)
              ·
                refine ⟨18269524233026026496638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179682822017350997758871 18269524233026026496638307)
                ·
                  refine ⟨27404286349539039744957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18269524233026026496638307 27404286349539039744957461)
                  ·
                    refine ⟨1284575922634642488044881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27404286349539039744957461 1284575922634642488044881)
                    ·
                      rfl

theorem cell23_7505108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_7505108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505108 prefixEnd_7505108 := by exact prefixLift 7505108
  have htrace : WordTrace (prefixWord ++ tailWord_7505108) baseStart_7505108 baseEnd_7505108 := by
    simpa [prefixWord, tailWord_7505108, baseEnd_7505108] using wordTrace_append hprefix tailTrace_7505108
  have hstable : (prefixWord ++ tailWord_7505108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505108).length < 2 ^ (prefixWord ++ tailWord_7505108).sum := by decide
  have hdescent : baseEnd_7505108 < baseStart_7505108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505124 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_7505124 : Nat := 118140960795 + 7505124 * 2 ^ 59
def prefixEnd_7505124 : Nat := 4983230072969 + 3 ^ 40 * 7505124 * 2
def baseEnd_7505124 : Nat := 3853735983594399401534569

theorem tailTrace_7505124 : CollatzResearch.WordTrace tailWord_7505124 prefixEnd_7505124 3853735983594399401534569 := by
  unfold tailWord_7505124
  simp only [CollatzResearch.WordTrace]
  refine ⟨136867180231112497988569213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182489573641483330651425617 136867180231112497988569213)
  ·
    refine ⟨51325192586667186745713455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136867180231112497988569213 51325192586667186745713455)
    ·
      refine ⟨76987788880000780118570183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51325192586667186745713455 76987788880000780118570183)
      ·
        refine ⟨115481683320001170177855275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76987788880000780118570183 115481683320001170177855275)
        ·
          refine ⟨173222524980001755266782913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115481683320001170177855275 173222524980001755266782913)
          ·
            refine ⟨129916893735001316450087185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173222524980001755266782913 129916893735001316450087185)
            ·
              refine ⟨97437670301250987337565389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129916893735001316450087185 97437670301250987337565389)
              ·
                refine ⟨36539126362969120251587021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97437670301250987337565389 36539126362969120251587021)
                ·
                  refine ⟨13702172386113420094345133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36539126362969120251587021 13702172386113420094345133)
                  ·
                    refine ⟨5138314644792532535379425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13702172386113420094345133 5138314644792532535379425)
                    ·
                      refine ⟨3853735983594399401534569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138314644792532535379425 3853735983594399401534569)
                      ·
                        rfl

theorem cell23_7505124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_7505124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505124 prefixEnd_7505124 := by exact prefixLift 7505124
  have htrace : WordTrace (prefixWord ++ tailWord_7505124) baseStart_7505124 baseEnd_7505124 := by
    simpa [prefixWord, tailWord_7505124, baseEnd_7505124] using wordTrace_append hprefix tailTrace_7505124
  have hstable : (prefixWord ++ tailWord_7505124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505124).length < 2 ^ (prefixWord ++ tailWord_7505124).sum := by decide
  have hdescent : baseEnd_7505124 < baseStart_7505124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505157 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_7505157 : Nat := 118140960795 + 7505157 * 2 ^ 59
def prefixEnd_7505157 : Nat := 4983230072969 + 3 ^ 40 * 7505157 * 2
def baseEnd_7505157 : Nat := 3853752928455997772421917

theorem tailTrace_7505157 : CollatzResearch.WordTrace tailWord_7505157 prefixEnd_7505157 3853752928455997772421917 := by
  unfold tailWord_7505157
  simp only [CollatzResearch.WordTrace]
  refine ⟨273735564071105442613089725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182490376047403628408726483 273735564071105442613089725)
  ·
    refine ⟨102650836526664540979908647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273735564071105442613089725 102650836526664540979908647)
    ·
      refine ⟨153976254789996811469862971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102650836526664540979908647 153976254789996811469862971)
      ·
        refine ⟨230964382184995217204794457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153976254789996811469862971 230964382184995217204794457)
        ·
          refine ⟨173223286638746412903595843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230964382184995217204794457 173223286638746412903595843)
          ·
            refine ⟨259834929958119619355393765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173223286638746412903595843 259834929958119619355393765)
            ·
              refine ⟨48719049367147428629136331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259834929958119619355393765 48719049367147428629136331)
              ·
                refine ⟨73078574050721142943704497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48719049367147428629136331 73078574050721142943704497)
                ·
                  refine ⟨54808930538040857207778373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73078574050721142943704497 54808930538040857207778373)
                  ·
                    refine ⟨10276674475882660726458445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54808930538040857207778373 10276674475882660726458445)
                    ·
                      refine ⟨3853752928455997772421917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276674475882660726458445 3853752928455997772421917)
                      ·
                        rfl

theorem cell23_7505157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_7505157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505157 prefixEnd_7505157 := by exact prefixLift 7505157
  have htrace : WordTrace (prefixWord ++ tailWord_7505157) baseStart_7505157 baseEnd_7505157 := by
    simpa [prefixWord, tailWord_7505157, baseEnd_7505157] using wordTrace_append hprefix tailTrace_7505157
  have hstable : (prefixWord ++ tailWord_7505157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505157).length < 2 ^ (prefixWord ++ tailWord_7505157).sum := by decide
  have hdescent : baseEnd_7505157 < baseStart_7505157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505222 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7505222 : Nat := 118140960795 + 7505222 * 2 ^ 59
def prefixEnd_7505222 : Nat := 4983230072969 + 3 ^ 40 * 7505222 * 2
def baseEnd_7505222 : Nat := 3853786304698540018109119

theorem tailTrace_7505222 : CollatzResearch.WordTrace tailWord_7505222 prefixEnd_7505222 3853786304698540018109119 := by
  unfold tailWord_7505222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554310462995936209818935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182491956543913305809470613 8554310462995936209818935)
  ·
    refine ⟨12831465694493904314728403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8554310462995936209818935 12831465694493904314728403)
    ·
      refine ⟨19247198541740856472092605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12831465694493904314728403 19247198541740856472092605)
      ·
        refine ⟨7217699453152821177034727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19247198541740856472092605 7217699453152821177034727)
        ·
          refine ⟨10826549179729231765552091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217699453152821177034727 10826549179729231765552091)
          ·
            refine ⟨16239823769593847648328137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826549179729231765552091 16239823769593847648328137)
            ·
              refine ⟨12179867827195385736246103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16239823769593847648328137 12179867827195385736246103)
              ·
                refine ⟨18269801740793078604369155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12179867827195385736246103 18269801740793078604369155)
                ·
                  refine ⟨27404702611189617906553733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18269801740793078604369155 27404702611189617906553733)
                  ·
                    refine ⟨5138381739598053357478825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27404702611189617906553733 5138381739598053357478825)
                    ·
                      refine ⟨3853786304698540018109119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138381739598053357478825 3853786304698540018109119)
                      ·
                        rfl

theorem cell23_7505222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7505222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505222 prefixEnd_7505222 := by exact prefixLift 7505222
  have htrace : WordTrace (prefixWord ++ tailWord_7505222) baseStart_7505222 baseEnd_7505222 := by
    simpa [prefixWord, tailWord_7505222, baseEnd_7505222] using wordTrace_append hprefix tailTrace_7505222
  have hstable : (prefixWord ++ tailWord_7505222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505222).length < 2 ^ (prefixWord ++ tailWord_7505222).sum := by decide
  have hdescent : baseEnd_7505222 < baseStart_7505222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505261 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_7505261 : Nat := 118140960795 + 7505261 * 2 ^ 59
def prefixEnd_7505261 : Nat := 4983230072969 + 3 ^ 40 * 7505261 * 2
def baseEnd_7505261 : Nat := 3853806330444065365521439

theorem tailTrace_7505261 : CollatzResearch.WordTrace tailWord_7505261 prefixEnd_7505261 3853806330444065365521439 := by
  unfold tailWord_7505261
  simp only [CollatzResearch.WordTrace]
  refine ⟨273739357262728668374875637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182492904841819112249917091 273739357262728668374875637)
  ·
    refine ⟨25663064743380812660144591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273739357262728668374875637 25663064743380812660144591)
    ·
      refine ⟨38494597115071218990216887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25663064743380812660144591 38494597115071218990216887)
      ·
        refine ⟨57741895672606828485325331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38494597115071218990216887 57741895672606828485325331)
        ·
          refine ⟨86612843508910242727987997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57741895672606828485325331 86612843508910242727987997)
          ·
            refine ⟨32479816315841341022995499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86612843508910242727987997 32479816315841341022995499)
            ·
              refine ⟨48719724473762011534493249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32479816315841341022995499 48719724473762011534493249)
              ·
                refine ⟨36539793355321508650869937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48719724473762011534493249 36539793355321508650869937)
                ·
                  refine ⟨27404845016491131488152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36539793355321508650869937 27404845016491131488152453)
                  ·
                    refine ⟨5138408440592087154028585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27404845016491131488152453 5138408440592087154028585)
                    ·
                      refine ⟨3853806330444065365521439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138408440592087154028585 3853806330444065365521439)
                      ·
                        rfl

theorem cell23_7505261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_7505261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505261 prefixEnd_7505261 := by exact prefixLift 7505261
  have htrace : WordTrace (prefixWord ++ tailWord_7505261) baseStart_7505261 baseEnd_7505261 := by
    simpa [prefixWord, tailWord_7505261, baseEnd_7505261] using wordTrace_append hprefix tailTrace_7505261
  have hstable : (prefixWord ++ tailWord_7505261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505261).length < 2 ^ (prefixWord ++ tailWord_7505261).sum := by decide
  have hdescent : baseEnd_7505261 < baseStart_7505261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505264 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3]
def baseStart_7505264 : Nat := 118140960795 + 7505264 * 2 ^ 59
def prefixEnd_7505264 : Nat := 4983230072969 + 3 ^ 40 * 7505264 * 2
def baseEnd_7505264 : Nat := 3853807870886028853783925

theorem tailTrace_7505264 : CollatzResearch.WordTrace tailWord_7505264 prefixEnd_7505264 3853807870886028853783925 := by
  unfold tailWord_7505264
  simp only [CollatzResearch.WordTrace]
  refine ⟨136869733340858899943617423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182492977787811866591489897 136869733340858899943617423)
  ·
    refine ⟨205304600011288349915426135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136869733340858899943617423 205304600011288349915426135)
    ·
      refine ⟨307956900016932524873139203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205304600011288349915426135 307956900016932524873139203)
      ·
        refine ⟨461935350025398787309708805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307956900016932524873139203 461935350025398787309708805)
        ·
          refine ⟨86612878129762272620570401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 461935350025398787309708805 86612878129762272620570401)
          ·
            refine ⟨64959658597321704465427801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86612878129762272620570401 64959658597321704465427801)
            ·
              refine ⟨48719743947991278349070851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64959658597321704465427801 48719743947991278349070851)
              ·
                refine ⟨73079615921986917523606277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48719743947991278349070851 73079615921986917523606277)
                ·
                  refine ⟨13702427985372547035676177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73079615921986917523606277 13702427985372547035676177)
                  ·
                    refine ⟨10276820989029410276757133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13702427985372547035676177 10276820989029410276757133)
                    ·
                      refine ⟨3853807870886028853783925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10276820989029410276757133 3853807870886028853783925)
                      ·
                        rfl

theorem cell23_7505264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 3].length) (baseStart_7505264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505264 prefixEnd_7505264 := by exact prefixLift 7505264
  have htrace : WordTrace (prefixWord ++ tailWord_7505264) baseStart_7505264 baseEnd_7505264 := by
    simpa [prefixWord, tailWord_7505264, baseEnd_7505264] using wordTrace_append hprefix tailTrace_7505264
  have hstable : (prefixWord ++ tailWord_7505264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505264).length < 2 ^ (prefixWord ++ tailWord_7505264).sum := by decide
  have hdescent : baseEnd_7505264 < baseStart_7505264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505271 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 1, 4]
def baseStart_7505271 : Nat := 118140960795 + 7505271 * 2 ^ 59
def prefixEnd_7505271 : Nat := 4983230072969 + 3 ^ 40 * 7505271 * 2
def baseEnd_7505271 : Nat := 1284603821750203442132131

theorem tailTrace_7505271 : CollatzResearch.WordTrace tailWord_7505271 prefixEnd_7505271 1284603821750203442132131 := by
  unfold tailWord_7505271
  simp only [CollatzResearch.WordTrace]
  refine ⟨273739721992692440082739667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182493147995128293388493111 273739721992692440082739667)
  ·
    refine ⟨410609582989038660124109501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273739721992692440082739667 410609582989038660124109501)
    ·
      refine ⟨153978593620889497546541063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410609582989038660124109501 153978593620889497546541063)
      ·
        refine ⟨230967890431334246319811595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153978593620889497546541063 230967890431334246319811595)
        ·
          refine ⟨346451835647001369479717393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230967890431334246319811595 346451835647001369479717393)
          ·
            refine ⟨259838876735251027109788045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346451835647001369479717393 259838876735251027109788045)
            ·
              refine ⟨97439578775719135166170517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259838876735251027109788045 97439578775719135166170517)
              ·
                refine ⟨4567480255111834460914243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97439578775719135166170517 4567480255111834460914243)
                ·
                  refine ⟨6851220382667751691371365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567480255111834460914243 6851220382667751691371365)
                  ·
                    refine ⟨1284603821750203442132131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6851220382667751691371365 1284603821750203442132131)
                    ·
                      rfl

theorem cell23_7505271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_7505271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505271 prefixEnd_7505271 := by exact prefixLift 7505271
  have htrace : WordTrace (prefixWord ++ tailWord_7505271) baseStart_7505271 baseEnd_7505271 := by
    simpa [prefixWord, tailWord_7505271, baseEnd_7505271] using wordTrace_append hprefix tailTrace_7505271
  have hstable : (prefixWord ++ tailWord_7505271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505271).length < 2 ^ (prefixWord ++ tailWord_7505271).sum := by decide
  have hdescent : baseEnd_7505271 < baseStart_7505271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505348 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7505348 : Nat := 118140960795 + 7505348 * 2 ^ 59
def prefixEnd_7505348 : Nat := 4983230072969 + 3 ^ 40 * 7505348 * 2
def baseEnd_7505348 : Nat := 1284617001087002175044513

theorem tailTrace_7505348 : CollatzResearch.WordTrace tailWord_7505348 prefixEnd_7505348 1284617001087002175044513 := by
  unfold tailWord_7505348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136871265206706741116646349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182495020275608988155528465 136871265206706741116646349)
  ·
    refine ⟨51326724452515027918742381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136871265206706741116646349 51326724452515027918742381)
    ·
      refine ⟨19247521669693135469528393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51326724452515027918742381 19247521669693135469528393)
      ·
        refine ⟨14435641252269851602146295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19247521669693135469528393 14435641252269851602146295)
        ·
          refine ⟨21653461878404777403219443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14435641252269851602146295 21653461878404777403219443)
          ·
            refine ⟨32480192817607166104829165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21653461878404777403219443 32480192817607166104829165)
            ·
              refine ⟨12180072306602687289310937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32480192817607166104829165 12180072306602687289310937)
              ·
                refine ⟨9135054229952015466983203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12180072306602687289310937 9135054229952015466983203)
                ·
                  refine ⟨13702581344928023200474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9135054229952015466983203 13702581344928023200474805)
                  ·
                    refine ⟨1284617001087002175044513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13702581344928023200474805 1284617001087002175044513)
                    ·
                      rfl

theorem cell23_7505348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7505348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505348 prefixEnd_7505348 := by exact prefixLift 7505348
  have htrace : WordTrace (prefixWord ++ tailWord_7505348) baseStart_7505348 baseEnd_7505348 := by
    simpa [prefixWord, tailWord_7505348, baseEnd_7505348] using wordTrace_append hprefix tailTrace_7505348
  have hstable : (prefixWord ++ tailWord_7505348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505348).length < 2 ^ (prefixWord ++ tailWord_7505348).sum := by decide
  have hdescent : baseEnd_7505348 < baseStart_7505348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505398 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7505398 : Nat := 118140960795 + 7505398 * 2 ^ 59
def prefixEnd_7505398 : Nat := 4983230072969 + 3 ^ 40 * 7505398 * 2
def baseEnd_7505398 : Nat := 3853876677293731329508309

theorem tailTrace_7505398 : CollatzResearch.WordTrace tailWord_7505398 prefixEnd_7505398 3853876677293731329508309 := by
  unfold tailWord_7505398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109022128952021298288303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182496236042154893848408565 17109022128952021298288303)
  ·
    refine ⟨25663533193428031947432455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17109022128952021298288303 25663533193428031947432455)
    ·
      refine ⟨38495299790142047921148683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25663533193428031947432455 38495299790142047921148683)
      ·
        refine ⟨57742949685213071881723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38495299790142047921148683 57742949685213071881723025)
        ·
          refine ⟨43307212263909803911292269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57742949685213071881723025 43307212263909803911292269)
          ·
            refine ⟨16240204598966176466734601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43307212263909803911292269 16240204598966176466734601)
            ·
              refine ⟨12180153449224632350050951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16240204598966176466734601 12180153449224632350050951)
              ·
                refine ⟨18270230173836948525076427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12180153449224632350050951 18270230173836948525076427)
                ·
                  refine ⟨27405345260755422787614641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18270230173836948525076427 27405345260755422787614641)
                  ·
                    refine ⟨20554008945566567090710981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27405345260755422787614641 20554008945566567090710981)
                    ·
                      refine ⟨3853876677293731329508309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20554008945566567090710981 3853876677293731329508309)
                      ·
                        rfl

theorem cell23_7505398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7505398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505398 prefixEnd_7505398 := by exact prefixLift 7505398
  have htrace : WordTrace (prefixWord ++ tailWord_7505398) baseStart_7505398 baseEnd_7505398 := by
    simpa [prefixWord, tailWord_7505398, baseEnd_7505398] using wordTrace_append hprefix tailTrace_7505398
  have hstable : (prefixWord ++ tailWord_7505398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505398).length < 2 ^ (prefixWord ++ tailWord_7505398).sum := by decide
  have hdescent : baseEnd_7505398 < baseStart_7505398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505401 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_7505401 : Nat := 118140960795 + 7505401 * 2 ^ 59
def prefixEnd_7505401 : Nat := 4983230072969 + 3 ^ 40 * 7505401 * 2
def baseEnd_7505401 : Nat := 3853878217735694817770795

theorem tailTrace_7505401 : CollatzResearch.WordTrace tailWord_7505401 prefixEnd_7505401 3853878217735694817770795 := by
  unfold tailWord_7505401
  simp only [CollatzResearch.WordTrace]
  refine ⟨273744463482221472284972057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182496308988147648189981371 273744463482221472284972057)
  ·
    refine ⟨205308347611666104213729043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273744463482221472284972057 205308347611666104213729043)
    ·
      refine ⟨307962521417499156320593565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205308347611666104213729043 307962521417499156320593565)
      ·
        refine ⟨115485945531562183620222587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307962521417499156320593565 115485945531562183620222587)
        ·
          refine ⟨173228918297343275430333881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115485945531562183620222587 173228918297343275430333881)
          ·
            refine ⟨129921688723007456572750411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173228918297343275430333881 129921688723007456572750411)
            ·
              refine ⟨194882533084511184859125617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129921688723007456572750411 194882533084511184859125617)
              ·
                refine ⟨146161899813383388644344213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194882533084511184859125617 146161899813383388644344213)
                ·
                  refine ⟨6851339053752346342703635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146161899813383388644344213 6851339053752346342703635)
                  ·
                    refine ⟨10277008580628519514055453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851339053752346342703635 10277008580628519514055453)
                    ·
                      refine ⟨3853878217735694817770795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277008580628519514055453 3853878217735694817770795)
                      ·
                        rfl

theorem cell23_7505401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_7505401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505401 prefixEnd_7505401 := by exact prefixLift 7505401
  have htrace : WordTrace (prefixWord ++ tailWord_7505401) baseStart_7505401 baseEnd_7505401 := by
    simpa [prefixWord, tailWord_7505401, baseEnd_7505401] using wordTrace_append hprefix tailTrace_7505401
  have hstable : (prefixWord ++ tailWord_7505401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505401).length < 2 ^ (prefixWord ++ tailWord_7505401).sum := by decide
  have hdescent : baseEnd_7505401 < baseStart_7505401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505422 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7505422 : Nat := 118140960795 + 7505422 * 2 ^ 59
def prefixEnd_7505422 : Nat := 4983230072969 + 3 ^ 40 * 7505422 * 2
def baseEnd_7505422 : Nat := 3853889000829439235608199

theorem tailTrace_7505422 : CollatzResearch.WordTrace tailWord_7505422 prefixEnd_7505422 3853889000829439235608199 := by
  unfold tailWord_7505422
  simp only [CollatzResearch.WordTrace]
  refine ⟨34218153676893174108935815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182496819610096928580991013 34218153676893174108935815)
  ·
    refine ⟨51327230515339761163403723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34218153676893174108935815 51327230515339761163403723)
    ·
      refine ⟨76990845773009641745105585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51327230515339761163403723 76990845773009641745105585)
      ·
        refine ⟨57743134329757231308829189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76990845773009641745105585 57743134329757231308829189)
        ·
          refine ⟨10826837686829480870405473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57743134329757231308829189 10826837686829480870405473)
          ·
            refine ⟨8120128265122110652804105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10826837686829480870405473 8120128265122110652804105)
            ·
              refine ⟨6090096198841582989603079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120128265122110652804105 6090096198841582989603079)
              ·
                refine ⟨9135144298262374484404619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090096198841582989603079 9135144298262374484404619)
                ·
                  refine ⟨13702716447393561726606929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9135144298262374484404619 13702716447393561726606929)
                  ·
                    refine ⟨10277037335545171294955197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13702716447393561726606929 10277037335545171294955197)
                    ·
                      refine ⟨3853889000829439235608199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277037335545171294955197 3853889000829439235608199)
                      ·
                        rfl

theorem cell23_7505422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7505422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505422 prefixEnd_7505422 := by exact prefixLift 7505422
  have htrace : WordTrace (prefixWord ++ tailWord_7505422) baseStart_7505422 baseEnd_7505422 := by
    simpa [prefixWord, tailWord_7505422, baseEnd_7505422] using wordTrace_append hprefix tailTrace_7505422
  have hstable : (prefixWord ++ tailWord_7505422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505422).length < 2 ^ (prefixWord ++ tailWord_7505422).sum := by decide
  have hdescent : baseEnd_7505422 < baseStart_7505422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505509 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 2, 2, 2]
def baseStart_7505509 : Nat := 118140960795 + 7505509 * 2 ^ 59
def prefixEnd_7505509 : Nat := 4983230072969 + 3 ^ 40 * 7505509 * 2
def baseEnd_7505509 : Nat := 3853933673646380395220299

theorem tailTrace_7505509 : CollatzResearch.WordTrace tailWord_7505509 prefixEnd_7505509 3853933673646380395220299 := by
  unfold tailWord_7505509
  simp only [CollatzResearch.WordTrace]
  refine ⟨273748402565830206729903581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182498935043886804486602387 273748402565830206729903581)
  ·
    refine ⟨102655650962186327523713843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273748402565830206729903581 102655650962186327523713843)
    ·
      refine ⟨153983476443279491285570765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102655650962186327523713843 153983476443279491285570765)
      ·
        refine ⟨57743803666229809232089037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153983476443279491285570765 57743803666229809232089037)
        ·
          refine ⟨21653926374836178462033389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57743803666229809232089037 21653926374836178462033389)
          ·
            refine ⟨8120222390563566923262521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21653926374836178462033389 8120222390563566923262521)
            ·
              refine ⟨6090166792922675192446891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120222390563566923262521 6090166792922675192446891)
              ·
                refine ⟨9135250189384012788670337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090166792922675192446891 9135250189384012788670337)
                ·
                  refine ⟨6851437642038009591502753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9135250189384012788670337 6851437642038009591502753)
                  ·
                    refine ⟨5138578231528507193627065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6851437642038009591502753 5138578231528507193627065)
                    ·
                      refine ⟨3853933673646380395220299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138578231528507193627065 3853933673646380395220299)
                      ·
                        rfl

theorem cell23_7505509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_7505509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505509 prefixEnd_7505509 := by exact prefixLift 7505509
  have htrace : WordTrace (prefixWord ++ tailWord_7505509) baseStart_7505509 baseEnd_7505509 := by
    simpa [prefixWord, tailWord_7505509, baseEnd_7505509] using wordTrace_append hprefix tailTrace_7505509
  have hstable : (prefixWord ++ tailWord_7505509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505509).length < 2 ^ (prefixWord ++ tailWord_7505509).sum := by decide
  have hdescent : baseEnd_7505509 < baseStart_7505509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505548 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_7505548 : Nat := 118140960795 + 7505548 * 2 ^ 59
def prefixEnd_7505548 : Nat := 4983230072969 + 3 ^ 40 * 7505548 * 2
def baseEnd_7505548 : Nat := 3853953699391905742632619

theorem tailTrace_7505548 : CollatzResearch.WordTrace tailWord_7505548 prefixEnd_7505548 3853953699391905742632619 := by
  unfold tailWord_7505548
  simp only [CollatzResearch.WordTrace]
  refine ⟨136874912506344458195286649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182499883341792610927048865 136874912506344458195286649)
  ·
    refine ⟨102656184379758343646464987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136874912506344458195286649 102656184379758343646464987)
    ·
      refine ⟨153984276569637515469697481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102656184379758343646464987 153984276569637515469697481)
      ·
        refine ⟨115488207427228136602273111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153984276569637515469697481 115488207427228136602273111)
        ·
          refine ⟨173232311140842204903409667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115488207427228136602273111 173232311140842204903409667)
          ·
            refine ⟨259848466711263307355114501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173232311140842204903409667 259848466711263307355114501)
            ·
              refine ⟨48721587508361870129083969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259848466711263307355114501 48721587508361870129083969)
              ·
                refine ⟨36541190631271402596812977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48721587508361870129083969 36541190631271402596812977)
                ·
                  refine ⟨27405892973453551947609733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36541190631271402596812977 27405892973453551947609733)
                  ·
                    refine ⟨5138604932522540990176825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27405892973453551947609733 5138604932522540990176825)
                    ·
                      refine ⟨3853953699391905742632619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138604932522540990176825 3853953699391905742632619)
                      ·
                        rfl

theorem cell23_7505548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_7505548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505548 prefixEnd_7505548 := by exact prefixLift 7505548
  have htrace : WordTrace (prefixWord ++ tailWord_7505548) baseStart_7505548 baseEnd_7505548 := by
    simpa [prefixWord, tailWord_7505548, baseEnd_7505548] using wordTrace_append hprefix tailTrace_7505548
  have hstable : (prefixWord ++ tailWord_7505548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505548).length < 2 ^ (prefixWord ++ tailWord_7505548).sum := by decide
  have hdescent : baseEnd_7505548 < baseStart_7505548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505571 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 6]
def baseStart_7505571 : Nat := 118140960795 + 7505571 * 2 ^ 59
def prefixEnd_7505571 : Nat := 4983230072969 + 3 ^ 40 * 7505571 * 2
def baseEnd_7505571 : Nat := 428218389938551016960557

theorem tailTrace_7505571 : CollatzResearch.WordTrace tailWord_7505571 prefixEnd_7505571 428218389938551016960557 := by
  unfold tailWord_7505571
  simp only [CollatzResearch.WordTrace]
  refine ⟨273750663891605591318660567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182500442594403727545773711 273750663891605591318660567)
  ·
    refine ⟨410625995837408386977990851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273750663891605591318660567 410625995837408386977990851)
    ·
      refine ⟨615938993756112580466986277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410625995837408386977990851 615938993756112580466986277)
      ·
        refine ⟨115488561329271108837559927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615938993756112580466986277 115488561329271108837559927)
        ·
          refine ⟨173232841993906663256339891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115488561329271108837559927 173232841993906663256339891)
          ·
            refine ⟨259849262990859994884509837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173232841993906663256339891 259849262990859994884509837)
            ·
              refine ⟨97443473621572498081691189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259849262990859994884509837 97443473621572498081691189)
              ·
                refine ⟨9135325652022421695158549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97443473621572498081691189 9135325652022421695158549)
                ·
                  refine ⟨428218389938551016960557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9135325652022421695158549 428218389938551016960557)
                  ·
                    rfl

theorem cell23_7505571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 6].length) (baseStart_7505571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505571 prefixEnd_7505571 := by exact prefixLift 7505571
  have htrace : WordTrace (prefixWord ++ tailWord_7505571) baseStart_7505571 baseEnd_7505571 := by
    simpa [prefixWord, tailWord_7505571, baseEnd_7505571] using wordTrace_append hprefix tailTrace_7505571
  have hstable : (prefixWord ++ tailWord_7505571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505571).length < 2 ^ (prefixWord ++ tailWord_7505571).sum := by decide
  have hdescent : baseEnd_7505571 < baseStart_7505571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_7505641 : Nat := 118140960795 + 7505641 * 2 ^ 59
def prefixEnd_7505641 : Nat := 4983230072969 + 3 ^ 40 * 7505641 * 2
def baseEnd_7505641 : Nat := 3854001453092773878769691

theorem tailTrace_7505641 : CollatzResearch.WordTrace tailWord_7505641 prefixEnd_7505641 3854001453092773878769691 := by
  unfold tailWord_7505641
  simp only [CollatzResearch.WordTrace]
  refine ⟨273753217001351993273708777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182502144667567995515805851 273753217001351993273708777)
  ·
    refine ⟨205314912751013994955281583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273753217001351993273708777 205314912751013994955281583)
    ·
      refine ⟨307972369126520992432922375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205314912751013994955281583 307972369126520992432922375)
      ·
        refine ⟨461958553689781488649383563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307972369126520992432922375 461958553689781488649383563)
        ·
          refine ⟨692937830534672232974075345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461958553689781488649383563 692937830534672232974075345)
          ·
            refine ⟨519703372901004174730556509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692937830534672232974075345 519703372901004174730556509)
            ·
              refine ⟨194888764837876565523958691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519703372901004174730556509 194888764837876565523958691)
              ·
                refine ⟨292333147256814848285938037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194888764837876565523958691 292333147256814848285938037)
                ·
                  refine ⟨27406232555326392026806691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292333147256814848285938037 27406232555326392026806691)
                  ·
                    refine ⟨41109348832989588040210037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27406232555326392026806691 41109348832989588040210037)
                    ·
                      refine ⟨3854001453092773878769691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41109348832989588040210037 3854001453092773878769691)
                      ·
                        rfl

theorem cell23_7505641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_7505641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505641 prefixEnd_7505641 := by exact prefixLift 7505641
  have htrace : WordTrace (prefixWord ++ tailWord_7505641) baseStart_7505641 baseEnd_7505641 := by
    simpa [prefixWord, tailWord_7505641, baseEnd_7505641] using wordTrace_append hprefix tailTrace_7505641
  have hstable : (prefixWord ++ tailWord_7505641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505641).length < 2 ^ (prefixWord ++ tailWord_7505641).sum := by decide
  have hdescent : baseEnd_7505641 < baseStart_7505641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505649 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_7505649 : Nat := 118140960795 + 7505649 * 2 ^ 59
def prefixEnd_7505649 : Nat := 4983230072969 + 3 ^ 40 * 7505649 * 2
def baseEnd_7505649 : Nat := 3854005560938009847469655

theorem tailTrace_7505649 : CollatzResearch.WordTrace tailWord_7505649 prefixEnd_7505649 3854005560938009847469655 := by
  unfold tailWord_7505649
  simp only [CollatzResearch.WordTrace]
  refine ⟨273753508785323010640000001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182502339190215340426666667 273753508785323010640000001)
  ·
    refine ⟨205315131588992257980000001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273753508785323010640000001 205315131588992257980000001)
    ·
      refine ⟨153986348691744193485000001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205315131588992257980000001 153986348691744193485000001)
      ·
        refine ⟨115489761518808145113750001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153986348691744193485000001 115489761518808145113750001)
        ·
          refine ⟨86617321139106108835312501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115489761518808145113750001 86617321139106108835312501)
          ·
            refine ⟨8120373856791197703310547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86617321139106108835312501 8120373856791197703310547)
            ·
              refine ⟨12180560785186796554965821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8120373856791197703310547 12180560785186796554965821)
              ·
                refine ⟨4567710294445048708112183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12180560785186796554965821 4567710294445048708112183)
                ·
                  refine ⟨6851565441667573062168275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567710294445048708112183 6851565441667573062168275)
                  ·
                    refine ⟨10277348162501359593252413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851565441667573062168275 10277348162501359593252413)
                    ·
                      refine ⟨3854005560938009847469655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277348162501359593252413 3854005560938009847469655)
                      ·
                        rfl

theorem cell23_7505649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_7505649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505649 prefixEnd_7505649 := by exact prefixLift 7505649
  have htrace : WordTrace (prefixWord ++ tailWord_7505649) baseStart_7505649 baseEnd_7505649 := by
    simpa [prefixWord, tailWord_7505649, baseEnd_7505649] using wordTrace_append hprefix tailTrace_7505649
  have hstable : (prefixWord ++ tailWord_7505649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505649).length < 2 ^ (prefixWord ++ tailWord_7505649).sum := by decide
  have hdescent : baseEnd_7505649 < baseStart_7505649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505655 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_7505655 : Nat := 118140960795 + 7505655 * 2 ^ 59
def prefixEnd_7505655 : Nat := 4983230072969 + 3 ^ 40 * 7505655 * 2
def baseEnd_7505655 : Nat := 3854008641821936823994627

theorem tailTrace_7505655 : CollatzResearch.WordTrace tailWord_7505655 prefixEnd_7505655 3854008641821936823994627 := by
  unfold tailWord_7505655
  simp only [CollatzResearch.WordTrace]
  refine ⟨273753727623301273664718419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182502485082200849109812279 273753727623301273664718419)
  ·
    refine ⟨410630591434951910497077629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273753727623301273664718419 410630591434951910497077629)
    ·
      refine ⟨153986471788106966436404111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410630591434951910497077629 153986471788106966436404111)
      ·
        refine ⟨230979707682160449654606167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153986471788106966436404111 230979707682160449654606167)
        ·
          refine ⟨346469561523240674481909251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230979707682160449654606167 346469561523240674481909251)
          ·
            refine ⟨519704342284861011722863877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346469561523240674481909251 519704342284861011722863877)
            ·
              refine ⟨97444564178411439698036977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 519704342284861011722863877 97444564178411439698036977)
              ·
                refine ⟨73083423133808579773527733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97444564178411439698036977 73083423133808579773527733)
                ·
                  refine ⟨6851570918794554353768225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73083423133808579773527733 6851570918794554353768225)
                  ·
                    refine ⟨5138678189095915765326169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6851570918794554353768225 5138678189095915765326169)
                    ·
                      refine ⟨3854008641821936823994627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138678189095915765326169 3854008641821936823994627)
                      ·
                        rfl

theorem cell23_7505655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_7505655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505655 prefixEnd_7505655 := by exact prefixLift 7505655
  have htrace : WordTrace (prefixWord ++ tailWord_7505655) baseStart_7505655 baseEnd_7505655 := by
    simpa [prefixWord, tailWord_7505655, baseEnd_7505655] using wordTrace_append hprefix tailTrace_7505655
  have hstable : (prefixWord ++ tailWord_7505655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505655).length < 2 ^ (prefixWord ++ tailWord_7505655).sum := by decide
  have hdescent : baseEnd_7505655 < baseStart_7505655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505658 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_7505658 : Nat := 118140960795 + 7505658 * 2 ^ 59
def prefixEnd_7505658 : Nat := 4983230072969 + 3 ^ 40 * 7505658 * 2
def baseEnd_7505658 : Nat := 3854010182263900312257113

theorem tailTrace_7505658 : CollatzResearch.WordTrace tailWord_7505658 prefixEnd_7505658 3854010182263900312257113 := by
  unfold tailWord_7505658
  simp only [CollatzResearch.WordTrace]
  refine ⟨68438459260572601294269407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182502558028193603451385085 68438459260572601294269407)
  ·
    refine ⟨102657688890858901941404111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68438459260572601294269407 102657688890858901941404111)
    ·
      refine ⟨153986533336288352912106167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102657688890858901941404111 153986533336288352912106167)
      ·
        refine ⟨230979800004432529368159251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153986533336288352912106167 230979800004432529368159251)
        ·
          refine ⟨346469700006648794052238877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230979800004432529368159251 346469700006648794052238877)
          ·
            refine ⟨129926137502493297769589579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346469700006648794052238877 129926137502493297769589579)
            ·
              refine ⟨194889206253739946654384369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129926137502493297769589579 194889206253739946654384369)
              ·
                refine ⟨146166904690304959990788277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194889206253739946654384369 146166904690304959990788277)
                ·
                  refine ⟨13703147314716089999136401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146166904690304959990788277 13703147314716089999136401)
                  ·
                    refine ⟨10277360486037067499352301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13703147314716089999136401 10277360486037067499352301)
                    ·
                      refine ⟨3854010182263900312257113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277360486037067499352301 3854010182263900312257113)
                      ·
                        rfl

theorem cell23_7505658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_7505658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505658 prefixEnd_7505658 := by exact prefixLift 7505658
  have htrace : WordTrace (prefixWord ++ tailWord_7505658) baseStart_7505658 baseEnd_7505658 := by
    simpa [prefixWord, tailWord_7505658, baseEnd_7505658] using wordTrace_append hprefix tailTrace_7505658
  have hstable : (prefixWord ++ tailWord_7505658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505658).length < 2 ^ (prefixWord ++ tailWord_7505658).sum := by decide
  have hdescent : baseEnd_7505658 < baseStart_7505658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505666 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_7505666 : Nat := 118140960795 + 7505666 * 2 ^ 59
def prefixEnd_7505666 : Nat := 4983230072969 + 3 ^ 40 * 7505666 * 2
def baseEnd_7505666 : Nat := 3854014290109136280957077

theorem tailTrace_7505666 : CollatzResearch.WordTrace tailWord_7505666 prefixEnd_7505666 3854014290109136280957077 := by
  unfold tailWord_7505666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68438532206565355635842213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182502752550840948362245901 68438532206565355635842213)
  ·
    refine ⟨12832224788731004181720415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68438532206565355635842213 12832224788731004181720415)
    ·
      refine ⟨19248337183096506272580623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832224788731004181720415 19248337183096506272580623)
      ·
        refine ⟨28872505774644759408870935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19248337183096506272580623 28872505774644759408870935)
        ·
          refine ⟨43308758661967139113306403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28872505774644759408870935 43308758661967139113306403)
          ·
            refine ⟨64963137992950708669959605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43308758661967139113306403 64963137992950708669959605)
            ·
              refine ⟨6090294186839128937808713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64963137992950708669959605 6090294186839128937808713)
              ·
                refine ⟨4567720640129346703356535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090294186839128937808713 4567720640129346703356535)
                ·
                  refine ⟨6851580960194020055034803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567720640129346703356535 6851580960194020055034803)
                  ·
                    refine ⟨10277371440291030082552205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851580960194020055034803 10277371440291030082552205)
                    ·
                      refine ⟨3854014290109136280957077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277371440291030082552205 3854014290109136280957077)
                      ·
                        rfl

theorem cell23_7505666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_7505666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505666 prefixEnd_7505666 := by exact prefixLift 7505666
  have htrace : WordTrace (prefixWord ++ tailWord_7505666) baseStart_7505666 baseEnd_7505666 := by
    simpa [prefixWord, tailWord_7505666, baseEnd_7505666] using wordTrace_append hprefix tailTrace_7505666
  have hstable : (prefixWord ++ tailWord_7505666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505666).length < 2 ^ (prefixWord ++ tailWord_7505666).sum := by decide
  have hdescent : baseEnd_7505666 < baseStart_7505666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505668 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7505668 : Nat := 118140960795 + 7505668 * 2 ^ 59
def prefixEnd_7505668 : Nat := 4983230072969 + 3 ^ 40 * 7505668 * 2
def baseEnd_7505668 : Nat := 3854015317070445273132067

theorem tailTrace_7505668 : CollatzResearch.WordTrace tailWord_7505668 prefixEnd_7505668 3854015317070445273132067 := by
  unfold tailWord_7505668
  simp only [CollatzResearch.WordTrace]
  refine ⟨136877100886127088442470829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182502801181502784589961105 136877100886127088442470829)
  ·
    refine ⟨51328912832297658165926561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136877100886127088442470829 51328912832297658165926561)
    ·
      refine ⟨38496684624223243624444921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51328912832297658165926561 38496684624223243624444921)
      ·
        refine ⟨28872513468167432718333691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38496684624223243624444921 28872513468167432718333691)
        ·
          refine ⟨43308770202251149077500537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28872513468167432718333691 43308770202251149077500537)
          ·
            refine ⟨32481577651688361808125403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43308770202251149077500537 32481577651688361808125403)
            ·
              refine ⟨48722366477532542712188105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32481577651688361808125403 48722366477532542712188105)
              ·
                refine ⟨36541774858149407034141079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48722366477532542712188105 36541774858149407034141079)
                ·
                  refine ⟨54812662287224110551211619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36541774858149407034141079 54812662287224110551211619)
                  ·
                    refine ⟨82218993430836165826817429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54812662287224110551211619 82218993430836165826817429)
                    ·
                      refine ⟨3854015317070445273132067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82218993430836165826817429 3854015317070445273132067)
                      ·
                        rfl

theorem cell23_7505668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7505668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505668 prefixEnd_7505668 := by exact prefixLift 7505668
  have htrace : WordTrace (prefixWord ++ tailWord_7505668) baseStart_7505668 baseEnd_7505668 := by
    simpa [prefixWord, tailWord_7505668, baseEnd_7505668] using wordTrace_append hprefix tailTrace_7505668
  have hstable : (prefixWord ++ tailWord_7505668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505668).length < 2 ^ (prefixWord ++ tailWord_7505668).sum := by decide
  have hdescent : baseEnd_7505668 < baseStart_7505668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7505681 : Nat := 118140960795 + 7505681 * 2 ^ 59
def prefixEnd_7505681 : Nat := 4983230072969 + 3 ^ 40 * 7505681 * 2
def baseEnd_7505681 : Nat := 3854021992318953722269507

theorem tailTrace_7505681 : CollatzResearch.WordTrace tailWord_7505681 prefixEnd_7505681 3854021992318953722269507 := by
  unfold tailWord_7505681
  simp only [CollatzResearch.WordTrace]
  refine ⟨273754675921207080105164897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182503117280804720070109931 273754675921207080105164897)
  ·
    refine ⟨205316006940905310078873673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273754675921207080105164897 205316006940905310078873673)
    ·
      refine ⟨153987005205678982559155255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205316006940905310078873673 153987005205678982559155255)
      ·
        refine ⟨230980507808518473838732883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153987005205678982559155255 230980507808518473838732883)
        ·
          refine ⟨346470761712777710758099325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230980507808518473838732883 346470761712777710758099325)
          ·
            refine ⟨129926535642291641534287247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346470761712777710758099325 129926535642291641534287247)
            ·
              refine ⟨194889803463437462301430871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129926535642291641534287247 194889803463437462301430871)
              ·
                refine ⟨292334705195156193452146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194889803463437462301430871 292334705195156193452146307)
                ·
                  refine ⟨438502057792734290178219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292334705195156193452146307 438502057792734290178219461)
                  ·
                    refine ⟨82219135836137679408416149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438502057792734290178219461 82219135836137679408416149)
                    ·
                      refine ⟨3854021992318953722269507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82219135836137679408416149 3854021992318953722269507)
                      ·
                        rfl

theorem cell23_7505681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7505681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505681 prefixEnd_7505681 := by exact prefixLift 7505681
  have htrace : WordTrace (prefixWord ++ tailWord_7505681) baseStart_7505681 baseEnd_7505681 := by
    simpa [prefixWord, tailWord_7505681, baseEnd_7505681] using wordTrace_append hprefix tailTrace_7505681
  have hstable : (prefixWord ++ tailWord_7505681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505681).length < 2 ^ (prefixWord ++ tailWord_7505681).sum := by decide
  have hdescent : baseEnd_7505681 < baseStart_7505681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505691 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 7]
def baseStart_7505691 : Nat := 118140960795 + 7505691 * 2 ^ 59
def prefixEnd_7505691 : Nat := 4983230072969 + 3 ^ 40 * 7505691 * 2
def baseEnd_7505691 : Nat := 1284675709041832894381487

theorem tailTrace_7505691 : CollatzResearch.WordTrace tailWord_7505691 prefixEnd_7505691 1284675709041832894381487 := by
  unfold tailWord_7505691
  simp only [CollatzResearch.WordTrace]
  refine ⟨273755040651170851813028927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182503360434113901208685951 273755040651170851813028927)
  ·
    refine ⟨410632560976756277719543391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273755040651170851813028927 410632560976756277719543391)
    ·
      refine ⟨615948841465134416579315087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410632560976756277719543391 615948841465134416579315087)
      ·
        refine ⟨923923262197701624868972631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615948841465134416579315087 923923262197701624868972631)
        ·
          refine ⟨1385884893296552437303458947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923923262197701624868972631 1385884893296552437303458947)
          ·
            refine ⟨2078827339944828655955188421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385884893296552437303458947 2078827339944828655955188421)
            ·
              refine ⟨389780126239655372991597829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2078827339944828655955188421 389780126239655372991597829)
              ·
                refine ⟨73083773669935382435924593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389780126239655372991597829 73083773669935382435924593)
                ·
                  refine ⟨54812830252451536826943445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73083773669935382435924593 54812830252451536826943445)
                  ·
                    refine ⟨1284675709041832894381487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54812830252451536826943445 1284675709041832894381487)
                    ·
                      rfl

theorem cell23_7505691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_7505691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505691 prefixEnd_7505691 := by exact prefixLift 7505691
  have htrace : WordTrace (prefixWord ++ tailWord_7505691) baseStart_7505691 baseEnd_7505691 := by
    simpa [prefixWord, tailWord_7505691, baseEnd_7505691] using wordTrace_append hprefix tailTrace_7505691
  have hstable : (prefixWord ++ tailWord_7505691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505691).length < 2 ^ (prefixWord ++ tailWord_7505691).sum := by decide
  have hdescent : baseEnd_7505691 < baseStart_7505691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505711 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_7505711 : Nat := 118140960795 + 7505711 * 2 ^ 59
def prefixEnd_7505711 : Nat := 4983230072969 + 3 ^ 40 * 7505711 * 2
def baseEnd_7505711 : Nat := 3854037396738588604894369

theorem tailTrace_7505711 : CollatzResearch.WordTrace tailWord_7505711 prefixEnd_7505711 3854037396738588604894369 := by
  unfold tailWord_7505711
  simp only [CollatzResearch.WordTrace]
  refine ⟨273755770111098395228756987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182503846740732263485837991 273755770111098395228756987)
  ·
    refine ⟨410633655166647592843135481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273755770111098395228756987 410633655166647592843135481)
    ·
      refine ⟨307975241374985694632351611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410633655166647592843135481 307975241374985694632351611)
      ·
        refine ⟨461962862062478541948527417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307975241374985694632351611 461962862062478541948527417)
        ·
          refine ⟨346472146546858906461395563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461962862062478541948527417 346472146546858906461395563)
          ·
            refine ⟨519708219820288359692093345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346472146546858906461395563 519708219820288359692093345)
            ·
              refine ⟨389781164865216269769070009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519708219820288359692093345 389781164865216269769070009)
              ·
                refine ⟨292335873648912202326802507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389781164865216269769070009 292335873648912202326802507)
                ·
                  refine ⟨438503810473368303490203761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292335873648912202326802507 438503810473368303490203761)
                  ·
                    refine ⟨328877857855026227617652821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 438503810473368303490203761 328877857855026227617652821)
                    ·
                      refine ⟨3854037396738588604894369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 328877857855026227617652821 3854037396738588604894369)
                      ·
                        rfl

theorem cell23_7505711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_7505711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505711 prefixEnd_7505711 := by exact prefixLift 7505711
  have htrace : WordTrace (prefixWord ++ tailWord_7505711) baseStart_7505711 baseEnd_7505711 := by
    simpa [prefixWord, tailWord_7505711, baseEnd_7505711] using wordTrace_append hprefix tailTrace_7505711
  have hstable : (prefixWord ++ tailWord_7505711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505711).length < 2 ^ (prefixWord ++ tailWord_7505711).sum := by decide
  have hdescent : baseEnd_7505711 < baseStart_7505711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505722 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_7505722 : Nat := 118140960795 + 7505722 * 2 ^ 59
def prefixEnd_7505722 : Nat := 4983230072969 + 3 ^ 40 * 7505722 * 2
def baseEnd_7505722 : Nat := 3854043045025788061856819

theorem tailTrace_7505722 : CollatzResearch.WordTrace tailWord_7505722 prefixEnd_7505722 3854043045025788061856819 := by
  unfold tailWord_7505722
  simp only [CollatzResearch.WordTrace]
  refine ⟨68439042828514636026851855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182504114209372362738271613 68439042828514636026851855)
  ·
    refine ⟨102658564242771954040277783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68439042828514636026851855 102658564242771954040277783)
    ·
      refine ⟨153987846364157931060416675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102658564242771954040277783 153987846364157931060416675)
      ·
        refine ⟨230981769546236896590625013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153987846364157931060416675 230981769546236896590625013)
        ·
          refine ⟨21654540894959709055371095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230981769546236896590625013 21654540894959709055371095)
          ·
            refine ⟨32481811342439563583056643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21654540894959709055371095 32481811342439563583056643)
            ·
              refine ⟨48722717013659345374584965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32481811342439563583056643 48722717013659345374584965)
              ·
                refine ⟨9135509440061127257734681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48722717013659345374584965 9135509440061127257734681)
                ·
                  refine ⟨6851632080045845443301011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9135509440061127257734681 6851632080045845443301011)
                  ·
                    refine ⟨10277448120068768164951517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851632080045845443301011 10277448120068768164951517)
                    ·
                      refine ⟨3854043045025788061856819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277448120068768164951517 3854043045025788061856819)
                      ·
                        rfl

theorem cell23_7505722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_7505722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505722 prefixEnd_7505722 := by exact prefixLift 7505722
  have htrace : WordTrace (prefixWord ++ tailWord_7505722) baseStart_7505722 baseEnd_7505722 := by
    simpa [prefixWord, tailWord_7505722, baseEnd_7505722] using wordTrace_append hprefix tailTrace_7505722
  have hstable : (prefixWord ++ tailWord_7505722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505722).length < 2 ^ (prefixWord ++ tailWord_7505722).sum := by decide
  have hdescent : baseEnd_7505722 < baseStart_7505722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505738 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_7505738 : Nat := 118140960795 + 7505738 * 2 ^ 59
def prefixEnd_7505738 : Nat := 4983230072969 + 3 ^ 40 * 7505738 * 2
def baseEnd_7505738 : Nat := 1284683753572086666418915

theorem tailTrace_7505738 : CollatzResearch.WordTrace tailWord_7505738 prefixEnd_7505738 1284683753572086666418915 := by
  unfold tailWord_7505738
  simp only [CollatzResearch.WordTrace]
  refine ⟨68439188720500144709997467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182504503254667052559993245 68439188720500144709997467)
  ·
    refine ⟨102658783080750217064996201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68439188720500144709997467 102658783080750217064996201)
    ·
      refine ⟨76994087310562662798747151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102658783080750217064996201 76994087310562662798747151)
      ·
        refine ⟨115491130965843994198120727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76994087310562662798747151 115491130965843994198120727)
        ·
          refine ⟨173236696448765991297181091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115491130965843994198120727 173236696448765991297181091)
          ·
            refine ⟨259855044673148986945771637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173236696448765991297181091 259855044673148986945771637)
            ·
              refine ⟨24361410438107717526166091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259855044673148986945771637 24361410438107717526166091)
              ·
                refine ⟨36542115657161576289249137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24361410438107717526166091 36542115657161576289249137)
                ·
                  refine ⟨27406586742871182216936853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36542115657161576289249137 27406586742871182216936853)
                  ·
                    refine ⟨1284683753572086666418915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27406586742871182216936853 1284683753572086666418915)
                    ·
                      rfl

theorem cell23_7505738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_7505738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505738 prefixEnd_7505738 := by exact prefixLift 7505738
  have htrace : WordTrace (prefixWord ++ tailWord_7505738) baseStart_7505738 baseEnd_7505738 := by
    simpa [prefixWord, tailWord_7505738, baseEnd_7505738] using wordTrace_append hprefix tailTrace_7505738
  have hstable : (prefixWord ++ tailWord_7505738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505738).length < 2 ^ (prefixWord ++ tailWord_7505738).sum := by decide
  have hdescent : baseEnd_7505738 < baseStart_7505738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505768 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 9]
def baseStart_7505768 : Nat := 118140960795 + 7505768 * 2 ^ 59
def prefixEnd_7505768 : Nat := 4983230072969 + 3 ^ 40 * 7505768 * 2
def baseEnd_7505768 : Nat := 428229629459543875764623

theorem tailTrace_7505768 : CollatzResearch.WordTrace tailWord_7505768 prefixEnd_7505768 428229629459543875764623 := by
  unfold tailWord_7505768
  simp only [CollatzResearch.WordTrace]
  refine ⟨136878924535945946981790979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182505232714594595975721305 136878924535945946981790979)
  ·
    refine ⟨205318386803918920472686469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136878924535945946981790979 205318386803918920472686469)
    ·
      refine ⟨38497197525734797588628713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205318386803918920472686469 38497197525734797588628713)
      ·
        refine ⟨28872898144301098191471535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38497197525734797588628713 28872898144301098191471535)
        ·
          refine ⟨43309347216451647287207303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28872898144301098191471535 43309347216451647287207303)
          ·
            refine ⟨64964020824677470930810955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43309347216451647287207303 64964020824677470930810955)
            ·
              refine ⟨97446031237016206396216433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64964020824677470930810955 97446031237016206396216433)
              ·
                refine ⟨73084523427762154797162325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97446031237016206396216433 73084523427762154797162325)
                ·
                  refine ⟨428229629459543875764623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73084523427762154797162325 428229629459543875764623)
                  ·
                    rfl

theorem cell23_7505768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_7505768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505768 prefixEnd_7505768 := by exact prefixLift 7505768
  have htrace : WordTrace (prefixWord ++ tailWord_7505768) baseStart_7505768 baseEnd_7505768 := by
    simpa [prefixWord, tailWord_7505768, baseEnd_7505768] using wordTrace_append hprefix tailTrace_7505768
  have hstable : (prefixWord ++ tailWord_7505768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505768).length < 2 ^ (prefixWord ++ tailWord_7505768).sum := by decide
  have hdescent : baseEnd_7505768 < baseStart_7505768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505785 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 5]
def baseStart_7505785 : Nat := 118140960795 + 7505785 * 2 ^ 59
def prefixEnd_7505785 : Nat := 4983230072969 + 3 ^ 40 * 7505785 * 2
def baseEnd_7505785 : Nat := 428230599367446812818781

theorem tailTrace_7505785 : CollatzResearch.WordTrace tailWord_7505785 prefixEnd_7505785 428230599367446812818781 := by
  unfold tailWord_7505785
  simp only [CollatzResearch.WordTrace]
  refine ⟨273758469112830305866950809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182505646075220203911300539 273758469112830305866950809)
  ·
    refine ⟨205318851834622729400213107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273758469112830305866950809 205318851834622729400213107)
    ·
      refine ⟨307978277751934094100319661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205318851834622729400213107 307978277751934094100319661)
      ·
        refine ⟨115491854156975285287619873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307978277751934094100319661 115491854156975285287619873)
        ·
          refine ⟨86618890617731463965714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115491854156975285287619873 86618890617731463965714905)
          ·
            refine ⟨64964167963298597974286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86618890617731463965714905 64964167963298597974286179)
            ·
              refine ⟨97446251944947896961429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64964167963298597974286179 97446251944947896961429269)
              ·
                refine ⟨4567793059919432670066997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97446251944947896961429269 4567793059919432670066997)
                ·
                  refine ⟨428230599367446812818781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567793059919432670066997 428230599367446812818781)
                  ·
                    rfl

theorem cell23_7505785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 5].length) (baseStart_7505785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505785 prefixEnd_7505785 := by exact prefixLift 7505785
  have htrace : WordTrace (prefixWord ++ tailWord_7505785) baseStart_7505785 baseEnd_7505785 := by
    simpa [prefixWord, tailWord_7505785, baseEnd_7505785] using wordTrace_append hprefix tailTrace_7505785
  have hstable : (prefixWord ++ tailWord_7505785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505785).length < 2 ^ (prefixWord ++ tailWord_7505785).sum := by decide
  have hdescent : baseEnd_7505785 < baseStart_7505785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505795 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3]
def baseStart_7505795 : Nat := 118140960795 + 7505795 * 2 ^ 59
def prefixEnd_7505795 : Nat := 4983230072969 + 3 ^ 40 * 7505795 * 2
def baseEnd_7505795 : Nat := 3854080529113566276243983

theorem tailTrace_7505795 : CollatzResearch.WordTrace tailWord_7505795 prefixEnd_7505795 3854080529113566276243983 := by
  unfold tailWord_7505795
  simp only [CollatzResearch.WordTrace]
  refine ⟨273758833842794077574814839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182505889228529385049876559 273758833842794077574814839)
  ·
    refine ⟨410638250764191116362222259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273758833842794077574814839 410638250764191116362222259)
    ·
      refine ⟨615957376146286674543333389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410638250764191116362222259 615957376146286674543333389)
      ·
        refine ⟨230984016054857502953750021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615957376146286674543333389 230984016054857502953750021)
        ·
          refine ⟨43309503010285781803828129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230984016054857502953750021 43309503010285781803828129)
          ·
            refine ⟨32482127257714336352871097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43309503010285781803828129 32482127257714336352871097)
            ·
              refine ⟨24361595443285752264653323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32482127257714336352871097 24361595443285752264653323)
              ·
                refine ⟨36542393164928628396979985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24361595443285752264653323 36542393164928628396979985)
                ·
                  refine ⟨27406794873696471297734989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36542393164928628396979985 27406794873696471297734989)
                  ·
                    refine ⟨10277548077636176736650621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27406794873696471297734989 10277548077636176736650621)
                    ·
                      refine ⟨3854080529113566276243983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277548077636176736650621 3854080529113566276243983)
                      ·
                        rfl

theorem cell23_7505795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_7505795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505795 prefixEnd_7505795 := by exact prefixLift 7505795
  have htrace : WordTrace (prefixWord ++ tailWord_7505795) baseStart_7505795 baseEnd_7505795 := by
    simpa [prefixWord, tailWord_7505795, baseEnd_7505795] using wordTrace_append hprefix tailTrace_7505795
  have hstable : (prefixWord ++ tailWord_7505795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505795).length < 2 ^ (prefixWord ++ tailWord_7505795).sum := by decide
  have hdescent : baseEnd_7505795 < baseStart_7505795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505855 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_7505855 : Nat := 118140960795 + 7505855 * 2 ^ 59
def prefixEnd_7505855 : Nat := 4983230072969 + 3 ^ 40 * 7505855 * 2
def baseEnd_7505855 : Nat := 3854111337952836041493707

theorem tailTrace_7505855 : CollatzResearch.WordTrace tailWord_7505855 prefixEnd_7505855 3854111337952836041493707 := by
  unfold tailWord_7505855
  simp only [CollatzResearch.WordTrace]
  refine ⟨273761022222576707821999019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182507348148384471881332679 273761022222576707821999019)
  ·
    refine ⟨410641533333865061732998529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273761022222576707821999019 410641533333865061732998529)
    ·
      refine ⟨307981150000398796299748897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410641533333865061732998529 307981150000398796299748897)
      ·
        refine ⟨230985862500299097224811673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307981150000398796299748897 230985862500299097224811673)
        ·
          refine ⟨173239396875224322918608755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230985862500299097224811673 173239396875224322918608755)
          ·
            refine ⟨259859095312836484377913133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173239396875224322918608755 259859095312836484377913133)
            ·
              refine ⟨97447160742313681641717425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259859095312836484377913133 97447160742313681641717425)
              ·
                refine ⟨73085370556735261231288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97447160742313681641717425 73085370556735261231288069)
                ·
                  refine ⟨13703506979387861480866513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73085370556735261231288069 13703506979387861480866513)
                  ·
                    refine ⟨10277630234540896110649885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13703506979387861480866513 10277630234540896110649885)
                    ·
                      refine ⟨3854111337952836041493707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277630234540896110649885 3854111337952836041493707)
                      ·
                        rfl

theorem cell23_7505855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_7505855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505855 prefixEnd_7505855 := by exact prefixLift 7505855
  have htrace : WordTrace (prefixWord ++ tailWord_7505855) baseStart_7505855 baseEnd_7505855 := by
    simpa [prefixWord, tailWord_7505855, baseEnd_7505855] using wordTrace_append hprefix tailTrace_7505855
  have hstable : (prefixWord ++ tailWord_7505855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505855).length < 2 ^ (prefixWord ++ tailWord_7505855).sum := by decide
  have hdescent : baseEnd_7505855 < baseStart_7505855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505912 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_7505912 : Nat := 118140960795 + 7505912 * 2 ^ 59
def prefixEnd_7505912 : Nat := 4983230072969 + 3 ^ 40 * 7505912 * 2
def baseEnd_7505912 : Nat := 3854140606350142318480945

theorem tailTrace_7505912 : CollatzResearch.WordTrace tailWord_7505912 prefixEnd_7505912 3854140606350142318480945 := by
  unfold tailWord_7505912
  simp only [CollatzResearch.WordTrace]
  refine ⟨136881550591685103278411995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182508734122246804371215993 136881550591685103278411995)
  ·
    refine ⟨205322325887527654917617993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136881550591685103278411995 205322325887527654917617993)
    ·
      refine ⟨153991744415645741188213495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205322325887527654917617993 153991744415645741188213495)
      ·
        refine ⟨230987616623468611782320243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153991744415645741188213495 230987616623468611782320243)
        ·
          refine ⟨346481424935202917673480365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230987616623468611782320243 346481424935202917673480365)
          ·
            refine ⟨129930534350701094127555137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346481424935202917673480365 129930534350701094127555137)
            ·
              refine ⟨97447900763025820595666353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129930534350701094127555137 97447900763025820595666353)
              ·
                refine ⟨73085925572269365446749765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97447900763025820595666353 73085925572269365446749765)
                ·
                  refine ⟨13703611044800506021265581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73085925572269365446749765 13703611044800506021265581)
                  ·
                    refine ⟨5138854141800189757974593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13703611044800506021265581 5138854141800189757974593)
                    ·
                      refine ⟨3854140606350142318480945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138854141800189757974593 3854140606350142318480945)
                      ·
                        rfl

theorem cell23_7505912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_7505912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505912 prefixEnd_7505912 := by exact prefixLift 7505912
  have htrace : WordTrace (prefixWord ++ tailWord_7505912) baseStart_7505912 baseEnd_7505912 := by
    simpa [prefixWord, tailWord_7505912, baseEnd_7505912] using wordTrace_append hprefix tailTrace_7505912
  have hstable : (prefixWord ++ tailWord_7505912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505912).length < 2 ^ (prefixWord ++ tailWord_7505912).sum := by decide
  have hdescent : baseEnd_7505912 < baseStart_7505912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505945 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7505945 : Nat := 118140960795 + 7505945 * 2 ^ 59
def prefixEnd_7505945 : Nat := 4983230072969 + 3 ^ 40 * 7505945 * 2
def baseEnd_7505945 : Nat := 3854157551211740689368293

theorem tailTrace_7505945 : CollatzResearch.WordTrace tailWord_7505945 prefixEnd_7505945 3854157551211740689368293 := by
  unfold tailWord_7505945
  simp only [CollatzResearch.WordTrace]
  refine ⟨273764304792250653192775289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182509536528167102128516859 273764304792250653192775289)
  ·
    refine ⟨205323228594187989894581467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273764304792250653192775289 205323228594187989894581467)
    ·
      refine ⟨307984842891281984841872201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205323228594187989894581467 307984842891281984841872201)
      ·
        refine ⟨230988632168461488631404151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307984842891281984841872201 230988632168461488631404151)
        ·
          refine ⟨346482948252692232947106227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230988632168461488631404151 346482948252692232947106227)
          ·
            refine ⟨519724422379038349420659341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346482948252692232947106227 519724422379038349420659341)
            ·
              refine ⟨194896658392139381032747253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519724422379038349420659341 194896658392139381032747253)
              ·
                refine ⟨18271561724263066971820055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194896658392139381032747253 18271561724263066971820055)
                ·
                  refine ⟨27407342586394600457730083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18271561724263066971820055 27407342586394600457730083)
                  ·
                    refine ⟨41111013879591900686595125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27407342586394600457730083 41111013879591900686595125)
                    ·
                      refine ⟨3854157551211740689368293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41111013879591900686595125 3854157551211740689368293)
                      ·
                        rfl

theorem cell23_7505945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7505945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505945 prefixEnd_7505945 := by exact prefixLift 7505945
  have htrace : WordTrace (prefixWord ++ tailWord_7505945) baseStart_7505945 baseEnd_7505945 := by
    simpa [prefixWord, tailWord_7505945, baseEnd_7505945] using wordTrace_append hprefix tailTrace_7505945
  have hstable : (prefixWord ++ tailWord_7505945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505945).length < 2 ^ (prefixWord ++ tailWord_7505945).sum := by decide
  have hdescent : baseEnd_7505945 < baseStart_7505945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505955 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_7505955 : Nat := 118140960795 + 7505955 * 2 ^ 59
def prefixEnd_7505955 : Nat := 4983230072969 + 3 ^ 40 * 7505955 * 2
def baseEnd_7505955 : Nat := 3854162686018285650243247

theorem tailTrace_7505955 : CollatzResearch.WordTrace tailWord_7505955 prefixEnd_7505955 3854162686018285650243247 := by
  unfold tailWord_7505955
  simp only [CollatzResearch.WordTrace]
  refine ⟨273764669522214424900639319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182509779681476283267092879 273764669522214424900639319)
  ·
    refine ⟨410647004283321637350958979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273764669522214424900639319 410647004283321637350958979)
    ·
      refine ⟨615970506424982456026438469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410647004283321637350958979 615970506424982456026438469)
      ·
        refine ⟨115494469954684210504957213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 615970506424982456026438469 115494469954684210504957213)
        ·
          refine ⟨43310426233006578939358955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115494469954684210504957213 43310426233006578939358955)
          ·
            refine ⟨64965639349509868409038433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43310426233006578939358955 64965639349509868409038433)
            ·
              refine ⟨48724229512132401306778825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64965639349509868409038433 48724229512132401306778825)
              ·
                refine ⟨36543172134099300980084119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48724229512132401306778825 36543172134099300980084119)
                ·
                  refine ⟨54814758201148951470126179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36543172134099300980084119 54814758201148951470126179)
                  ·
                    refine ⟨82222137301723427205189269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54814758201148951470126179 82222137301723427205189269)
                    ·
                      refine ⟨3854162686018285650243247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82222137301723427205189269 3854162686018285650243247)
                      ·
                        rfl

theorem cell23_7505955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_7505955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505955 prefixEnd_7505955 := by exact prefixLift 7505955
  have htrace : WordTrace (prefixWord ++ tailWord_7505955) baseStart_7505955 baseEnd_7505955 := by
    simpa [prefixWord, tailWord_7505955, baseEnd_7505955] using wordTrace_append hprefix tailTrace_7505955
  have hstable : (prefixWord ++ tailWord_7505955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505955).length < 2 ^ (prefixWord ++ tailWord_7505955).sum := by decide
  have hdescent : baseEnd_7505955 < baseStart_7505955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7505962 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7505962 : Nat := 118140960795 + 7505962 * 2 ^ 59
def prefixEnd_7505962 : Nat := 4983230072969 + 3 ^ 40 * 7505962 * 2
def baseEnd_7505962 : Nat := 3854166280382867122855715

theorem tailTrace_7505962 : CollatzResearch.WordTrace tailWord_7505962 prefixEnd_7505962 3854166280382867122855715 := by
  unfold tailWord_7505962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68441231208297266274036035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182509949888792710064096093 68441231208297266274036035)
  ·
    refine ⟨102661846812445899411054053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68441231208297266274036035 102661846812445899411054053)
    ·
      refine ⟨19249096277333606139572635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102661846812445899411054053 19249096277333606139572635)
      ·
        refine ⟨28873644416000409209358953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19249096277333606139572635 28873644416000409209358953)
        ·
          refine ⟨21655233312000306907019215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28873644416000409209358953 21655233312000306907019215)
          ·
            refine ⟨32482849968000460360528823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21655233312000306907019215 32482849968000460360528823)
            ·
              refine ⟨48724274952000690540793235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32482849968000460360528823 48724274952000690540793235)
              ·
                refine ⟨73086412428001035811189853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48724274952000690540793235 73086412428001035811189853)
                ·
                  refine ⟨27407404660500388429196195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73086412428001035811189853 27407404660500388429196195)
                  ·
                    refine ⟨41111106990750582643794293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27407404660500388429196195 41111106990750582643794293)
                    ·
                      refine ⟨3854166280382867122855715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41111106990750582643794293 3854166280382867122855715)
                      ·
                        rfl

theorem cell23_7505962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7505962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7505962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7505962 prefixEnd_7505962 := by exact prefixLift 7505962
  have htrace : WordTrace (prefixWord ++ tailWord_7505962) baseStart_7505962 baseEnd_7505962 := by
    simpa [prefixWord, tailWord_7505962, baseEnd_7505962] using wordTrace_append hprefix tailTrace_7505962
  have hstable : (prefixWord ++ tailWord_7505962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7505962).length < 2 ^ (prefixWord ++ tailWord_7505962).sum := by decide
  have hdescent : baseEnd_7505962 < baseStart_7505962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7505962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
