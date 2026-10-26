import V185TrunkScan23Chunk0378

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2240362 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2240362 : Nat := 118140960795 + 2240362 * 2 ^ 59
def prefixEnd_2240362 : Nat := 4983230072969 + 3 ^ 40 * 2240362 * 2
def baseEnd_2240362 : Nat := 1150382546068268807071769

theorem tailTrace_2240362 : CollatzResearch.WordTrace tailWord_2240362 prefixEnd_2240362 1150382546068268807071769 := by
  unfold tailWord_2240362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428178777389643053126835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54475143406372381475004893 20428178777389643053126835)
  ·
    refine ⟨30642268166084464579690253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20428178777389643053126835 30642268166084464579690253)
    ·
      refine ⟨11490850562281674217383845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30642268166084464579690253 11490850562281674217383845)
      ·
        refine ⟨2154534480427813915759471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11490850562281674217383845 2154534480427813915759471)
        ·
          refine ⟨3231801720641720873639207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154534480427813915759471 3231801720641720873639207)
          ·
            refine ⟨4847702580962581310458811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231801720641720873639207 4847702580962581310458811)
            ·
              refine ⟨7271553871443871965688217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847702580962581310458811 7271553871443871965688217)
              ·
                refine ⟨5453665403582903974266163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271553871443871965688217 5453665403582903974266163)
                ·
                  refine ⟨8180498105374355961399245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453665403582903974266163 8180498105374355961399245)
                  ·
                    refine ⟨3067686789515383485524717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8180498105374355961399245 3067686789515383485524717)
                    ·
                      refine ⟨1150382546068268807071769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067686789515383485524717 1150382546068268807071769)
                      ·
                        rfl

theorem cell23_2240362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2240362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240362 prefixEnd_2240362 := by exact prefixLift 2240362
  have htrace : WordTrace (prefixWord ++ tailWord_2240362) baseStart_2240362 baseEnd_2240362 := by
    simpa [prefixWord, tailWord_2240362, baseEnd_2240362] using wordTrace_append hprefix tailTrace_2240362
  have hstable : (prefixWord ++ tailWord_2240362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240362).length < 2 ^ (prefixWord ++ tailWord_2240362).sum := by decide
  have hdescent : baseEnd_2240362 < baseStart_2240362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240381 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2240381 : Nat := 118140960795 + 2240381 * 2 ^ 59
def prefixEnd_2240381 : Nat := 4983230072969 + 3 ^ 40 * 2240381 * 2
def baseEnd_2240381 : Nat := 1150392302200704232734181

theorem tailTrace_2240381 : CollatzResearch.WordTrace tailWord_2240381 prefixEnd_2240381 1150392302200704232734181 := by
  unfold tailWord_2240381
  simp only [CollatzResearch.WordTrace]
  refine ⟨81713408096489738457448997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54475605397659825638299331 81713408096489738457448997)
  ·
    refine ⟨15321264018091825960771687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81713408096489738457448997 15321264018091825960771687)
    ·
      refine ⟨22981896027137738941157531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15321264018091825960771687 22981896027137738941157531)
      ·
        refine ⟨34472844040706608411736297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22981896027137738941157531 34472844040706608411736297)
        ·
          refine ⟨25854633030529956308802223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34472844040706608411736297 25854633030529956308802223)
          ·
            refine ⟨38781949545794934463203335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25854633030529956308802223 38781949545794934463203335)
            ·
              refine ⟨58172924318692401694805003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38781949545794934463203335 58172924318692401694805003)
              ·
                refine ⟨87259386478038602542207505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58172924318692401694805003 87259386478038602542207505)
                ·
                  refine ⟨65444539858528951906655629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87259386478038602542207505 65444539858528951906655629)
                  ·
                    refine ⟨24541702446948356964995861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65444539858528951906655629 24541702446948356964995861)
                    ·
                      refine ⟨1150392302200704232734181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24541702446948356964995861 1150392302200704232734181)
                      ·
                        rfl

theorem cell23_2240381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2240381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240381 prefixEnd_2240381 := by exact prefixLift 2240381
  have htrace : WordTrace (prefixWord ++ tailWord_2240381) baseStart_2240381 baseEnd_2240381 := by
    simpa [prefixWord, tailWord_2240381, baseEnd_2240381] using wordTrace_append hprefix tailTrace_2240381
  have hstable : (prefixWord ++ tailWord_2240381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240381).length < 2 ^ (prefixWord ++ tailWord_2240381).sum := by decide
  have hdescent : baseEnd_2240381 < baseStart_2240381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240388 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2240388 : Nat := 118140960795 + 2240388 * 2 ^ 59
def prefixEnd_2240388 : Nat := 4983230072969 + 3 ^ 40 * 2240388 * 2
def baseEnd_2240388 : Nat := 1150395896565285705346649

theorem tailTrace_2240388 : CollatzResearch.WordTrace tailWord_2240388 prefixEnd_2240388 1150395896565285705346649 := by
  unfold tailWord_2240388
  simp only [CollatzResearch.WordTrace]
  refine ⟨40856831703732189326476909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54475775604976252435302545 40856831703732189326476909)
  ·
    refine ⟨15321311888899570997428841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40856831703732189326476909 15321311888899570997428841)
    ·
      refine ⟨11490983916674678248071631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15321311888899570997428841 11490983916674678248071631)
      ·
        refine ⟨17236475875012017372107447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11490983916674678248071631 17236475875012017372107447)
        ·
          refine ⟨25854713812518026058161171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17236475875012017372107447 25854713812518026058161171)
          ·
            refine ⟨38782070718777039087241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25854713812518026058161171 38782070718777039087241757)
            ·
              refine ⟨14543276519541389657715659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38782070718777039087241757 14543276519541389657715659)
              ·
                refine ⟨21814914779312084486573489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543276519541389657715659 21814914779312084486573489)
                ·
                  refine ⟨16361186084484063364930117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21814914779312084486573489 16361186084484063364930117)
                  ·
                    refine ⟨3067722390840761880924397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16361186084484063364930117 3067722390840761880924397)
                    ·
                      refine ⟨1150395896565285705346649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067722390840761880924397 1150395896565285705346649)
                      ·
                        rfl

theorem cell23_2240388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2240388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240388 prefixEnd_2240388 := by exact prefixLift 2240388
  have htrace : WordTrace (prefixWord ++ tailWord_2240388) baseStart_2240388 baseEnd_2240388 := by
    simpa [prefixWord, tailWord_2240388, baseEnd_2240388] using wordTrace_append hprefix tailTrace_2240388
  have hstable : (prefixWord ++ tailWord_2240388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240388).length < 2 ^ (prefixWord ++ tailWord_2240388).sum := by decide
  have hdescent : baseEnd_2240388 < baseStart_2240388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240402 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2240402 : Nat := 118140960795 + 2240402 * 2 ^ 59
def prefixEnd_2240402 : Nat := 4983230072969 + 3 ^ 40 * 2240402 * 2
def baseEnd_2240402 : Nat := 1150403085294448650571585

theorem tailTrace_2240402 : CollatzResearch.WordTrace tailWord_2240402 prefixEnd_2240402 1150403085294448650571585 := by
  unfold tailWord_2240402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428543507353414760990865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54476116019609106029308973 20428543507353414760990865)
  ·
    refine ⟨15321407630515061070743149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20428543507353414760990865 15321407630515061070743149)
    ·
      refine ⟨5745527861443147901528681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15321407630515061070743149 5745527861443147901528681)
      ·
        refine ⟨4309145896082360926146511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5745527861443147901528681 4309145896082360926146511)
        ·
          refine ⟨6463718844123541389219767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309145896082360926146511 6463718844123541389219767)
          ·
            refine ⟨9695578266185312083829651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463718844123541389219767 9695578266185312083829651)
            ·
              refine ⟨14543367399277968125744477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9695578266185312083829651 14543367399277968125744477)
              ·
                refine ⟨5453762774729238047154179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14543367399277968125744477 5453762774729238047154179)
                ·
                  refine ⟨8180644162093857070731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453762774729238047154179 8180644162093857070731269)
                  ·
                    refine ⟨1533870780392598200762113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8180644162093857070731269 1533870780392598200762113)
                    ·
                      refine ⟨1150403085294448650571585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533870780392598200762113 1150403085294448650571585)
                      ·
                        rfl

theorem cell23_2240402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2240402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240402 prefixEnd_2240402 := by exact prefixLift 2240402
  have htrace : WordTrace (prefixWord ++ tailWord_2240402) baseStart_2240402 baseEnd_2240402 := by
    simpa [prefixWord, tailWord_2240402, baseEnd_2240402] using wordTrace_append hprefix tailTrace_2240402
  have hstable : (prefixWord ++ tailWord_2240402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240402).length < 2 ^ (prefixWord ++ tailWord_2240402).sum := by decide
  have hdescent : baseEnd_2240402 < baseStart_2240402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240430 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2240430 : Nat := 118140960795 + 2240430 * 2 ^ 59
def prefixEnd_2240430 : Nat := 4983230072969 + 3 ^ 40 * 2240430 * 2
def baseEnd_2240430 : Nat := 1150417462752774541021457

theorem tailTrace_2240430 : CollatzResearch.WordTrace tailWord_2240430 prefixEnd_2240430 1150417462752774541021457 := by
  unfold tailWord_2240430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214399409164027478247843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54476796848874813217321829 10214399409164027478247843)
  ·
    refine ⟨15321599113746041217371765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10214399409164027478247843 15321599113746041217371765)
    ·
      refine ⟨1436399916913691364128603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15321599113746041217371765 1436399916913691364128603)
      ·
        refine ⟨2154599875370537046192905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436399916913691364128603 2154599875370537046192905)
        ·
          refine ⟨1615949906527902784644679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2154599875370537046192905 1615949906527902784644679)
          ·
            refine ⟨2423924859791854176967019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615949906527902784644679 2423924859791854176967019)
            ·
              refine ⟨3635887289687781265450529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423924859791854176967019 3635887289687781265450529)
              ·
                refine ⟨2726915467265835949087897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635887289687781265450529 2726915467265835949087897)
                ·
                  refine ⟨2045186600449376961815923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726915467265835949087897 2045186600449376961815923)
                  ·
                    refine ⟨3067779900674065442723885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045186600449376961815923 3067779900674065442723885)
                    ·
                      refine ⟨1150417462752774541021457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067779900674065442723885 1150417462752774541021457)
                      ·
                        rfl

theorem cell23_2240430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2240430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240430 prefixEnd_2240430 := by exact prefixLift 2240430
  have htrace : WordTrace (prefixWord ++ tailWord_2240430) baseStart_2240430 baseEnd_2240430 := by
    simpa [prefixWord, tailWord_2240430, baseEnd_2240430] using wordTrace_append hprefix tailTrace_2240430
  have hstable : (prefixWord ++ tailWord_2240430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240430).length < 2 ^ (prefixWord ++ tailWord_2240430).sum := by decide
  have hdescent : baseEnd_2240430 < baseStart_2240430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240436 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2240436 : Nat := 118140960795 + 2240436 * 2 ^ 59
def prefixEnd_2240436 : Nat := 4983230072969 + 3 ^ 40 * 2240436 * 2
def baseEnd_2240436 : Nat := 1150420543636701517546429

theorem tailTrace_2240436 : CollatzResearch.WordTrace tailWord_2240436 prefixEnd_2240436 1150420543636701517546429 := by
  unfold tailWord_2240436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40857707055645241425350581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54476942740860321900467441 40857707055645241425350581)
  ·
    refine ⟨3830410036466741383626617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40857707055645241425350581 3830410036466741383626617)
    ·
      refine ⟨2872807527350056037719963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3830410036466741383626617 2872807527350056037719963)
      ·
        refine ⟨4309211291025084056579945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872807527350056037719963 4309211291025084056579945)
        ·
          refine ⟨3231908468268813042434959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4309211291025084056579945 3231908468268813042434959)
          ·
            refine ⟨4847862702403219563652439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231908468268813042434959 4847862702403219563652439)
            ·
              refine ⟨7271794053604829345478659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847862702403219563652439 7271794053604829345478659)
              ·
                refine ⟨10907691080407244018217989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271794053604829345478659 10907691080407244018217989)
                ·
                  refine ⟨2045192077576358253415873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10907691080407244018217989 2045192077576358253415873)
                  ·
                    refine ⟨1533894058182268690061905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045192077576358253415873 1533894058182268690061905)
                    ·
                      refine ⟨1150420543636701517546429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1533894058182268690061905 1150420543636701517546429)
                      ·
                        rfl

theorem cell23_2240436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2240436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240436 prefixEnd_2240436 := by exact prefixLift 2240436
  have htrace : WordTrace (prefixWord ++ tailWord_2240436) baseStart_2240436 baseEnd_2240436 := by
    simpa [prefixWord, tailWord_2240436, baseEnd_2240436] using wordTrace_append hprefix tailTrace_2240436
  have hstable : (prefixWord ++ tailWord_2240436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240436).length < 2 ^ (prefixWord ++ tailWord_2240436).sum := by decide
  have hdescent : baseEnd_2240436 < baseStart_2240436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240451 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 8]
def baseStart_2240451 : Nat := 118140960795 + 2240451 * 2 ^ 59
def prefixEnd_2240451 : Nat := 4983230072969 + 3 ^ 40 * 2240451 * 2
def baseEnd_2240451 : Nat := 383476081948839652952953

theorem tailTrace_2240451 : CollatzResearch.WordTrace tailWord_2240451 prefixEnd_2240451 383476081948839652952953 := by
  unfold tailWord_2240451
  simp only [CollatzResearch.WordTrace]
  refine ⟨81715961206236140412497207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54477307470824093608331471 81715961206236140412497207)
  ·
    refine ⟨122573941809354210618745811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81715961206236140412497207 122573941809354210618745811)
    ·
      refine ⟨183860912714031315928118717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122573941809354210618745811 183860912714031315928118717)
      ·
        refine ⟨68947842267761743473044519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183860912714031315928118717 68947842267761743473044519)
        ·
          refine ⟨103421763401642615209566779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68947842267761743473044519 103421763401642615209566779)
          ·
            refine ⟨155132645102463922814350169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103421763401642615209566779 155132645102463922814350169)
            ·
              refine ⟨116349483826847942110762627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155132645102463922814350169 116349483826847942110762627)
              ·
                refine ⟨174524225740271913166143941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116349483826847942110762627 174524225740271913166143941)
                ·
                  refine ⟨32723292326300983718651989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174524225740271913166143941 32723292326300983718651989)
                  ·
                    refine ⟨383476081948839652952953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32723292326300983718651989 383476081948839652952953)
                    ·
                      rfl

theorem cell23_2240451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_2240451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240451 prefixEnd_2240451 := by exact prefixLift 2240451
  have htrace : WordTrace (prefixWord ++ tailWord_2240451) baseStart_2240451 baseEnd_2240451 := by
    simpa [prefixWord, tailWord_2240451, baseEnd_2240451] using wordTrace_append hprefix tailTrace_2240451
  have hstable : (prefixWord ++ tailWord_2240451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240451).length < 2 ^ (prefixWord ++ tailWord_2240451).sum := by decide
  have hdescent : baseEnd_2240451 < baseStart_2240451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240458 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2240458 : Nat := 118140960795 + 2240458 * 2 ^ 59
def prefixEnd_2240458 : Nat := 4983230072969 + 3 ^ 40 * 2240458 * 2
def baseEnd_2240458 : Nat := 1150431840211100431471327

theorem tailTrace_2240458 : CollatzResearch.WordTrace tailWord_2240458 prefixEnd_2240458 1150431840211100431471327 := by
  unfold tailWord_2240458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20429054129302695152000507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54477477678140520405334685 20429054129302695152000507)
  ·
    refine ⟨30643581193954042728000761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20429054129302695152000507 30643581193954042728000761)
    ·
      refine ⟨22982685895465532046000571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30643581193954042728000761 22982685895465532046000571)
      ·
        refine ⟨34474028843198298069000857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22982685895465532046000571 34474028843198298069000857)
        ·
          refine ⟨25855521632398723551750643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34474028843198298069000857 25855521632398723551750643)
          ·
            refine ⟨38783282448598085327625965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25855521632398723551750643 38783282448598085327625965)
            ·
              refine ⟨14543730918224281997859737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38783282448598085327625965 14543730918224281997859737)
              ·
                refine ⟨10907798188668211498394803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14543730918224281997859737 10907798188668211498394803)
                ·
                  refine ⟨16361697283002317247592205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10907798188668211498394803 16361697283002317247592205)
                  ·
                    refine ⟨6135636481125868967847077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16361697283002317247592205 6135636481125868967847077)
                    ·
                      refine ⟨1150431840211100431471327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6135636481125868967847077 1150431840211100431471327)
                      ·
                        rfl

theorem cell23_2240458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2240458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240458 prefixEnd_2240458 := by exact prefixLift 2240458
  have htrace : WordTrace (prefixWord ++ tailWord_2240458) baseStart_2240458 baseEnd_2240458 := by
    simpa [prefixWord, tailWord_2240458, baseEnd_2240458] using wordTrace_append hprefix tailTrace_2240458
  have hstable : (prefixWord ++ tailWord_2240458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240458).length < 2 ^ (prefixWord ++ tailWord_2240458).sum := by decide
  have hdescent : baseEnd_2240458 < baseStart_2240458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240468 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2240468 : Nat := 118140960795 + 2240468 * 2 ^ 59
def prefixEnd_2240468 : Nat := 4983230072969 + 3 ^ 40 * 2240468 * 2
def baseEnd_2240468 : Nat := 383478991672548464115427

theorem tailTrace_2240468 : CollatzResearch.WordTrace tailWord_2240468 prefixEnd_2240468 383478991672548464115427 := by
  unfold tailWord_2240468
  simp only [CollatzResearch.WordTrace]
  refine ⟨40858290623587276157933029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54477720831449701543910705 40858290623587276157933029)
  ·
    refine ⟨7660929491922614279612443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40858290623587276157933029 7660929491922614279612443)
    ·
      refine ⟨11491394237883921419418665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7660929491922614279612443 11491394237883921419418665)
      ·
        refine ⟨8618545678412941064563999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11491394237883921419418665 8618545678412941064563999)
        ·
          refine ⟨12927818517619411596845999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8618545678412941064563999 12927818517619411596845999)
          ·
            refine ⟨19391727776429117395268999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927818517619411596845999 19391727776429117395268999)
            ·
              refine ⟨29087591664643676092903499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19391727776429117395268999 29087591664643676092903499)
              ·
                refine ⟨43631387496965514139355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29087591664643676092903499 43631387496965514139355249)
                ·
                  refine ⟨32723540622724135604516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43631387496965514139355249 32723540622724135604516437)
                  ·
                    refine ⟨383478991672548464115427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32723540622724135604516437 383478991672548464115427)
                    ·
                      rfl

theorem cell23_2240468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2240468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240468 prefixEnd_2240468 := by exact prefixLift 2240468
  have htrace : WordTrace (prefixWord ++ tailWord_2240468) baseStart_2240468 baseEnd_2240468 := by
    simpa [prefixWord, tailWord_2240468, baseEnd_2240468] using wordTrace_append hprefix tailTrace_2240468
  have hstable : (prefixWord ++ tailWord_2240468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240468).length < 2 ^ (prefixWord ++ tailWord_2240468).sum := by decide
  have hdescent : baseEnd_2240468 < baseStart_2240468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240495 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_2240495 : Nat := 118140960795 + 2240495 * 2 ^ 59
def prefixEnd_2240495 : Nat := 4983230072969 + 3 ^ 40 * 2240495 * 2
def baseEnd_2240495 : Nat := 1150450838995316786708657

theorem tailTrace_2240495 : CollatzResearch.WordTrace tailWord_2240495 prefixEnd_2240495 1150450838995316786708657 := by
  unfold tailWord_2240495
  simp only [CollatzResearch.WordTrace]
  refine ⟨81717566018076735927098939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54478377345384490618065959 81717566018076735927098939)
  ·
    refine ⟨122576349027115103890648409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81717566018076735927098939 122576349027115103890648409)
    ·
      refine ⟨91932261770336327917986307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122576349027115103890648409 91932261770336327917986307)
      ·
        refine ⟨137898392655504491876979461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91932261770336327917986307 137898392655504491876979461)
        ·
          refine ⟨25855948622907092226933649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137898392655504491876979461 25855948622907092226933649)
          ·
            refine ⟨19391961467180319170200237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25855948622907092226933649 19391961467180319170200237)
            ·
              refine ⟨7271985550192619688825089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19391961467180319170200237 7271985550192619688825089)
              ·
                refine ⟨5453989162644464766618817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271985550192619688825089 5453989162644464766618817)
                ·
                  refine ⟨4090491871983348574964113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453989162644464766618817 4090491871983348574964113)
                  ·
                    refine ⟨3067868903987511431223085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090491871983348574964113 3067868903987511431223085)
                    ·
                      refine ⟨1150450838995316786708657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067868903987511431223085 1150450838995316786708657)
                      ·
                        rfl

theorem cell23_2240495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_2240495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240495 prefixEnd_2240495 := by exact prefixLift 2240495
  have htrace : WordTrace (prefixWord ++ tailWord_2240495) baseStart_2240495 baseEnd_2240495 := by
    simpa [prefixWord, tailWord_2240495, baseEnd_2240495] using wordTrace_append hprefix tailTrace_2240495
  have hstable : (prefixWord ++ tailWord_2240495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240495).length < 2 ^ (prefixWord ++ tailWord_2240495).sum := by decide
  have hdescent : baseEnd_2240495 < baseStart_2240495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240528 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_2240528 : Nat := 118140960795 + 2240528 * 2 ^ 59
def prefixEnd_2240528 : Nat := 4983230072969 + 3 ^ 40 * 2240528 * 2
def baseEnd_2240528 : Nat := 383489261285638385865335

theorem tailTrace_2240528 : CollatzResearch.WordTrace tailWord_2240528 prefixEnd_2240528 383489261285638385865335 := by
  unfold tailWord_2240528
  simp only [CollatzResearch.WordTrace]
  refine ⟨40859384813478591281525119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54479179751304788375366825 40859384813478591281525119)
  ·
    refine ⟨61289077220217886922287679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40859384813478591281525119 61289077220217886922287679)
    ·
      refine ⟨91933615830326830383431519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61289077220217886922287679 91933615830326830383431519)
      ·
        refine ⟨137900423745490245575147279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91933615830326830383431519 137900423745490245575147279)
        ·
          refine ⟨206850635618235368362720919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137900423745490245575147279 206850635618235368362720919)
          ·
            refine ⟨310275953427353052544081379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206850635618235368362720919 310275953427353052544081379)
            ·
              refine ⟨465413930141029578816122069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310275953427353052544081379 465413930141029578816122069)
              ·
                refine ⟨10908138987680380753502861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 465413930141029578816122069 10908138987680380753502861)
                ·
                  refine ⟨4090552120380142782563573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10908138987680380753502861 4090552120380142782563573)
                  ·
                    refine ⟨383489261285638385865335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4090552120380142782563573 383489261285638385865335)
                    ·
                      rfl

theorem cell23_2240528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_2240528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240528 prefixEnd_2240528 := by exact prefixLift 2240528
  have htrace : WordTrace (prefixWord ++ tailWord_2240528) baseStart_2240528 baseEnd_2240528 := by
    simpa [prefixWord, tailWord_2240528, baseEnd_2240528] using wordTrace_append hprefix tailTrace_2240528
  have hstable : (prefixWord ++ tailWord_2240528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240528).length < 2 ^ (prefixWord ++ tailWord_2240528).sum := by decide
  have hdescent : baseEnd_2240528 < baseStart_2240528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240565 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2240565 : Nat := 118140960795 + 2240565 * 2 ^ 59
def prefixEnd_2240565 : Nat := 4983230072969 + 3 ^ 40 * 2240565 * 2
def baseEnd_2240565 : Nat := 1150486782641131512833335

theorem tailTrace_2240565 : CollatzResearch.WordTrace tailWord_2240565 prefixEnd_2240565 1150486782641131512833335 := by
  unfold tailWord_2240565
  simp only [CollatzResearch.WordTrace]
  refine ⟨81720119127823137882147149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54480079418548758588098099 81720119127823137882147149)
  ·
    refine ⟨30645044672933676705805181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81720119127823137882147149 30645044672933676705805181)
    ·
      refine ⟨11491891752350128764676943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30645044672933676705805181 11491891752350128764676943)
      ·
        refine ⟨17237837628525193147015415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491891752350128764676943 17237837628525193147015415)
        ·
          refine ⟨25856756442787789720523123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17237837628525193147015415 25856756442787789720523123)
          ·
            refine ⟨38785134664181684580784685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25856756442787789720523123 38785134664181684580784685)
            ·
              refine ⟨14544425499068131717794257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38785134664181684580784685 14544425499068131717794257)
              ·
                refine ⟨10908319124301098788345693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14544425499068131717794257 10908319124301098788345693)
                ·
                  refine ⟨4090619671612912045629635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10908319124301098788345693 4090619671612912045629635)
                  ·
                    refine ⟨6135929507419368068444453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090619671612912045629635 6135929507419368068444453)
                    ·
                      refine ⟨1150486782641131512833335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6135929507419368068444453 1150486782641131512833335)
                      ·
                        rfl

theorem cell23_2240565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2240565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240565 prefixEnd_2240565 := by exact prefixLift 2240565
  have htrace : WordTrace (prefixWord ++ tailWord_2240565) baseStart_2240565 baseEnd_2240565 := by
    simpa [prefixWord, tailWord_2240565, baseEnd_2240565] using wordTrace_append hprefix tailTrace_2240565
  have hstable : (prefixWord ++ tailWord_2240565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240565).length < 2 ^ (prefixWord ++ tailWord_2240565).sum := by decide
  have hdescent : baseEnd_2240565 < baseStart_2240565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240585 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_2240585 : Nat := 118140960795 + 2240585 * 2 ^ 59
def prefixEnd_2240585 : Nat := 4983230072969 + 3 ^ 40 * 2240585 * 2
def baseEnd_2240585 : Nat := 1150497052254221434583243

theorem tailTrace_2240585 : CollatzResearch.WordTrace tailWord_2240585 prefixEnd_2240585 1150497052254221434583243 := by
  unfold tailWord_2240585
  simp only [CollatzResearch.WordTrace]
  refine ⟨81720848587750681297875209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54480565725167120865250139 81720848587750681297875209)
  ·
    refine ⟨61290636440813010973406407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81720848587750681297875209 61290636440813010973406407)
    ·
      refine ⟨91935954661219516460109611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61290636440813010973406407 91935954661219516460109611)
      ·
        refine ⟨137903931991829274690164417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91935954661219516460109611 137903931991829274690164417)
        ·
          refine ⟨103427948993871956017623313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137903931991829274690164417 103427948993871956017623313)
          ·
            refine ⟨77570961745403967013217485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103427948993871956017623313 77570961745403967013217485)
            ·
              refine ⟨29089110654526487629956557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77570961745403967013217485 29089110654526487629956557)
              ·
                refine ⟨10908416495447432861233709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29089110654526487629956557 10908416495447432861233709)
                ·
                  refine ⟨4090656185792787322962641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10908416495447432861233709 4090656185792787322962641)
                  ·
                    refine ⟨3067992139344590492221981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090656185792787322962641 3067992139344590492221981)
                    ·
                      refine ⟨1150497052254221434583243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3067992139344590492221981 1150497052254221434583243)
                      ·
                        rfl

theorem cell23_2240585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_2240585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240585 prefixEnd_2240585 := by exact prefixLift 2240585
  have htrace : WordTrace (prefixWord ++ tailWord_2240585) baseStart_2240585 baseEnd_2240585 := by
    simpa [prefixWord, tailWord_2240585, baseEnd_2240585] using wordTrace_append hprefix tailTrace_2240585
  have hstable : (prefixWord ++ tailWord_2240585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240585).length < 2 ^ (prefixWord ++ tailWord_2240585).sum := by decide
  have hdescent : baseEnd_2240585 < baseStart_2240585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240588 : List Nat := [2, 2, 1, 3, 1, 1, 2, 11]
def baseStart_2240588 : Nat := 118140960795 + 2240588 * 2 ^ 59
def prefixEnd_2240588 : Nat := 4983230072969 + 3 ^ 40 * 2240588 * 2
def baseEnd_2240588 : Nat := 42611058988747589735027

theorem tailTrace_2240588 : CollatzResearch.WordTrace tailWord_2240588 prefixEnd_2240588 42611058988747589735027 := by
  unfold tailWord_2240588
  simp only [CollatzResearch.WordTrace]
  refine ⟨40860479003369906405117209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54480638671159875206822945 40860479003369906405117209)
  ·
    refine ⟨30645359252527429803837907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40860479003369906405117209 30645359252527429803837907)
    ·
      refine ⟨45968038878791144705756861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30645359252527429803837907 45968038878791144705756861)
      ·
        refine ⟨17238014579546679264658823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45968038878791144705756861 17238014579546679264658823)
        ·
          refine ⟨25857021869320018896988235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17238014579546679264658823 25857021869320018896988235)
          ·
            refine ⟨38785532803980028345482353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25857021869320018896988235 38785532803980028345482353)
            ·
              refine ⟨29089149602985021259111765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38785532803980028345482353 29089149602985021259111765)
              ·
                refine ⟨42611058988747589735027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 29089149602985021259111765 42611058988747589735027)
                ·
                  rfl

theorem cell23_2240588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 11].length) (baseStart_2240588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240588 prefixEnd_2240588 := by exact prefixLift 2240588
  have htrace : WordTrace (prefixWord ++ tailWord_2240588) baseStart_2240588 baseEnd_2240588 := by
    simpa [prefixWord, tailWord_2240588, baseEnd_2240588] using wordTrace_append hprefix tailTrace_2240588
  have hstable : (prefixWord ++ tailWord_2240588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240588).length < 2 ^ (prefixWord ++ tailWord_2240588).sum := by decide
  have hdescent : baseEnd_2240588 < baseStart_2240588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240602 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_2240602 : Nat := 118140960795 + 2240602 * 2 ^ 59
def prefixEnd_2240602 : Nat := 4983230072969 + 3 ^ 40 * 2240602 * 2
def baseEnd_2240602 : Nat := 1150505781425347868070665

theorem tailTrace_2240602 : CollatzResearch.WordTrace tailWord_2240602 prefixEnd_2240602 1150505781425347868070665 := by
  unfold tailWord_2240602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20430367157172273300311015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54480979085792728800829373 20430367157172273300311015)
  ·
    refine ⟨30645550735758409950466523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20430367157172273300311015 30645550735758409950466523)
    ·
      refine ⟨45968326103637614925699785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30645550735758409950466523 45968326103637614925699785)
      ·
        refine ⟨34476244577728211194274839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45968326103637614925699785 34476244577728211194274839)
        ·
          refine ⟨51714366866592316791412259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34476244577728211194274839 51714366866592316791412259)
          ·
            refine ⟨77571550299888475187118389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51714366866592316791412259 77571550299888475187118389)
            ·
              refine ⟨7272332840614544548792349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77571550299888475187118389 7272332840614544548792349)
              ·
                refine ⟨2727124815230454205797131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272332840614544548792349 2727124815230454205797131)
                ·
                  refine ⟨4090687222845681308695697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727124815230454205797131 4090687222845681308695697)
                  ·
                    refine ⟨3068015417134260981521773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090687222845681308695697 3068015417134260981521773)
                    ·
                      refine ⟨1150505781425347868070665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068015417134260981521773 1150505781425347868070665)
                      ·
                        rfl

theorem cell23_2240602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_2240602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240602 prefixEnd_2240602 := by exact prefixLift 2240602
  have htrace : WordTrace (prefixWord ++ tailWord_2240602) baseStart_2240602 baseEnd_2240602 := by
    simpa [prefixWord, tailWord_2240602, baseEnd_2240602] using wordTrace_append hprefix tailTrace_2240602
  have hstable : (prefixWord ++ tailWord_2240602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240602).length < 2 ^ (prefixWord ++ tailWord_2240602).sum := by decide
  have hdescent : baseEnd_2240602 < baseStart_2240602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240645 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_2240645 : Nat := 118140960795 + 2240645 * 2 ^ 59
def prefixEnd_2240645 : Nat := 4983230072969 + 3 ^ 40 * 2240645 * 2
def baseEnd_2240645 : Nat := 1150527861093491199832967

theorem tailTrace_2240645 : CollatzResearch.WordTrace tailWord_2240645 prefixEnd_2240645 1150527861093491199832967 := by
  unfold tailWord_2240645
  simp only [CollatzResearch.WordTrace]
  refine ⟨81723036967533311545059389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54482024645022207696706259 81723036967533311545059389)
  ·
    refine ⟨30646138862824991829397271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81723036967533311545059389 30646138862824991829397271)
    ·
      refine ⟨45969208294237487744095907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30646138862824991829397271 45969208294237487744095907)
      ·
        refine ⟨68953812441356231616143861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45969208294237487744095907 68953812441356231616143861)
        ·
          refine ⟨6464419916377146714013487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68953812441356231616143861 6464419916377146714013487)
          ·
            refine ⟨9696629874565720071020231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6464419916377146714013487 9696629874565720071020231)
            ·
              refine ⟨14544944811848580106530347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9696629874565720071020231 14544944811848580106530347)
              ·
                refine ⟨21817417217772870159795521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14544944811848580106530347 21817417217772870159795521)
                ·
                  refine ⟨16363062913329652619846641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21817417217772870159795521 16363062913329652619846641)
                  ·
                    refine ⟨12272297184997239464884981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16363062913329652619846641 12272297184997239464884981)
                    ·
                      refine ⟨1150527861093491199832967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12272297184997239464884981 1150527861093491199832967)
                      ·
                        rfl

theorem cell23_2240645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_2240645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240645 prefixEnd_2240645 := by exact prefixLift 2240645
  have htrace : WordTrace (prefixWord ++ tailWord_2240645) baseStart_2240645 baseEnd_2240645 := by
    simpa [prefixWord, tailWord_2240645, baseEnd_2240645] using wordTrace_append hprefix tailTrace_2240645
  have hstable : (prefixWord ++ tailWord_2240645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240645).length < 2 ^ (prefixWord ++ tailWord_2240645).sum := by decide
  have hdescent : baseEnd_2240645 < baseStart_2240645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240712 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 5]
def baseStart_2240712 : Nat := 118140960795 + 2240712 * 2 ^ 59
def prefixEnd_2240712 : Nat := 4983230072969 + 3 ^ 40 * 2240712 * 2
def baseEnd_2240712 : Nat := 127840251588593604188351

theorem tailTrace_2240712 : CollatzResearch.WordTrace tailWord_2240712 prefixEnd_2240712 127840251588593604188351 := by
  unfold tailWord_2240712
  simp only [CollatzResearch.WordTrace]
  refine ⟨40862740329145290993874195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54483653772193721325165593 40862740329145290993874195)
  ·
    refine ⟨61294110493717936490811293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40862740329145290993874195 61294110493717936490811293)
    ·
      refine ⟨22985291435144226184054235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61294110493717936490811293 22985291435144226184054235)
      ·
        refine ⟨34477937152716339276081353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22985291435144226184054235 34477937152716339276081353)
        ·
          refine ⟨25858452864537254457061015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34477937152716339276081353 25858452864537254457061015)
          ·
            refine ⟨38787679296805881685591523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858452864537254457061015 38787679296805881685591523)
            ·
              refine ⟨58181518945208822528387285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38787679296805881685591523 58181518945208822528387285)
              ·
                refine ⟨1363629350278331778009077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58181518945208822528387285 1363629350278331778009077)
                ·
                  refine ⟨127840251588593604188351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363629350278331778009077 127840251588593604188351)
                  ·
                    rfl

theorem cell23_2240712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 5].length) (baseStart_2240712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240712 prefixEnd_2240712 := by exact prefixLift 2240712
  have htrace : WordTrace (prefixWord ++ tailWord_2240712) baseStart_2240712 baseEnd_2240712 := by
    simpa [prefixWord, tailWord_2240712, baseEnd_2240712] using wordTrace_append hprefix tailTrace_2240712
  have hstable : (prefixWord ++ tailWord_2240712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240712).length < 2 ^ (prefixWord ++ tailWord_2240712).sum := by decide
  have hdescent : baseEnd_2240712 < baseStart_2240712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240729 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 5]
def baseStart_2240729 : Nat := 118140960795 + 2240729 * 2 ^ 59
def prefixEnd_2240729 : Nat := 4983230072969 + 3 ^ 40 * 2240729 * 2
def baseEnd_2240729 : Nat := 127841221496496541242509

theorem tailTrace_2240729 : CollatzResearch.WordTrace tailWord_2240729 prefixEnd_2240729 127841221496496541242509 := by
  unfold tailWord_2240729
  simp only [CollatzResearch.WordTrace]
  refine ⟨81726100699228993891117241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54484067132819329260744827 81726100699228993891117241)
  ·
    refine ⟨61294575524421745418337931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81726100699228993891117241 61294575524421745418337931)
    ·
      refine ⟨91941863286632618127506897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61294575524421745418337931 91941863286632618127506897)
      ·
        refine ⟨68956397464974463595630173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91941863286632618127506897 68956397464974463595630173)
        ·
          refine ⟨25858649049365423848361315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68956397464974463595630173 25858649049365423848361315)
          ·
            refine ⟨38787973574048135772541973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858649049365423848361315 38787973574048135772541973)
            ·
              refine ⟨1818186261283506364337905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38787973574048135772541973 1818186261283506364337905)
              ·
                refine ⟨1363639695962629773253429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818186261283506364337905 1363639695962629773253429)
                ·
                  refine ⟨127841221496496541242509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363639695962629773253429 127841221496496541242509)
                  ·
                    rfl

theorem cell23_2240729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 5].length) (baseStart_2240729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240729 prefixEnd_2240729 := by exact prefixLift 2240729
  have htrace : WordTrace (prefixWord ++ tailWord_2240729) baseStart_2240729 baseEnd_2240729 := by
    simpa [prefixWord, tailWord_2240729, baseEnd_2240729] using wordTrace_append hprefix tailTrace_2240729
  have hstable : (prefixWord ++ tailWord_2240729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240729).length < 2 ^ (prefixWord ++ tailWord_2240729).sum := by decide
  have hdescent : baseEnd_2240729 < baseStart_2240729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240745 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_2240745 : Nat := 118140960795 + 2240745 * 2 ^ 59
def prefixEnd_2240745 : Nat := 4983230072969 + 3 ^ 40 * 2240745 * 2
def baseEnd_2240745 : Nat := 1150579209158940808582507

theorem tailTrace_2240745 : CollatzResearch.WordTrace tailWord_2240745 prefixEnd_2240745 1150579209158940808582507 := by
  unfold tailWord_2240745
  simp only [CollatzResearch.WordTrace]
  refine ⟨81726684267171028623699689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54484456178114019082466459 81726684267171028623699689)
  ·
    refine ⟨61295013200378271467774767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81726684267171028623699689 61295013200378271467774767)
    ·
      refine ⟨91942519800567407201662151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61295013200378271467774767 91942519800567407201662151)
      ·
        refine ⟨137913779700851110802493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91942519800567407201662151 137913779700851110802493227)
        ·
          refine ⟨206870669551276666203739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137913779700851110802493227 206870669551276666203739841)
          ·
            refine ⟨155153002163457499652804881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206870669551276666203739841 155153002163457499652804881)
            ·
              refine ⟨116364751622593124739603661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155153002163457499652804881 116364751622593124739603661)
              ·
                refine ⟨43636781858472421777351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116364751622593124739603661 43636781858472421777351373)
                ·
                  refine ⟨16363793196927158166506765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43636781858472421777351373 16363793196927158166506765)
                  ·
                    refine ⟨6136422448847684312440037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16363793196927158166506765 6136422448847684312440037)
                    ·
                      refine ⟨1150579209158940808582507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6136422448847684312440037 1150579209158940808582507)
                      ·
                        rfl

theorem cell23_2240745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_2240745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240745 prefixEnd_2240745 := by exact prefixLift 2240745
  have htrace : WordTrace (prefixWord ++ tailWord_2240745) baseStart_2240745 baseEnd_2240745 := by
    simpa [prefixWord, tailWord_2240745, baseEnd_2240745] using wordTrace_append hprefix tailTrace_2240745
  have hstable : (prefixWord ++ tailWord_2240745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240745).length < 2 ^ (prefixWord ++ tailWord_2240745).sum := by decide
  have hdescent : baseEnd_2240745 < baseStart_2240745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240762 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_2240762 : Nat := 118140960795 + 2240762 * 2 ^ 59
def prefixEnd_2240762 : Nat := 4983230072969 + 3 ^ 40 * 2240762 * 2
def baseEnd_2240762 : Nat := 1150587938330067242069929

theorem tailTrace_2240762 : CollatzResearch.WordTrace tailWord_2240762 prefixEnd_2240762 1150587938330067242069929 := by
  unfold tailWord_2240762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20431826077027360131767135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54484869538739627018045693 20431826077027360131767135)
  ·
    refine ⟨30647739115541040197650703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20431826077027360131767135 30647739115541040197650703)
    ·
      refine ⟨45971608673311560296476055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30647739115541040197650703 45971608673311560296476055)
      ·
        refine ⟨68957413009967340444714083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45971608673311560296476055 68957413009967340444714083)
        ·
          refine ⟨103436119514951010667071125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68957413009967340444714083 103436119514951010667071125)
          ·
            refine ⟨4848568102263328625018959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103436119514951010667071125 4848568102263328625018959)
            ·
              refine ⟨7272852153394992937528439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848568102263328625018959 7272852153394992937528439)
              ·
                refine ⟨10909278230092489406292659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7272852153394992937528439 10909278230092489406292659)
                ·
                  refine ⟨16363917345138734109438989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10909278230092489406292659 16363917345138734109438989)
                  ·
                    refine ⟨6136469004427025291039621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16363917345138734109438989 6136469004427025291039621)
                    ·
                      refine ⟨1150587938330067242069929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6136469004427025291039621 1150587938330067242069929)
                      ·
                        rfl

theorem cell23_2240762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_2240762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240762 prefixEnd_2240762 := by exact prefixLift 2240762
  have htrace : WordTrace (prefixWord ++ tailWord_2240762) baseStart_2240762 baseEnd_2240762 := by
    simpa [prefixWord, tailWord_2240762, baseEnd_2240762] using wordTrace_append hprefix tailTrace_2240762
  have hstable : (prefixWord ++ tailWord_2240762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240762).length < 2 ^ (prefixWord ++ tailWord_2240762).sum := by decide
  have hdescent : baseEnd_2240762 < baseStart_2240762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240853 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 6]
def baseStart_2240853 : Nat := 118140960795 + 2240853 * 2 ^ 59
def prefixEnd_2240853 : Nat := 4983230072969 + 3 ^ 40 * 2240853 * 2
def baseEnd_2240853 : Nat := 127848296118847376225779

theorem tailTrace_2240853 : CollatzResearch.WordTrace tailWord_2240853 prefixEnd_2240853 127848296118847376225779 := by
  unfold tailWord_2240853
  simp only [CollatzResearch.WordTrace]
  refine ⟨81730623350779763068631213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54487082233853175379087475 81730623350779763068631213)
  ·
    refine ⟨30648983756542411150736705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81730623350779763068631213 30648983756542411150736705)
    ·
      refine ⟨22986737817406808363052529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30648983756542411150736705 22986737817406808363052529)
      ·
        refine ⟨17240053363055106272289397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22986737817406808363052529 17240053363055106272289397)
        ·
          refine ⟨1616255002786416213027131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17240053363055106272289397 1616255002786416213027131)
          ·
            refine ⟨2424382504179624319540697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616255002786416213027131 2424382504179624319540697)
            ·
              refine ⟨1818286878134718239655523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424382504179624319540697 1818286878134718239655523)
              ·
                refine ⟨2727430317202077359483285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818286878134718239655523 2727430317202077359483285)
                ·
                  refine ⟨127848296118847376225779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2727430317202077359483285 127848296118847376225779)
                  ·
                    rfl

theorem cell23_2240853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_2240853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240853 prefixEnd_2240853 := by exact prefixLift 2240853
  have htrace : WordTrace (prefixWord ++ tailWord_2240853) baseStart_2240853 baseEnd_2240853 := by
    simpa [prefixWord, tailWord_2240853, baseEnd_2240853] using wordTrace_append hprefix tailTrace_2240853
  have hstable : (prefixWord ++ tailWord_2240853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240853).length < 2 ^ (prefixWord ++ tailWord_2240853).sum := by decide
  have hdescent : baseEnd_2240853 < baseStart_2240853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240866 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2240866 : Nat := 118140960795 + 2240866 * 2 ^ 59
def prefixEnd_2240866 : Nat := 4983230072969 + 3 ^ 40 * 2240866 * 2
def baseEnd_2240866 : Nat := 383547113439378278389817

theorem tailTrace_2240866 : CollatzResearch.WordTrace tailWord_2240866 prefixEnd_2240866 383547113439378278389817 := by
  unfold tailWord_2240866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20432774374933166572213613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54487398333155110859236301 20432774374933166572213613)
  ·
    refine ⟨7662290390599937464580105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20432774374933166572213613 7662290390599937464580105)
    ·
      refine ⟨5746717792949953098435079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662290390599937464580105 5746717792949953098435079)
      ·
        refine ⟨8620076689424929647652619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746717792949953098435079 8620076689424929647652619)
        ·
          refine ⟨12930115034137394471478929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8620076689424929647652619 12930115034137394471478929)
          ·
            refine ⟨9697586275603045853609197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12930115034137394471478929 9697586275603045853609197)
            ·
              refine ⟨3636594853351142195103449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9697586275603045853609197 3636594853351142195103449)
              ·
                refine ⟨2727446140013356646327587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3636594853351142195103449 2727446140013356646327587)
                ·
                  refine ⟨4091169210020034969491381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727446140013356646327587 4091169210020034969491381)
                  ·
                    refine ⟨383547113439378278389817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4091169210020034969491381 383547113439378278389817)
                    ·
                      rfl

theorem cell23_2240866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2240866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240866 prefixEnd_2240866 := by exact prefixLift 2240866
  have htrace : WordTrace (prefixWord ++ tailWord_2240866) baseStart_2240866 baseEnd_2240866 := by
    simpa [prefixWord, tailWord_2240866, baseEnd_2240866] using wordTrace_append hprefix tailTrace_2240866
  have hstable : (prefixWord ++ tailWord_2240866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240866).length < 2 ^ (prefixWord ++ tailWord_2240866).sum := by decide
  have hdescent : baseEnd_2240866 < baseStart_2240866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240869 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2240869 : Nat := 118140960795 + 2240869 * 2 ^ 59
def prefixEnd_2240869 : Nat := 4983230072969 + 3 ^ 40 * 2240869 * 2
def baseEnd_2240869 : Nat := 1150642880760098323431937

theorem tailTrace_2240869 : CollatzResearch.WordTrace tailWord_2240869 prefixEnd_2240869 1150642880760098323431937 := by
  unfold tailWord_2240869
  simp only [CollatzResearch.WordTrace]
  refine ⟨81731206918721797801213661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54487471279147865200809107 81731206918721797801213661)
  ·
    refine ⟨30649202594520674175455123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81731206918721797801213661 30649202594520674175455123)
    ·
      refine ⟨45973803891781011263182685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30649202594520674175455123 45973803891781011263182685)
      ·
        refine ⟨17240176459417879223693507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45973803891781011263182685 17240176459417879223693507)
        ·
          refine ⟨25860264689126818835540261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17240176459417879223693507 25860264689126818835540261)
          ·
            refine ⟨4848799629211278531663799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25860264689126818835540261 4848799629211278531663799)
            ·
              refine ⟨7273199443816917797495699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848799629211278531663799 7273199443816917797495699)
              ·
                refine ⟨10909799165725376696243549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273199443816917797495699 10909799165725376696243549)
                ·
                  refine ⟨4091174687147016261091331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10909799165725376696243549 4091174687147016261091331)
                  ·
                    refine ⟨6136762030720524391636997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4091174687147016261091331 6136762030720524391636997)
                    ·
                      refine ⟨1150642880760098323431937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6136762030720524391636997 1150642880760098323431937)
                      ·
                        rfl

theorem cell23_2240869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2240869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240869 prefixEnd_2240869 := by exact prefixLift 2240869
  have htrace : WordTrace (prefixWord ++ tailWord_2240869) baseStart_2240869 baseEnd_2240869 := by
    simpa [prefixWord, tailWord_2240869, baseEnd_2240869] using wordTrace_append hprefix tailTrace_2240869
  have hstable : (prefixWord ++ tailWord_2240869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240869).length < 2 ^ (prefixWord ++ tailWord_2240869).sum := by decide
  have hdescent : baseEnd_2240869 < baseStart_2240869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240897 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2240897 : Nat := 118140960795 + 2240897 * 2 ^ 59
def prefixEnd_2240897 : Nat := 4983230072969 + 3 ^ 40 * 2240897 * 2
def baseEnd_2240897 : Nat := 1150657258218424213881809

theorem tailTrace_2240897 : CollatzResearch.WordTrace tailWord_2240897 prefixEnd_2240897 1150657258218424213881809 := by
  unfold tailWord_2240897
  simp only [CollatzResearch.WordTrace]
  refine ⟨81732228162620358583232945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54488152108413572388821963 81732228162620358583232945)
  ·
    refine ⟨61299171121965268937424709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81732228162620358583232945 61299171121965268937424709)
    ·
      refine ⟨11493594585368487925767133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61299171121965268937424709 11493594585368487925767133)
      ·
        refine ⟨4310097969513182972162675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11493594585368487925767133 4310097969513182972162675)
        ·
          refine ⟨6465146954269774458244013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310097969513182972162675 6465146954269774458244013)
          ·
            refine ⟨2424430107851165421841505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6465146954269774458244013 2424430107851165421841505)
            ·
              refine ⟨1818322580888374066381129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2424430107851165421841505 1818322580888374066381129)
              ·
                refine ⟨1363741935666280549785847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818322580888374066381129 1363741935666280549785847)
                ·
                  refine ⟨2045612903499420824678771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363741935666280549785847 2045612903499420824678771)
                  ·
                    refine ⟨3068419355249131237018157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045612903499420824678771 3068419355249131237018157)
                    ·
                      refine ⟨1150657258218424213881809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068419355249131237018157 1150657258218424213881809)
                      ·
                        rfl

theorem cell23_2240897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2240897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240897 prefixEnd_2240897 := by exact prefixLift 2240897
  have htrace : WordTrace (prefixWord ++ tailWord_2240897) baseStart_2240897 baseEnd_2240897 := by
    simpa [prefixWord, tailWord_2240897, baseEnd_2240897] using wordTrace_append hprefix tailTrace_2240897
  have hstable : (prefixWord ++ tailWord_2240897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240897).length < 2 ^ (prefixWord ++ tailWord_2240897).sum := by decide
  have hdescent : baseEnd_2240897 < baseStart_2240897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240919 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2240919 : Nat := 118140960795 + 2240919 * 2 ^ 59
def prefixEnd_2240919 : Nat := 4983230072969 + 3 ^ 40 * 2240919 * 2
def baseEnd_2240919 : Nat := 1150668554792823127806707

theorem tailTrace_2240919 : CollatzResearch.WordTrace tailWord_2240919 prefixEnd_2240919 1150668554792823127806707 := by
  unfold tailWord_2240919
  simp only [CollatzResearch.WordTrace]
  refine ⟨81733030568540656340533811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54488687045693770893689207 81733030568540656340533811)
  ·
    refine ⟨122599545852810984510800717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81733030568540656340533811 122599545852810984510800717)
    ·
      refine ⟨45974829694804119191550269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122599545852810984510800717 45974829694804119191550269)
      ·
        refine ⟨17240561135551544696831351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45974829694804119191550269 17240561135551544696831351)
        ·
          refine ⟨25860841703327317045247027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17240561135551544696831351 25860841703327317045247027)
          ·
            refine ⟨38791262554990975567870541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25860841703327317045247027 38791262554990975567870541)
            ·
              refine ⟨14546723458121615837951453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38791262554990975567870541 14546723458121615837951453)
              ·
                refine ⟨5455021296795605939231795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14546723458121615837951453 5455021296795605939231795)
                ·
                  refine ⟨8182531945193408908847693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455021296795605939231795 8182531945193408908847693)
                  ·
                    refine ⟨3068449479447528340817885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8182531945193408908847693 3068449479447528340817885)
                    ·
                      refine ⟨1150668554792823127806707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068449479447528340817885 1150668554792823127806707)
                      ·
                        rfl

theorem cell23_2240919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2240919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240919 prefixEnd_2240919 := by exact prefixLift 2240919
  have htrace : WordTrace (prefixWord ++ tailWord_2240919) baseStart_2240919 baseEnd_2240919 := by
    simpa [prefixWord, tailWord_2240919, baseEnd_2240919] using wordTrace_append hprefix tailTrace_2240919
  have hstable : (prefixWord ++ tailWord_2240919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240919).length < 2 ^ (prefixWord ++ tailWord_2240919).sum := by decide
  have hdescent : baseEnd_2240919 < baseStart_2240919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240953 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2240953 : Nat := 118140960795 + 2240953 * 2 ^ 59
def prefixEnd_2240953 : Nat := 4983230072969 + 3 ^ 40 * 2240953 * 2
def baseEnd_2240953 : Nat := 1150686013135075994781551

theorem tailTrace_2240953 : CollatzResearch.WordTrace tailWord_2240953 prefixEnd_2240953 1150686013135075994781551 := by
  unfold tailWord_2240953
  simp only [CollatzResearch.WordTrace]
  refine ⟨81734270650417480147271513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54489513766944986764847675 81734270650417480147271513)
  ·
    refine ⟨61300702987813110110453635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81734270650417480147271513 61300702987813110110453635)
    ·
      refine ⟨91951054481719665165680453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61300702987813110110453635 91951054481719665165680453)
      ·
        refine ⟨17240822715322437218565085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91951054481719665165680453 17240822715322437218565085)
        ·
          refine ⟨6465308518245913956961907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17240822715322437218565085 6465308518245913956961907)
          ·
            refine ⟨9697962777368870935442861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6465308518245913956961907 9697962777368870935442861)
            ·
              refine ⟨3636736041513326600791073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9697962777368870935442861 3636736041513326600791073)
              ·
                refine ⟨2727552031134994950593305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3636736041513326600791073 2727552031134994950593305)
                ·
                  refine ⟨2045664023351246212944979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727552031134994950593305 2045664023351246212944979)
                  ·
                    refine ⟨3068496035026869319417469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045664023351246212944979 3068496035026869319417469)
                    ·
                      refine ⟨1150686013135075994781551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068496035026869319417469 1150686013135075994781551)
                      ·
                        rfl

theorem cell23_2240953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2240953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240953 prefixEnd_2240953 := by exact prefixLift 2240953
  have htrace : WordTrace (prefixWord ++ tailWord_2240953) baseStart_2240953 baseEnd_2240953 := by
    simpa [prefixWord, tailWord_2240953, baseEnd_2240953] using wordTrace_append hprefix tailTrace_2240953
  have hstable : (prefixWord ++ tailWord_2240953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240953).length < 2 ^ (prefixWord ++ tailWord_2240953).sum := by decide
  have hdescent : baseEnd_2240953 < baseStart_2240953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240959 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 8, 2]
def baseStart_2240959 : Nat := 118140960795 + 2240959 * 2 ^ 59
def prefixEnd_2240959 : Nat := 4983230072969 + 3 ^ 40 * 2240959 * 2
def baseEnd_2240959 : Nat := 1150689094019002971306523

theorem tailTrace_2240959 : CollatzResearch.WordTrace tailWord_2240959 prefixEnd_2240959 1150689094019002971306523 := by
  unfold tailWord_2240959
  simp only [CollatzResearch.WordTrace]
  refine ⟨81734489488395743171989931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54489659658930495447993287 81734489488395743171989931)
  ·
    refine ⟨122601734232593614757984897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81734489488395743171989931 122601734232593614757984897)
    ·
      refine ⟨91951300674445211068488673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122601734232593614757984897 91951300674445211068488673)
      ·
        refine ⟨68963475505833908301366505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91951300674445211068488673 68963475505833908301366505)
        ·
          refine ⟨51722606629375431226024879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68963475505833908301366505 51722606629375431226024879)
          ·
            refine ⟨77583909944063146839037319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51722606629375431226024879 77583909944063146839037319)
            ·
              refine ⟨116375864916094720258555979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77583909944063146839037319 116375864916094720258555979)
              ·
                refine ⟨174563797374142080387833969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116375864916094720258555979 174563797374142080387833969)
                ·
                  refine ⟨130922848030606560290875477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174563797374142080387833969 130922848030606560290875477)
                  ·
                    refine ⟨1534252125358670628408697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 130922848030606560290875477 1534252125358670628408697)
                    ·
                      refine ⟨1150689094019002971306523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534252125358670628408697 1150689094019002971306523)
                      ·
                        rfl

theorem cell23_2240959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_2240959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240959 prefixEnd_2240959 := by exact prefixLift 2240959
  have htrace : WordTrace (prefixWord ++ tailWord_2240959) baseStart_2240959 baseEnd_2240959 := by
    simpa [prefixWord, tailWord_2240959, baseEnd_2240959] using wordTrace_append hprefix tailTrace_2240959
  have hstable : (prefixWord ++ tailWord_2240959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240959).length < 2 ^ (prefixWord ++ tailWord_2240959).sum := by decide
  have hdescent : baseEnd_2240959 < baseStart_2240959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240976 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2]
def baseStart_2240976 : Nat := 118140960795 + 2240976 * 2 ^ 59
def prefixEnd_2240976 : Nat := 4983230072969 + 3 ^ 40 * 2240976 * 2
def baseEnd_2240976 : Nat := 1150697823190129404793945

theorem tailTrace_2240976 : CollatzResearch.WordTrace tailWord_2240976 prefixEnd_2240976 1150697823190129404793945 := by
  unfold tailWord_2240976
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867554764667077537679391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54490073019556103383572521 40867554764667077537679391)
  ·
    refine ⟨61301332147000616306519087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40867554764667077537679391 61301332147000616306519087)
    ·
      refine ⟨91951998220500924459778631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61301332147000616306519087 91951998220500924459778631)
      ·
        refine ⟨137927997330751386689667947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91951998220500924459778631 137927997330751386689667947)
        ·
          refine ⟨206891995996127080034501921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137927997330751386689667947 206891995996127080034501921)
          ·
            refine ⟨155168996997095310025876441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206891995996127080034501921 155168996997095310025876441)
            ·
              refine ⟨116376747747821482519407331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155168996997095310025876441 116376747747821482519407331)
              ·
                refine ⟨174565121621732223779110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116376747747821482519407331 174565121621732223779110997)
                ·
                  refine ⟨2045685019004674497411457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 174565121621732223779110997 2045685019004674497411457)
                  ·
                    refine ⟨1534263764253505873058593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045685019004674497411457 1534263764253505873058593)
                    ·
                      refine ⟨1150697823190129404793945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534263764253505873058593 1150697823190129404793945)
                      ·
                        rfl

theorem cell23_2240976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 8, 2, 2].length) (baseStart_2240976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240976 prefixEnd_2240976 := by exact prefixLift 2240976
  have htrace : WordTrace (prefixWord ++ tailWord_2240976) baseStart_2240976 baseEnd_2240976 := by
    simpa [prefixWord, tailWord_2240976, baseEnd_2240976] using wordTrace_append hprefix tailTrace_2240976
  have hstable : (prefixWord ++ tailWord_2240976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240976).length < 2 ^ (prefixWord ++ tailWord_2240976).sum := by decide
  have hdescent : baseEnd_2240976 < baseStart_2240976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2240980 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2240980 : Nat := 118140960795 + 2240980 * 2 ^ 59
def prefixEnd_2240980 : Nat := 4983230072969 + 3 ^ 40 * 2240980 * 2
def baseEnd_2240980 : Nat := 1150699877112747389143927

theorem tailTrace_2240980 : CollatzResearch.WordTrace tailWord_2240980 prefixEnd_2240980 1150699877112747389143927 := by
  unfold tailWord_2240980
  simp only [CollatzResearch.WordTrace]
  refine ⟨40867627710659831879252197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54490170280879775839002929 40867627710659831879252197)
  ·
    refine ⟨7662680195748718477359787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40867627710659831879252197 7662680195748718477359787)
    ·
      refine ⟨11494020293623077716039681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662680195748718477359787 11494020293623077716039681)
      ·
        refine ⟨8620515220217308287029761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11494020293623077716039681 8620515220217308287029761)
        ·
          refine ⟨6465386415162981215272321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8620515220217308287029761 6465386415162981215272321)
          ·
            refine ⟨4849039811372235911454241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6465386415162981215272321 4849039811372235911454241)
            ·
              refine ⟨3636779858529176933590681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849039811372235911454241 3636779858529176933590681)
              ·
                refine ⟨2727584893896882700193011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3636779858529176933590681 2727584893896882700193011)
                ·
                  refine ⟨4091377340845324050289517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727584893896882700193011 4091377340845324050289517)
                  ·
                    refine ⟨1534266502816996518858569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4091377340845324050289517 1534266502816996518858569)
                    ·
                      refine ⟨1150699877112747389143927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534266502816996518858569 1150699877112747389143927)
                      ·
                        rfl

theorem cell23_2240980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2240980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2240980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2240980 prefixEnd_2240980 := by exact prefixLift 2240980
  have htrace : WordTrace (prefixWord ++ tailWord_2240980) baseStart_2240980 baseEnd_2240980 := by
    simpa [prefixWord, tailWord_2240980, baseEnd_2240980] using wordTrace_append hprefix tailTrace_2240980
  have hstable : (prefixWord ++ tailWord_2240980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2240980).length < 2 ^ (prefixWord ++ tailWord_2240980).sum := by decide
  have hdescent : baseEnd_2240980 < baseStart_2240980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2240980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241030 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2241030 : Nat := 118140960795 + 2241030 * 2 ^ 59
def prefixEnd_2241030 : Nat := 4983230072969 + 3 ^ 40 * 2241030 * 2
def baseEnd_2241030 : Nat := 1150725551145472193518697

theorem tailTrace_2241030 : CollatzResearch.WordTrace tailWord_2241030 prefixEnd_2241030 1150725551145472193518697 := by
  unfold tailWord_2241030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554283720973078821807017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54491386047425681531883029 2554283720973078821807017)
  ·
    refine ⟨1915712790729809116355263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554283720973078821807017 1915712790729809116355263)
    ·
      refine ⟨2873569186094713674532895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915712790729809116355263 2873569186094713674532895)
      ·
        refine ⟨4310353779142070511799343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2873569186094713674532895 4310353779142070511799343)
        ·
          refine ⟨6465530668713105767699015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310353779142070511799343 6465530668713105767699015)
          ·
            refine ⟨9698296003069658651548523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6465530668713105767699015 9698296003069658651548523)
            ·
              refine ⟨14547444004604487977322785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9698296003069658651548523 14547444004604487977322785)
              ·
                refine ⟨10910583003453365982992089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14547444004604487977322785 10910583003453365982992089)
                ·
                  refine ⟨8182937252590024487244067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10910583003453365982992089 8182937252590024487244067)
                  ·
                    refine ⟨12274405878885036730866101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8182937252590024487244067 12274405878885036730866101)
                    ·
                      refine ⟨1150725551145472193518697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12274405878885036730866101 1150725551145472193518697)
                      ·
                        rfl

theorem cell23_2241030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2241030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241030 prefixEnd_2241030 := by exact prefixLift 2241030
  have htrace : WordTrace (prefixWord ++ tailWord_2241030) baseStart_2241030 baseEnd_2241030 := by
    simpa [prefixWord, tailWord_2241030, baseEnd_2241030] using wordTrace_append hprefix tailTrace_2241030
  have hstable : (prefixWord ++ tailWord_2241030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241030).length < 2 ^ (prefixWord ++ tailWord_2241030).sum := by decide
  have hdescent : baseEnd_2241030 < baseStart_2241030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241049 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_2241049 : Nat := 118140960795 + 2241049 * 2 ^ 59
def prefixEnd_2241049 : Nat := 4983230072969 + 3 ^ 40 * 2241049 * 2
def baseEnd_2241049 : Nat := 1150735307277907619181109

theorem tailTrace_2241049 : CollatzResearch.WordTrace tailWord_2241049 prefixEnd_2241049 1150735307277907619181109 := by
  unfold tailWord_2241049
  simp only [CollatzResearch.WordTrace]
  refine ⟨81737772058069688542766201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54491848038713125695177467 81737772058069688542766201)
  ·
    refine ⟨61303329043552266407074651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81737772058069688542766201 61303329043552266407074651)
    ·
      refine ⟨91954993565328399610611977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61303329043552266407074651 91954993565328399610611977)
      ·
        refine ⟨68966245173996299707958983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91954993565328399610611977 68966245173996299707958983)
        ·
          refine ⟨103449367760994449561938475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68966245173996299707958983 103449367760994449561938475)
          ·
            refine ⟨155174051641491674342907713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103449367760994449561938475 155174051641491674342907713)
            ·
              refine ⟨116380538731118755757180785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155174051641491674342907713 116380538731118755757180785)
              ·
                refine ⟨87285404048339066817885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116380538731118755757180785 87285404048339066817885589)
                ·
                  refine ⟨4091503314765893757088387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87285404048339066817885589 4091503314765893757088387)
                  ·
                    refine ⟨6137254972148840635632581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4091503314765893757088387 6137254972148840635632581)
                    ·
                      refine ⟨1150735307277907619181109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6137254972148840635632581 1150735307277907619181109)
                      ·
                        rfl

theorem cell23_2241049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_2241049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241049 prefixEnd_2241049 := by exact prefixLift 2241049
  have htrace : WordTrace (prefixWord ++ tailWord_2241049) baseStart_2241049 baseEnd_2241049 := by
    simpa [prefixWord, tailWord_2241049, baseEnd_2241049] using wordTrace_append hprefix tailTrace_2241049
  have hstable : (prefixWord ++ tailWord_2241049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241049).length < 2 ^ (prefixWord ++ tailWord_2241049).sum := by decide
  have hdescent : baseEnd_2241049 < baseStart_2241049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241139 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_2241139 : Nat := 118140960795 + 2241139 * 2 ^ 59
def prefixEnd_2241139 : Nat := 4983230072969 + 3 ^ 40 * 2241139 * 2
def baseEnd_2241139 : Nat := 1150781520536812267055695

theorem tailTrace_2241139 : CollatzResearch.WordTrace tailWord_2241139 prefixEnd_2241139 1150781520536812267055695 := by
  unfold tailWord_2241139
  simp only [CollatzResearch.WordTrace]
  refine ⟨81741054627743633913542471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54494036418495755942361647 81741054627743633913542471)
  ·
    refine ⟨122611581941615450870313707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81741054627743633913542471 122611581941615450870313707)
    ·
      refine ⟨183917372912423176305470561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122611581941615450870313707 183917372912423176305470561)
      ·
        refine ⟨137938029684317382229102921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183917372912423176305470561 137938029684317382229102921)
        ·
          refine ⟨103453522263238036671827191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137938029684317382229102921 103453522263238036671827191)
          ·
            refine ⟨155180283394857055007740787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103453522263238036671827191 155180283394857055007740787)
            ·
              refine ⟨232770425092285582511611181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155180283394857055007740787 232770425092285582511611181)
              ·
                refine ⟨87288909409607093441854193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232770425092285582511611181 87288909409607093441854193)
                ·
                  refine ⟨65466682057205320081390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87288909409607093441854193 65466682057205320081390645)
                  ·
                    refine ⟨6137501442862998757630373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65466682057205320081390645 6137501442862998757630373)
                    ·
                      refine ⟨1150781520536812267055695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6137501442862998757630373 1150781520536812267055695)
                      ·
                        rfl

theorem cell23_2241139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_2241139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241139 prefixEnd_2241139 := by exact prefixLift 2241139
  have htrace : WordTrace (prefixWord ++ tailWord_2241139) baseStart_2241139 baseEnd_2241139 := by
    simpa [prefixWord, tailWord_2241139, baseEnd_2241139] using wordTrace_append hprefix tailTrace_2241139
  have hstable : (prefixWord ++ tailWord_2241139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241139).length < 2 ^ (prefixWord ++ tailWord_2241139).sum := by decide
  have hdescent : baseEnd_2241139 < baseStart_2241139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241153 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2241153 : Nat := 118140960795 + 2241153 * 2 ^ 59
def prefixEnd_2241153 : Nat := 4983230072969 + 3 ^ 40 * 2241153 * 2
def baseEnd_2241153 : Nat := 383596236421991737426877

theorem tailTrace_2241153 : CollatzResearch.WordTrace tailWord_2241153 prefixEnd_2241153 383596236421991737426877 := by
  unfold tailWord_2241153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81741565249692914304552113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54494376833128609536368075 81741565249692914304552113)
  ·
    refine ⟨61306173937269685728414085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81741565249692914304552113 61306173937269685728414085)
    ·
      refine ⟨11494907613238066074077641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61306173937269685728414085 11494907613238066074077641)
      ·
        refine ⟨8621180709928549555558231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11494907613238066074077641 8621180709928549555558231)
        ·
          refine ⟨12931771064892824333337347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621180709928549555558231 12931771064892824333337347)
          ·
            refine ⟨19397656597339236500006021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931771064892824333337347 19397656597339236500006021)
            ·
              refine ⟨3637060612001106843751129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19397656597339236500006021 3637060612001106843751129)
              ·
                refine ⟨2727795459000830132813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3637060612001106843751129 2727795459000830132813347)
                ·
                  refine ⟨4091693188501245199220021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727795459000830132813347 4091693188501245199220021)
                  ·
                    refine ⟨383596236421991737426877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4091693188501245199220021 383596236421991737426877)
                    ·
                      rfl

theorem cell23_2241153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2241153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241153 prefixEnd_2241153 := by exact prefixLift 2241153
  have htrace : WordTrace (prefixWord ++ tailWord_2241153) baseStart_2241153 baseEnd_2241153 := by
    simpa [prefixWord, tailWord_2241153, baseEnd_2241153] using wordTrace_append hprefix tailTrace_2241153
  have hstable : (prefixWord ++ tailWord_2241153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241153).length < 2 ^ (prefixWord ++ tailWord_2241153).sum := by decide
  have hdescent : baseEnd_2241153 < baseStart_2241153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241166 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2241166 : Nat := 118140960795 + 2241166 * 2 ^ 59
def prefixEnd_2241166 : Nat := 4983230072969 + 3 ^ 40 * 2241166 * 2
def baseEnd_2241166 : Nat := 383598461504827887139357

theorem tailTrace_2241166 : CollatzResearch.WordTrace tailWord_2241166 prefixEnd_2241166 383598461504827887139357 := by
  unfold tailWord_2241166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217754924830727190596919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54494692932430545016516901 10217754924830727190596919)
  ·
    refine ⟨15326632387246090785895379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217754924830727190596919 15326632387246090785895379)
    ·
      refine ⟨22989948580869136178843069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15326632387246090785895379 22989948580869136178843069)
      ·
        refine ⟨8621230717825926067066151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22989948580869136178843069 8621230717825926067066151)
        ·
          refine ⟨12931846076738889100599227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621230717825926067066151 12931846076738889100599227)
          ·
            refine ⟨19397769115108333650898841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931846076738889100599227 19397769115108333650898841)
            ·
              refine ⟨14548326836331250238174131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19397769115108333650898841 14548326836331250238174131)
              ·
                refine ⟨21822490254496875357261197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14548326836331250238174131 21822490254496875357261197)
                ·
                  refine ⟨8183433845436328258972949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21822490254496875357261197 8183433845436328258972949)
                  ·
                    refine ⟨383598461504827887139357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8183433845436328258972949 383598461504827887139357)
                    ·
                      rfl

theorem cell23_2241166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2241166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241166 prefixEnd_2241166 := by exact prefixLift 2241166
  have htrace : WordTrace (prefixWord ++ tailWord_2241166) baseStart_2241166 baseEnd_2241166 := by
    simpa [prefixWord, tailWord_2241166, baseEnd_2241166] using wordTrace_append hprefix tailTrace_2241166
  have hstable : (prefixWord ++ tailWord_2241166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241166).length < 2 ^ (prefixWord ++ tailWord_2241166).sum := by decide
  have hdescent : baseEnd_2241166 < baseStart_2241166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241184 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 1, 1, 3]
def baseStart_2241184 : Nat := 118140960795 + 2241184 * 2 ^ 59
def prefixEnd_2241184 : Nat := 4983230072969 + 3 ^ 40 * 2241184 * 2
def baseEnd_2241184 : Nat := 1150804627166264590992989

theorem tailTrace_2241184 : CollatzResearch.WordTrace tailWord_2241184 prefixEnd_2241184 1150804627166264590992989 := by
  unfold tailWord_2241184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40871347956290303299465303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54495130608387071065953737 40871347956290303299465303)
  ·
    refine ⟨61307021934435454949197955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40871347956290303299465303 61307021934435454949197955)
    ·
      refine ⟨91960532901653182423796933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61307021934435454949197955 91960532901653182423796933)
      ·
        refine ⟨17242599919059971704461925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91960532901653182423796933 17242599919059971704461925)
        ·
          refine ⟨3232987484823744694586611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17242599919059971704461925 3232987484823744694586611)
          ·
            refine ⟨4849481227235617041879917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232987484823744694586611 4849481227235617041879917)
            ·
              refine ⟨1818555460213356390704969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4849481227235617041879917 1818555460213356390704969)
              ·
                refine ⟨1363916595160017293028727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818555460213356390704969 1363916595160017293028727)
                ·
                  refine ⟨2045874892740025939543091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1363916595160017293028727 2045874892740025939543091)
                  ·
                    refine ⟨3068812339110038909314637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045874892740025939543091 3068812339110038909314637)
                    ·
                      refine ⟨1150804627166264590992989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068812339110038909314637 1150804627166264590992989)
                      ·
                        rfl

theorem cell23_2241184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_2241184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241184 prefixEnd_2241184 := by exact prefixLift 2241184
  have htrace : WordTrace (prefixWord ++ tailWord_2241184) baseStart_2241184 baseEnd_2241184 := by
    simpa [prefixWord, tailWord_2241184, baseEnd_2241184] using wordTrace_append hprefix tailTrace_2241184
  have hstable : (prefixWord ++ tailWord_2241184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241184).length < 2 ^ (prefixWord ++ tailWord_2241184).sum := by decide
  have hdescent : baseEnd_2241184 < baseStart_2241184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241207 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_2241207 : Nat := 118140960795 + 2241207 * 2 ^ 59
def prefixEnd_2241207 : Nat := 4983230072969 + 3 ^ 40 * 2241207 * 2
def baseEnd_2241207 : Nat := 1150816437221318001005383

theorem tailTrace_2241207 : CollatzResearch.WordTrace tailWord_2241207 prefixEnd_2241207 1150816437221318001005383 := by
  unfold tailWord_2241207
  simp only [CollatzResearch.WordTrace]
  refine ⟨81743534791497281527017875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54495689860998187684678583 81743534791497281527017875)
  ·
    refine ⟨122615302187245922290526813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81743534791497281527017875 122615302187245922290526813)
    ·
      refine ⟨45980738320217220858947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122615302187245922290526813 45980738320217220858947555)
      ·
        refine ⟨68971107480325831288421333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45980738320217220858947555 68971107480325831288421333)
        ·
          refine ⟨1616510331570136670822375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68971107480325831288421333 1616510331570136670822375)
          ·
            refine ⟨2424765497355205006233563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616510331570136670822375 2424765497355205006233563)
            ·
              refine ⟨3637148246032807509350345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424765497355205006233563 3637148246032807509350345)
              ·
                refine ⟨2727861184524605632012759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3637148246032807509350345 2727861184524605632012759)
                ·
                  refine ⟨4091791776786908448019139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727861184524605632012759 4091791776786908448019139)
                  ·
                    refine ⟨6137687665180362672028709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4091791776786908448019139 6137687665180362672028709)
                    ·
                      refine ⟨1150816437221318001005383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6137687665180362672028709 1150816437221318001005383)
                      ·
                        rfl

theorem cell23_2241207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_2241207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241207 prefixEnd_2241207 := by exact prefixLift 2241207
  have htrace : WordTrace (prefixWord ++ tailWord_2241207) baseStart_2241207 baseEnd_2241207 := by
    simpa [prefixWord, tailWord_2241207, baseEnd_2241207] using wordTrace_append hprefix tailTrace_2241207
  have hstable : (prefixWord ++ tailWord_2241207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241207).length < 2 ^ (prefixWord ++ tailWord_2241207).sum := by decide
  have hdescent : baseEnd_2241207 < baseStart_2241207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241223 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_2241223 : Nat := 118140960795 + 2241223 * 2 ^ 59
def prefixEnd_2241223 : Nat := 4983230072969 + 3 ^ 40 * 2241223 * 2
def baseEnd_2241223 : Nat := 1150824652911789938405309

theorem tailTrace_2241223 : CollatzResearch.WordTrace tailWord_2241223 prefixEnd_2241223 1150824652911789938405309 := by
  unfold tailWord_2241223
  simp only [CollatzResearch.WordTrace]
  refine ⟨81744118359439316259600323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54496078906292877506400215 81744118359439316259600323)
  ·
    refine ⟨122616177539158974389400485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81744118359439316259600323 122616177539158974389400485)
    ·
      refine ⟨22990533288592307698012591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122616177539158974389400485 22990533288592307698012591)
      ·
        refine ⟨34485799932888461547018887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22990533288592307698012591 34485799932888461547018887)
        ·
          refine ⟨51728699899332692320528331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34485799932888461547018887 51728699899332692320528331)
          ·
            refine ⟨77593049848999038480792497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51728699899332692320528331 77593049848999038480792497)
            ·
              refine ⟨58194787386749278860594373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77593049848999038480792497 58194787386749278860594373)
              ·
                refine ⟨10911522635015489786361445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58194787386749278860594373 10911522635015489786361445)
                ·
                  refine ⟨2045910494065404334942771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10911522635015489786361445 2045910494065404334942771)
                  ·
                    refine ⟨3068865741098106502414157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045910494065404334942771 3068865741098106502414157)
                    ·
                      refine ⟨1150824652911789938405309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068865741098106502414157 1150824652911789938405309)
                      ·
                        rfl

theorem cell23_2241223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_2241223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241223 prefixEnd_2241223 := by exact prefixLift 2241223
  have htrace : WordTrace (prefixWord ++ tailWord_2241223) baseStart_2241223 baseEnd_2241223 := by
    simpa [prefixWord, tailWord_2241223, baseEnd_2241223] using wordTrace_append hprefix tailTrace_2241223
  have hstable : (prefixWord ++ tailWord_2241223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241223).length < 2 ^ (prefixWord ++ tailWord_2241223).sum := by decide
  have hdescent : baseEnd_2241223 < baseStart_2241223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241240 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_2241240 : Nat := 118140960795 + 2241240 * 2 ^ 59
def prefixEnd_2241240 : Nat := 4983230072969 + 3 ^ 40 * 2241240 * 2
def baseEnd_2241240 : Nat := 1150833382082916371892731

theorem tailTrace_2241240 : CollatzResearch.WordTrace tailWord_2241240 prefixEnd_2241240 1150833382082916371892731 := by
  unfold tailWord_2241240
  simp only [CollatzResearch.WordTrace]
  refine ⟨40872369200188864081484587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54496492266918485441979449 40872369200188864081484587)
  ·
    refine ⟨61308553800283296122226881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40872369200188864081484587 61308553800283296122226881)
    ·
      refine ⟨45981415350212472091670161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61308553800283296122226881 45981415350212472091670161)
      ·
        refine ⟨34486061512659354068752621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45981415350212472091670161 34486061512659354068752621)
        ·
          refine ⟨12932273067247257775782233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34486061512659354068752621 12932273067247257775782233)
          ·
            refine ⟨9699204800435443331836675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12932273067247257775782233 9699204800435443331836675)
            ·
              refine ⟨14548807200653164997755013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9699204800435443331836675 14548807200653164997755013)
              ·
                refine ⟨2727901350122468437079065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14548807200653164997755013 2727901350122468437079065)
                ·
                  refine ⟨2045926012591851327809299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727901350122468437079065 2045926012591851327809299)
                  ·
                    refine ⟨3068889018887776991713949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2045926012591851327809299 3068889018887776991713949)
                    ·
                      refine ⟨1150833382082916371892731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068889018887776991713949 1150833382082916371892731)
                      ·
                        rfl

theorem cell23_2241240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_2241240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241240 prefixEnd_2241240 := by exact prefixLift 2241240
  have htrace : WordTrace (prefixWord ++ tailWord_2241240) baseStart_2241240 baseEnd_2241240 := by
    simpa [prefixWord, tailWord_2241240, baseEnd_2241240] using wordTrace_append hprefix tailTrace_2241240
  have hstable : (prefixWord ++ tailWord_2241240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241240).length < 2 ^ (prefixWord ++ tailWord_2241240).sum := by decide
  have hdescent : baseEnd_2241240 < baseStart_2241240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241297 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_2241297 : Nat := 118140960795 + 2241297 * 2 ^ 59
def prefixEnd_2241297 : Nat := 4983230072969 + 3 ^ 40 * 2241297 * 2
def baseEnd_2241297 : Nat := 1150862650480222648879969

theorem tailTrace_2241297 : CollatzResearch.WordTrace tailWord_2241297 prefixEnd_2241297 1150862650480222648879969 := by
  unfold tailWord_2241297
  simp only [CollatzResearch.WordTrace]
  refine ⟨81746817361171226897794145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54497878240780817931862763 81746817361171226897794145)
  ·
    refine ⟨61310113020878420173345609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81746817361171226897794145 61310113020878420173345609)
    ·
      refine ⟨45982584765658815130009207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61310113020878420173345609 45982584765658815130009207)
      ·
        refine ⟨68973877148488222695013811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45982584765658815130009207 68973877148488222695013811)
        ·
          refine ⟨103460815722732334042520717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68973877148488222695013811 103460815722732334042520717)
          ·
            refine ⟨38797805896024625265945269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103460815722732334042520717 38797805896024625265945269)
            ·
              refine ⟨3637294302752308618682369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38797805896024625265945269 3637294302752308618682369)
              ·
                refine ⟨2727970727064231464011777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3637294302752308618682369 2727970727064231464011777)
                ·
                  refine ⟨2045978045298173598008833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2727970727064231464011777 2045978045298173598008833)
                  ·
                    refine ⟨1534483533973630198506625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2045978045298173598008833 1534483533973630198506625)
                    ·
                      refine ⟨1150862650480222648879969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534483533973630198506625 1150862650480222648879969)
                      ·
                        rfl

theorem cell23_2241297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_2241297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241297 prefixEnd_2241297 := by exact prefixLift 2241297
  have htrace : WordTrace (prefixWord ++ tailWord_2241297) baseStart_2241297 baseEnd_2241297 := by
    simpa [prefixWord, tailWord_2241297, baseEnd_2241297] using wordTrace_append hprefix tailTrace_2241297
  have hstable : (prefixWord ++ tailWord_2241297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241297).length < 2 ^ (prefixWord ++ tailWord_2241297).sum := by decide
  have hdescent : baseEnd_2241297 < baseStart_2241297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241313 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2241313 : Nat := 118140960795 + 2241313 * 2 ^ 59
def prefixEnd_2241313 : Nat := 4983230072969 + 3 ^ 40 * 2241313 * 2
def baseEnd_2241313 : Nat := 1150870866170694586279895

theorem tailTrace_2241313 : CollatzResearch.WordTrace tailWord_2241313 prefixEnd_2241313 1150870866170694586279895 := by
  unfold tailWord_2241313
  simp only [CollatzResearch.WordTrace]
  refine ⟨81747400929113261630376593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54498267286075507753584395 81747400929113261630376593)
  ·
    refine ⟨61310550696834946222782445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81747400929113261630376593 61310550696834946222782445)
    ·
      refine ⟨22991456511313104833543417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61310550696834946222782445 22991456511313104833543417)
      ·
        refine ⟨17243592383484828625157563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22991456511313104833543417 17243592383484828625157563)
        ·
          refine ⟨25865388575227242937736345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17243592383484828625157563 25865388575227242937736345)
          ·
            refine ⟨19399041431420432203302259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25865388575227242937736345 19399041431420432203302259)
            ·
              refine ⟨29098562147130648304953389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19399041431420432203302259 29098562147130648304953389)
              ·
                refine ⟨10911960805173993114357521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29098562147130648304953389 10911960805173993114357521)
                ·
                  refine ⟨8183970603880494835768141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10911960805173993114357521 8183970603880494835768141)
                  ·
                    refine ⟨3068988976455185563413053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8183970603880494835768141 3068988976455185563413053)
                    ·
                      refine ⟨1150870866170694586279895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3068988976455185563413053 1150870866170694586279895)
                      ·
                        rfl

theorem cell23_2241313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2241313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241313 prefixEnd_2241313 := by exact prefixLift 2241313
  have htrace : WordTrace (prefixWord ++ tailWord_2241313) baseStart_2241313 baseEnd_2241313 := by
    simpa [prefixWord, tailWord_2241313, baseEnd_2241313] using wordTrace_append hprefix tailTrace_2241313
  have hstable : (prefixWord ++ tailWord_2241313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241313).length < 2 ^ (prefixWord ++ tailWord_2241313).sum := by decide
  have hdescent : baseEnd_2241313 < baseStart_2241313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241323 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 5, 2]
def baseStart_2241323 : Nat := 118140960795 + 2241323 * 2 ^ 59
def prefixEnd_2241323 : Nat := 4983230072969 + 3 ^ 40 * 2241323 * 2
def baseEnd_2241323 : Nat := 1150876000977239547154849

theorem tailTrace_2241323 : CollatzResearch.WordTrace tailWord_2241323 prefixEnd_2241323 1150876000977239547154849 := by
  unfold tailWord_2241323
  simp only [CollatzResearch.WordTrace]
  refine ⟨81747765659077033338240623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54498510439384688892160415 81747765659077033338240623)
  ·
    refine ⟨122621648488615550007360935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81747765659077033338240623 122621648488615550007360935)
    ·
      refine ⟨183932472732923325011041403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122621648488615550007360935 183932472732923325011041403)
      ·
        refine ⟨275898709099384987516562105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183932472732923325011041403 275898709099384987516562105)
        ·
          refine ⟨206924031824538740637421579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275898709099384987516562105 206924031824538740637421579)
          ·
            refine ⟨310386047736808110956132369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206924031824538740637421579 310386047736808110956132369)
            ·
              refine ⟨232789535802606083217099277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310386047736808110956132369 232789535802606083217099277)
              ·
                refine ⟨87296075925977281206412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232789535802606083217099277 87296075925977281206412229)
                ·
                  refine ⟨16368014236120740226202293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87296075925977281206412229 16368014236120740226202293)
                  ·
                    refine ⟨1534501334636319396206465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16368014236120740226202293 1534501334636319396206465)
                    ·
                      refine ⟨1150876000977239547154849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534501334636319396206465 1150876000977239547154849)
                      ·
                        rfl

theorem cell23_2241323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 5, 2].length) (baseStart_2241323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241323 prefixEnd_2241323 := by exact prefixLift 2241323
  have htrace : WordTrace (prefixWord ++ tailWord_2241323) baseStart_2241323 baseEnd_2241323 := by
    simpa [prefixWord, tailWord_2241323, baseEnd_2241323] using wordTrace_append hprefix tailTrace_2241323
  have hstable : (prefixWord ++ tailWord_2241323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241323).length < 2 ^ (prefixWord ++ tailWord_2241323).sum := by decide
  have hdescent : baseEnd_2241323 < baseStart_2241323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241333 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2241333 : Nat := 118140960795 + 2241333 * 2 ^ 59
def prefixEnd_2241333 : Nat := 4983230072969 + 3 ^ 40 * 2241333 * 2
def baseEnd_2241333 : Nat := 383627045261261502676601

theorem tailTrace_2241333 : CollatzResearch.WordTrace tailWord_2241333 prefixEnd_2241333 383627045261261502676601 := by
  unfold tailWord_2241333
  simp only [CollatzResearch.WordTrace]
  refine ⟨81748130389040805046104653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54498753592693870030736435 81748130389040805046104653)
  ·
    refine ⟨30655548895890301892289245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81748130389040805046104653 30655548895890301892289245)
    ·
      refine ⟨11495830835958863209608467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30655548895890301892289245 11495830835958863209608467)
      ·
        refine ⟨17243746253938294814412701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495830835958863209608467 17243746253938294814412701)
        ·
          refine ⟨6466404845226860555404763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17243746253938294814412701 6466404845226860555404763)
          ·
            refine ⟨9699607267840290833107145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466404845226860555404763 9699607267840290833107145)
            ·
              refine ⟨7274705450880218124830359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9699607267840290833107145 7274705450880218124830359)
              ·
                refine ⟨10912058176320327187245539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274705450880218124830359 10912058176320327187245539)
                ·
                  refine ⟨16368087264480490780868309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10912058176320327187245539 16368087264480490780868309)
                  ·
                    refine ⟨383627045261261502676601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16368087264480490780868309 383627045261261502676601)
                    ·
                      rfl

theorem cell23_2241333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2241333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241333 prefixEnd_2241333 := by exact prefixLift 2241333
  have htrace : WordTrace (prefixWord ++ tailWord_2241333) baseStart_2241333 baseEnd_2241333 := by
    simpa [prefixWord, tailWord_2241333, baseEnd_2241333] using wordTrace_append hprefix tailTrace_2241333
  have hstable : (prefixWord ++ tailWord_2241333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241333).length < 2 ^ (prefixWord ++ tailWord_2241333).sum := by decide
  have hdescent : baseEnd_2241333 < baseStart_2241333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241353 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_2241353 : Nat := 118140960795 + 2241353 * 2 ^ 59
def prefixEnd_2241353 : Nat := 4983230072969 + 3 ^ 40 * 2241353 * 2
def baseEnd_2241353 : Nat := 1150891405396874429779711

theorem tailTrace_2241353 : CollatzResearch.WordTrace tailWord_2241353 prefixEnd_2241353 1150891405396874429779711 := by
  unfold tailWord_2241353
  simp only [CollatzResearch.WordTrace]
  refine ⟨81748859848968348461832713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54499239899312232307888475 81748859848968348461832713)
  ·
    refine ⟨61311644886726261346374535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81748859848968348461832713 61311644886726261346374535)
    ·
      refine ⟨91967467330089392019561803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61311644886726261346374535 91967467330089392019561803)
      ·
        refine ⟨137951200995134088029342705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91967467330089392019561803 137951200995134088029342705)
        ·
          refine ⟨103463400746350566022007029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137951200995134088029342705 103463400746350566022007029)
          ·
            refine ⟨9699693819970365564563159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103463400746350566022007029 9699693819970365564563159)
            ·
              refine ⟨14549540729955548346844739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9699693819970365564563159 14549540729955548346844739)
              ·
                refine ⟨21824311094933322520267109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14549540729955548346844739 21824311094933322520267109)
                ·
                  refine ⟨4092058330299997972550083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21824311094933322520267109 4092058330299997972550083)
                  ·
                    refine ⟨6138087495449996958825125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4092058330299997972550083 6138087495449996958825125)
                    ·
                      refine ⟨1150891405396874429779711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6138087495449996958825125 1150891405396874429779711)
                      ·
                        rfl

theorem cell23_2241353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_2241353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241353 prefixEnd_2241353 := by exact prefixLift 2241353
  have htrace : WordTrace (prefixWord ++ tailWord_2241353) baseStart_2241353 baseEnd_2241353 := by
    simpa [prefixWord, tailWord_2241353, baseEnd_2241353] using wordTrace_append hprefix tailTrace_2241353
  have hstable : (prefixWord ++ tailWord_2241353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241353).length < 2 ^ (prefixWord ++ tailWord_2241353).sum := by decide
  have hdescent : baseEnd_2241353 < baseStart_2241353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241437 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2241437 : Nat := 118140960795 + 2241437 * 2 ^ 59
def prefixEnd_2241437 : Nat := 4983230072969 + 3 ^ 40 * 2241437 * 2
def baseEnd_2241437 : Nat := 1150934537771852101129325

theorem tailTrace_2241437 : CollatzResearch.WordTrace tailWord_2241437 prefixEnd_2241437 1150934537771852101129325 := by
  unfold tailWord_2241437
  simp only [CollatzResearch.WordTrace]
  refine ⟨81751923580664030807890565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54501282387109353871927043 81751923580664030807890565)
  ·
    refine ⟨15328485671374505776479481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81751923580664030807890565 15328485671374505776479481)
    ·
      refine ⟨11496364253530879332359611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15328485671374505776479481 11496364253530879332359611)
      ·
        refine ⟨17244546380296318998539417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11496364253530879332359611 17244546380296318998539417)
        ·
          refine ⟨12933409785222239248904563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17244546380296318998539417 12933409785222239248904563)
          ·
            refine ⟨19400114677833358873356845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12933409785222239248904563 19400114677833358873356845)
            ·
              refine ⟨7275043004187509577508817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19400114677833358873356845 7275043004187509577508817)
              ·
                refine ⟨5456282253140632183131613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7275043004187509577508817 5456282253140632183131613)
                ·
                  refine ⟨2046105844927737068674355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5456282253140632183131613 2046105844927737068674355)
                  ·
                    refine ⟨3069158767391605603011533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046105844927737068674355 3069158767391605603011533)
                    ·
                      refine ⟨1150934537771852101129325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069158767391605603011533 1150934537771852101129325)
                      ·
                        rfl

theorem cell23_2241437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2241437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241437 prefixEnd_2241437 := by exact prefixLift 2241437
  have htrace : WordTrace (prefixWord ++ tailWord_2241437) baseStart_2241437 baseEnd_2241437 := by
    simpa [prefixWord, tailWord_2241437, baseEnd_2241437] using wordTrace_append hprefix tailTrace_2241437
  have hstable : (prefixWord ++ tailWord_2241437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241437).length < 2 ^ (prefixWord ++ tailWord_2241437).sum := by decide
  have hdescent : baseEnd_2241437 < baseStart_2241437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241457 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_2241457 : Nat := 118140960795 + 2241457 * 2 ^ 59
def prefixEnd_2241457 : Nat := 4983230072969 + 3 ^ 40 * 2241457 * 2
def baseEnd_2241457 : Nat := 383648269128314007626411

theorem tailTrace_2241457 : CollatzResearch.WordTrace tailWord_2241457 prefixEnd_2241457 383648269128314007626411 := by
  unfold tailWord_2241457
  simp only [CollatzResearch.WordTrace]
  refine ⟨81752653040591574223618625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54501768693727716149079083 81752653040591574223618625)
  ·
    refine ⟨61314489780443680667713969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81752653040591574223618625 61314489780443680667713969)
    ·
      refine ⟨45985867335332760500785477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61314489780443680667713969 45985867335332760500785477)
      ·
        refine ⟨8622350125374892593897277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45985867335332760500785477 8622350125374892593897277)
        ·
          refine ⟨3233381297015584722711479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8622350125374892593897277 3233381297015584722711479)
          ·
            refine ⟨4850071945523377084067219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233381297015584722711479 4850071945523377084067219)
            ·
              refine ⟨7275107918285065626100829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850071945523377084067219 7275107918285065626100829)
              ·
                refine ⟨2728165469356899609787811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7275107918285065626100829 2728165469356899609787811)
                ·
                  refine ⟨4092248204035349414681717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728165469356899609787811 4092248204035349414681717)
                  ·
                    refine ⟨383648269128314007626411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4092248204035349414681717 383648269128314007626411)
                    ·
                      rfl

theorem cell23_2241457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_2241457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241457 prefixEnd_2241457 := by exact prefixLift 2241457
  have htrace : WordTrace (prefixWord ++ tailWord_2241457) baseStart_2241457 baseEnd_2241457 := by
    simpa [prefixWord, tailWord_2241457, baseEnd_2241457] using wordTrace_append hprefix tailTrace_2241457
  have hstable : (prefixWord ++ tailWord_2241457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241457).length < 2 ^ (prefixWord ++ tailWord_2241457).sum := by decide
  have hdescent : baseEnd_2241457 < baseStart_2241457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241494 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2241494 : Nat := 118140960795 + 2241494 * 2 ^ 59
def prefixEnd_2241494 : Nat := 4983230072969 + 3 ^ 40 * 2241494 * 2
def baseEnd_2241494 : Nat := 1150963806169158378116563

theorem tailTrace_2241494 : CollatzResearch.WordTrace tailWord_2241494 prefixEnd_2241494 1150963806169158378116563 := by
  unfold tailWord_2241494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109625158841095596419721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54502668360971686361810357 5109625158841095596419721)
  ·
    refine ⟨3832218869130821697314791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5109625158841095596419721 3832218869130821697314791)
    ·
      refine ⟨5748328303696232545972187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832218869130821697314791 5748328303696232545972187)
      ·
        refine ⟨8622492455544348818958281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5748328303696232545972187 8622492455544348818958281)
        ·
          refine ⟨6466869341658261614218711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8622492455544348818958281 6466869341658261614218711)
          ·
            refine ⟨9700304012487392421328067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466869341658261614218711 9700304012487392421328067)
            ·
              refine ⟨14550456018731088631992101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700304012487392421328067 14550456018731088631992101)
              ·
                refine ⟨2728210503512079118498519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14550456018731088631992101 2728210503512079118498519)
                ·
                  refine ⟨4092315755268118677747779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728210503512079118498519 4092315755268118677747779)
                  ·
                    refine ⟨6138473632902178016621669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4092315755268118677747779 6138473632902178016621669)
                    ·
                      refine ⟨1150963806169158378116563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6138473632902178016621669 1150963806169158378116563)
                      ·
                        rfl

theorem cell23_2241494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2241494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241494 prefixEnd_2241494 := by exact prefixLift 2241494
  have htrace : WordTrace (prefixWord ++ tailWord_2241494) baseStart_2241494 baseEnd_2241494 := by
    simpa [prefixWord, tailWord_2241494, baseEnd_2241494] using wordTrace_append hprefix tailTrace_2241494
  have hstable : (prefixWord ++ tailWord_2241494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241494).length < 2 ^ (prefixWord ++ tailWord_2241494).sum := by decide
  have hdescent : baseEnd_2241494 < baseStart_2241494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241497 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_2241497 : Nat := 118140960795 + 2241497 * 2 ^ 59
def prefixEnd_2241497 : Nat := 4983230072969 + 3 ^ 40 * 2241497 * 2
def baseEnd_2241497 : Nat := 1150965346611121866379049

theorem tailTrace_2241497 : CollatzResearch.WordTrace tailWord_2241497 prefixEnd_2241497 1150965346611121866379049 := by
  unfold tailWord_2241497
  simp only [CollatzResearch.WordTrace]
  refine ⟨81754111960446661055074745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54502741306964440703383163 81754111960446661055074745)
  ·
    refine ⟨61315583970334995791306059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81754111960446661055074745 61315583970334995791306059)
    ·
      refine ⟨91973375955502493686959089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61315583970334995791306059 91973375955502493686959089)
      ·
        refine ⟨68980031966626870265219317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91973375955502493686959089 68980031966626870265219317)
        ·
          refine ⟨6466877996871269087364311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68980031966626870265219317 6466877996871269087364311)
          ·
            refine ⟨9700316995306903631046467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466877996871269087364311 9700316995306903631046467)
            ·
              refine ⟨14550475492960355446569701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700316995306903631046467 14550475492960355446569701)
              ·
                refine ⟨2728214154930066646231819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14550475492960355446569701 2728214154930066646231819)
                ·
                  refine ⟨4092321232395099969347729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728214154930066646231819 4092321232395099969347729)
                  ·
                    refine ⟨3069240924296324977010797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4092321232395099969347729 3069240924296324977010797)
                    ·
                      refine ⟨1150965346611121866379049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069240924296324977010797 1150965346611121866379049)
                      ·
                        rfl

theorem cell23_2241497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_2241497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241497 prefixEnd_2241497 := by exact prefixLift 2241497
  have htrace : WordTrace (prefixWord ++ tailWord_2241497) baseStart_2241497 baseEnd_2241497 := by
    simpa [prefixWord, tailWord_2241497, baseEnd_2241497] using wordTrace_append hprefix tailTrace_2241497
  have hstable : (prefixWord ++ tailWord_2241497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241497).length < 2 ^ (prefixWord ++ tailWord_2241497).sum := by decide
  have hdescent : baseEnd_2241497 < baseStart_2241497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241544 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2241544 : Nat := 118140960795 + 2241544 * 2 ^ 59
def prefixEnd_2241544 : Nat := 4983230072969 + 3 ^ 40 * 2241544 * 2
def baseEnd_2241544 : Nat := 1150989480201883182491333

theorem tailTrace_2241544 : CollatzResearch.WordTrace tailWord_2241544 prefixEnd_2241544 1150989480201883182491333 := by
  unfold tailWord_2241544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40877913095638194041017843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54503884127517592054690457 40877913095638194041017843)
  ·
    refine ⟨61316869643457291061526765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40877913095638194041017843 61316869643457291061526765)
    ·
      refine ⟨22993826116296484148072537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61316869643457291061526765 22993826116296484148072537)
      ·
        refine ⟨17245369587222363111054403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22993826116296484148072537 17245369587222363111054403)
        ·
          refine ⟨25868054380833544666581605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17245369587222363111054403 25868054380833544666581605)
          ·
            refine ⟨4850260196406289624984051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25868054380833544666581605 4850260196406289624984051)
            ·
              refine ⟨7275390294609434437476077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850260196406289624984051 7275390294609434437476077)
              ·
                refine ⟨2728271360478537914053529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7275390294609434437476077 2728271360478537914053529)
                ·
                  refine ⟨2046203520358903435540147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728271360478537914053529 2046203520358903435540147)
                  ·
                    refine ⟨3069305280538355153310221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046203520358903435540147 3069305280538355153310221)
                    ·
                      refine ⟨1150989480201883182491333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069305280538355153310221 1150989480201883182491333)
                      ·
                        rfl

theorem cell23_2241544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2241544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241544 prefixEnd_2241544 := by exact prefixLift 2241544
  have htrace : WordTrace (prefixWord ++ tailWord_2241544) baseStart_2241544 baseEnd_2241544 := by
    simpa [prefixWord, tailWord_2241544, baseEnd_2241544] using wordTrace_append hprefix tailTrace_2241544
  have hstable : (prefixWord ++ tailWord_2241544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241544).length < 2 ^ (prefixWord ++ tailWord_2241544).sum := by decide
  have hdescent : baseEnd_2241544 < baseStart_2241544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241563 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6]
def baseStart_2241563 : Nat := 118140960795 + 2241563 * 2 ^ 59
def prefixEnd_2241563 : Nat := 4983230072969 + 3 ^ 40 * 2241563 * 2
def baseEnd_2241563 : Nat := 1150999236334318608153745

theorem tailTrace_2241563 : CollatzResearch.WordTrace tailWord_2241563 prefixEnd_2241563 1150999236334318608153745 := by
  unfold tailWord_2241563
  simp only [CollatzResearch.WordTrace]
  refine ⟨81756519178207554326977343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54504346118805036217984895 81756519178207554326977343)
  ·
    refine ⟨122634778767311331490466015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81756519178207554326977343 122634778767311331490466015)
    ·
      refine ⟨183952168150966997235699023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122634778767311331490466015 183952168150966997235699023)
      ·
        refine ⟨275928252226450495853548535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183952168150966997235699023 275928252226450495853548535)
        ·
          refine ⟨413892378339675743780322803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275928252226450495853548535 413892378339675743780322803)
          ·
            refine ⟨620838567509513615670484205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413892378339675743780322803 620838567509513615670484205)
            ·
              refine ⟨232814462816067605876431577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620838567509513615670484205 232814462816067605876431577)
              ·
                refine ⟨174610847112050704407323683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232814462816067605876431577 174610847112050704407323683)
                ·
                  refine ⟨261916270668076056610985525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174610847112050704407323683 261916270668076056610985525)
                  ·
                    refine ⟨24554650375132130307279893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 261916270668076056610985525 24554650375132130307279893)
                    ·
                      refine ⟨1150999236334318608153745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24554650375132130307279893 1150999236334318608153745)
                      ·
                        rfl

theorem cell23_2241563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 6].length) (baseStart_2241563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241563 prefixEnd_2241563 := by exact prefixLift 2241563
  have htrace : WordTrace (prefixWord ++ tailWord_2241563) baseStart_2241563 baseEnd_2241563 := by
    simpa [prefixWord, tailWord_2241563, baseEnd_2241563] using wordTrace_append hprefix tailTrace_2241563
  have hstable : (prefixWord ++ tailWord_2241563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241563).length < 2 ^ (prefixWord ++ tailWord_2241563).sum := by decide
  have hdescent : baseEnd_2241563 < baseStart_2241563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241567 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 4, 2]
def baseStart_2241567 : Nat := 118140960795 + 2241567 * 2 ^ 59
def prefixEnd_2241567 : Nat := 4983230072969 + 3 ^ 40 * 2241567 * 2
def baseEnd_2241567 : Nat := 1151001290256936592503727

theorem tailTrace_2241567 : CollatzResearch.WordTrace tailWord_2241567 prefixEnd_2241567 1151001290256936592503727 := by
  unfold tailWord_2241567
  simp only [CollatzResearch.WordTrace]
  refine ⟨81756665070193063010122955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54504443380128708673415303 81756665070193063010122955)
  ·
    refine ⟨122634997605289594515184433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81756665070193063010122955 122634997605289594515184433)
    ·
      refine ⟨91976248203967195886388325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122634997605289594515184433 91976248203967195886388325)
      ·
        refine ⟨17245546538243849228697811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91976248203967195886388325 17245546538243849228697811)
        ·
          refine ⟨25868319807365773843046717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17245546538243849228697811 25868319807365773843046717)
          ·
            refine ⟨9700619927762165191142519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25868319807365773843046717 9700619927762165191142519)
            ·
              refine ⟨14550929891643247786713779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700619927762165191142519 14550929891643247786713779)
              ·
                refine ⟨21826394837464871680070669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14550929891643247786713779 21826394837464871680070669)
                ·
                  refine ⟨8184898064049326880026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21826394837464871680070669 8184898064049326880026501)
                  ·
                    refine ⟨1534668387009248790004969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8184898064049326880026501 1534668387009248790004969)
                    ·
                      refine ⟨1151001290256936592503727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534668387009248790004969 1151001290256936592503727)
                      ·
                        rfl

theorem cell23_2241567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_2241567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241567 prefixEnd_2241567 := by exact prefixLift 2241567
  have htrace : WordTrace (prefixWord ++ tailWord_2241567) baseStart_2241567 baseEnd_2241567 := by
    simpa [prefixWord, tailWord_2241567, baseEnd_2241567] using wordTrace_append hprefix tailTrace_2241567
  have hstable : (prefixWord ++ tailWord_2241567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241567).length < 2 ^ (prefixWord ++ tailWord_2241567).sum := by decide
  have hdescent : baseEnd_2241567 < baseStart_2241567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241571 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 1, 3, 2]
def baseStart_2241571 : Nat := 118140960795 + 2241571 * 2 ^ 59
def prefixEnd_2241571 : Nat := 4983230072969 + 3 ^ 40 * 2241571 * 2
def baseEnd_2241571 : Nat := 1151003344179554576853709

theorem tailTrace_2241571 : CollatzResearch.WordTrace tailWord_2241571 prefixEnd_2241571 1151003344179554576853709 := by
  unfold tailWord_2241571
  simp only [CollatzResearch.WordTrace]
  refine ⟨81756810962178571693268567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54504540641452381128845711 81756810962178571693268567)
  ·
    refine ⟨122635216443267857539902851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81756810962178571693268567 122635216443267857539902851)
    ·
      refine ⟨183952824664901786309854277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122635216443267857539902851 183952824664901786309854277)
      ·
        refine ⟨34491154624669084933097677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183952824664901786309854277 34491154624669084933097677)
        ·
          refine ⟨12934182984250906849911629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34491154624669084933097677 12934182984250906849911629)
          ·
            refine ⟨4850318619094090068716861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12934182984250906849911629 4850318619094090068716861)
            ·
              refine ⟨1818869482160283775768823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4850318619094090068716861 1818869482160283775768823)
              ·
                refine ⟨2728304223240425663653235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818869482160283775768823 2728304223240425663653235)
                ·
                  refine ⟨4092456334860638495479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728304223240425663653235 4092456334860638495479853)
                  ·
                    refine ⟨1534671125572739435804945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4092456334860638495479853 1534671125572739435804945)
                    ·
                      refine ⟨1151003344179554576853709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534671125572739435804945 1151003344179554576853709)
                      ·
                        rfl

theorem cell23_2241571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_2241571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241571 prefixEnd_2241571 := by exact prefixLift 2241571
  have htrace : WordTrace (prefixWord ++ tailWord_2241571) baseStart_2241571 baseEnd_2241571 := by
    simpa [prefixWord, tailWord_2241571, baseEnd_2241571] using wordTrace_append hprefix tailTrace_2241571
  have hstable : (prefixWord ++ tailWord_2241571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241571).length < 2 ^ (prefixWord ++ tailWord_2241571).sum := by decide
  have hdescent : baseEnd_2241571 < baseStart_2241571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241580 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2241580 : Nat := 118140960795 + 2241580 * 2 ^ 59
def prefixEnd_2241580 : Nat := 4983230072969 + 3 ^ 40 * 2241580 * 2
def baseEnd_2241580 : Nat := 1151007965505445041641167

theorem tailTrace_2241580 : CollatzResearch.WordTrace tailWord_2241580 prefixEnd_2241580 1151007965505445041641167 := by
  unfold tailWord_2241580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40878569609572983115173097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54504759479430644153564129 40878569609572983115173097)
  ·
    refine ⟨30658927207179737336379823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40878569609572983115173097 30658927207179737336379823)
    ·
      refine ⟨45988390810769606004569735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30658927207179737336379823 45988390810769606004569735)
      ·
        refine ⟨68982586216154409006854603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45988390810769606004569735 68982586216154409006854603)
        ·
          refine ⟨103473879324231613510281905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68982586216154409006854603 103473879324231613510281905)
          ·
            refine ⟨77605409493173710132711429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103473879324231613510281905 77605409493173710132711429)
            ·
              refine ⟨14551014279970070649883393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77605409493173710132711429 14551014279970070649883393)
              ·
                refine ⟨10913260709977552987412545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14551014279970070649883393 10913260709977552987412545)
                ·
                  refine ⟨8184945532483164740559409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10913260709977552987412545 8184945532483164740559409)
                  ·
                    refine ⟨6138709149362373555419557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8184945532483164740559409 6138709149362373555419557)
                    ·
                      refine ⟨1151007965505445041641167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6138709149362373555419557 1151007965505445041641167)
                      ·
                        rfl

theorem cell23_2241580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2241580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241580 prefixEnd_2241580 := by exact prefixLift 2241580
  have htrace : WordTrace (prefixWord ++ tailWord_2241580) baseStart_2241580 baseEnd_2241580 := by
    simpa [prefixWord, tailWord_2241580, baseEnd_2241580] using wordTrace_append hprefix tailTrace_2241580
  have hstable : (prefixWord ++ tailWord_2241580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241580).length < 2 ^ (prefixWord ++ tailWord_2241580).sum := by decide
  have hdescent : baseEnd_2241580 < baseStart_2241580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241597 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2241597 : Nat := 118140960795 + 2241597 * 2 ^ 59
def prefixEnd_2241597 : Nat := 4983230072969 + 3 ^ 40 * 2241597 * 2
def baseEnd_2241597 : Nat := 1151016694676571475128589

theorem tailTrace_2241597 : CollatzResearch.WordTrace tailWord_2241597 prefixEnd_2241597 1151016694676571475128589 := by
  unfold tailWord_2241597
  simp only [CollatzResearch.WordTrace]
  refine ⟨81757759260084378133715045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54505172840056252089143363 81757759260084378133715045)
  ·
    refine ⟨15329579861265820900071571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81757759260084378133715045 15329579861265820900071571)
    ·
      refine ⟨22994369791898731350107357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15329579861265820900071571 22994369791898731350107357)
      ·
        refine ⟨8622888671962024256290259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22994369791898731350107357 8622888671962024256290259)
        ·
          refine ⟨12934333007943036384435389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8622888671962024256290259 12934333007943036384435389)
          ·
            refine ⟨4850374877978638644163271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12934333007943036384435389 4850374877978638644163271)
            ·
              refine ⟨7275562316967957966244907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850374877978638644163271 7275562316967957966244907)
              ·
                refine ⟨10913343475451936949367361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7275562316967957966244907 10913343475451936949367361)
                ·
                  refine ⟨8185007606588952712025521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10913343475451936949367361 8185007606588952712025521)
                  ·
                    refine ⟨6138755704941714534019141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8185007606588952712025521 6138755704941714534019141)
                    ·
                      refine ⟨1151016694676571475128589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6138755704941714534019141 1151016694676571475128589)
                      ·
                        rfl

theorem cell23_2241597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2241597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241597 prefixEnd_2241597 := by exact prefixLift 2241597
  have htrace : WordTrace (prefixWord ++ tailWord_2241597) baseStart_2241597 baseEnd_2241597 := by
    simpa [prefixWord, tailWord_2241597, baseEnd_2241597] using wordTrace_append hprefix tailTrace_2241597
  have hstable : (prefixWord ++ tailWord_2241597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241597).length < 2 ^ (prefixWord ++ tailWord_2241597).sum := by decide
  have hdescent : baseEnd_2241597 < baseStart_2241597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241601 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2241601 : Nat := 118140960795 + 2241601 * 2 ^ 59
def prefixEnd_2241601 : Nat := 4983230072969 + 3 ^ 40 * 2241601 * 2
def baseEnd_2241601 : Nat := 1151018748599189459478571

theorem tailTrace_2241601 : CollatzResearch.WordTrace tailWord_2241601 prefixEnd_2241601 1151018748599189459478571 := by
  unfold tailWord_2241601
  simp only [CollatzResearch.WordTrace]
  refine ⟨81757905152069886816860657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54505270101379924544573771 81757905152069886816860657)
  ·
    refine ⟨61318428864052415112645493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81757905152069886816860657 61318428864052415112645493)
    ·
      refine ⟨5748602706004913916810515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61318428864052415112645493 5748602706004913916810515)
      ·
        refine ⟨8622904059007370875215773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5748602706004913916810515 8622904059007370875215773)
        ·
          refine ⟨3233589022127764078205915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8622904059007370875215773 3233589022127764078205915)
          ·
            refine ⟨4850383533191646117308873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233589022127764078205915 4850383533191646117308873)
            ·
              refine ⟨3637787649893734587981655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4850383533191646117308873 3637787649893734587981655)
              ·
                refine ⟨5456681474840601881972483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637787649893734587981655 5456681474840601881972483)
                ·
                  refine ⟨8185022212260902822958725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5456681474840601881972483 8185022212260902822958725)
                  ·
                    refine ⟨1534691664798919279304761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8185022212260902822958725 1534691664798919279304761)
                    ·
                      refine ⟨1151018748599189459478571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534691664798919279304761 1151018748599189459478571)
                      ·
                        rfl

theorem cell23_2241601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2241601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241601 prefixEnd_2241601 := by exact prefixLift 2241601
  have htrace : WordTrace (prefixWord ++ tailWord_2241601) baseStart_2241601 baseEnd_2241601 := by
    simpa [prefixWord, tailWord_2241601, baseEnd_2241601] using wordTrace_append hprefix tailTrace_2241601
  have hstable : (prefixWord ++ tailWord_2241601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241601).length < 2 ^ (prefixWord ++ tailWord_2241601).sum := by decide
  have hdescent : baseEnd_2241601 < baseStart_2241601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241622 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2241622 : Nat := 118140960795 + 2241622 * 2 ^ 59
def prefixEnd_2241622 : Nat := 4983230072969 + 3 ^ 40 * 2241622 * 2
def baseEnd_2241622 : Nat := 1151029531692933877315975

theorem tailTrace_2241622 : CollatzResearch.WordTrace tailWord_2241622 prefixEnd_2241622 1151029531692933877315975 := by
  unfold tailWord_2241622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109916942812112962710945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54505780723329204935583413 5109916942812112962710945)
  ·
    refine ⟨3832437707109084722033209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5109916942812112962710945 3832437707109084722033209)
    ·
      refine ⟨2874328280331813541524907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3832437707109084722033209 2874328280331813541524907)
      ·
        refine ⟨4311492420497720312287361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874328280331813541524907 4311492420497720312287361)
        ·
          refine ⟨3233619315373290234215521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4311492420497720312287361 3233619315373290234215521)
          ·
            refine ⟨2425214486529967675661641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3233619315373290234215521 2425214486529967675661641)
            ·
              refine ⟨1818910864897475756746231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425214486529967675661641 1818910864897475756746231)
              ·
                refine ⟨2728366297346213635119347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818910864897475756746231 2728366297346213635119347)
                ·
                  refine ⟨4092549446019320452679021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728366297346213635119347 4092549446019320452679021)
                  ·
                    refine ⟨1534706042257245169754633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4092549446019320452679021 1534706042257245169754633)
                    ·
                      refine ⟨1151029531692933877315975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534706042257245169754633 1151029531692933877315975)
                      ·
                        rfl

theorem cell23_2241622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2241622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241622 prefixEnd_2241622 := by exact prefixLift 2241622
  have htrace : WordTrace (prefixWord ++ tailWord_2241622) baseStart_2241622 baseEnd_2241622 := by
    simpa [prefixWord, tailWord_2241622, baseEnd_2241622] using wordTrace_append hprefix tailTrace_2241622
  have hstable : (prefixWord ++ tailWord_2241622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241622).length < 2 ^ (prefixWord ++ tailWord_2241622).sum := by decide
  have hdescent : baseEnd_2241622 < baseStart_2241622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241634 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2241634 : Nat := 118140960795 + 2241634 * 2 ^ 59
def prefixEnd_2241634 : Nat := 4983230072969 + 3 ^ 40 * 2241634 * 2
def baseEnd_2241634 : Nat := 1151035693460787830365919

theorem tailTrace_2241634 : CollatzResearch.WordTrace tailWord_2241634 prefixEnd_2241634 1151035693460787830365919 := by
  unfold tailWord_2241634
  simp only [CollatzResearch.WordTrace]
  refine ⟨20439777190237583363202989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54506072507300222301874637 20439777190237583363202989)
  ·
    refine ⟨7664916446339093761201121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20439777190237583363202989 7664916446339093761201121)
    ·
      refine ⟨5748687334754320320900841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7664916446339093761201121 5748687334754320320900841)
      ·
        refine ⟨4311515501065740240675631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5748687334754320320900841 4311515501065740240675631)
        ·
          refine ⟨6467273251598610361013447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311515501065740240675631 6467273251598610361013447)
          ·
            refine ⟨9700909877397915541520171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467273251598610361013447 9700909877397915541520171)
            ·
              refine ⟨14551364816096873312280257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700909877397915541520171 14551364816096873312280257)
              ·
                refine ⟨10913523612072654984210193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14551364816096873312280257 10913523612072654984210193)
                ·
                  refine ⟨8185142709054491238157645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10913523612072654984210193 8185142709054491238157645)
                  ·
                    refine ⟨3069428515895434214309117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8185142709054491238157645 3069428515895434214309117)
                    ·
                      refine ⟨1151035693460787830365919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069428515895434214309117 1151035693460787830365919)
                      ·
                        rfl

theorem cell23_2241634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2241634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241634 prefixEnd_2241634 := by exact prefixLift 2241634
  have htrace : WordTrace (prefixWord ++ tailWord_2241634) baseStart_2241634 baseEnd_2241634 := by
    simpa [prefixWord, tailWord_2241634, baseEnd_2241634] using wordTrace_append hprefix tailTrace_2241634
  have hstable : (prefixWord ++ tailWord_2241634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241634).length < 2 ^ (prefixWord ++ tailWord_2241634).sum := by decide
  have hdescent : baseEnd_2241634 < baseStart_2241634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241667 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 3, 4]
def baseStart_2241667 : Nat := 118140960795 + 2241667 * 2 ^ 59
def prefixEnd_2241667 : Nat := 4983230072969 + 3 ^ 40 * 2241667 * 2
def baseEnd_2241667 : Nat := 383684212774128733751089

theorem tailTrace_2241667 : CollatzResearch.WordTrace tailWord_2241667 prefixEnd_2241667 383684212774128733751089 := by
  unfold tailWord_2241667
  simp only [CollatzResearch.WordTrace]
  refine ⟨81760312369830780088763255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54506874913220520059175503 81760312369830780088763255)
  ·
    refine ⟨122640468554746170133144883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81760312369830780088763255 122640468554746170133144883)
    ·
      refine ⟨183960702832119255199717325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122640468554746170133144883 183960702832119255199717325)
      ·
        refine ⟨68985263562044720699893997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183960702832119255199717325 68985263562044720699893997)
        ·
          refine ⟨25869473835766770262460249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68985263562044720699893997 25869473835766770262460249)
          ·
            refine ⟨19402105376825077696845187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25869473835766770262460249 19402105376825077696845187)
            ·
              refine ⟨29103158065237616545267781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19402105376825077696845187 29103158065237616545267781)
              ·
                refine ⟨5456842137232053102237709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29103158065237616545267781 5456842137232053102237709)
                ·
                  refine ⟨2046315801462019913339141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5456842137232053102237709 2046315801462019913339141)
                  ·
                    refine ⟨383684212774128733751089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046315801462019913339141 383684212774128733751089)
                    ·
                      rfl

theorem cell23_2241667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 4].length) (baseStart_2241667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241667 prefixEnd_2241667 := by exact prefixLift 2241667
  have htrace : WordTrace (prefixWord ++ tailWord_2241667) baseStart_2241667 baseEnd_2241667 := by
    simpa [prefixWord, tailWord_2241667, baseEnd_2241667] using wordTrace_append hprefix tailTrace_2241667
  have hstable : (prefixWord ++ tailWord_2241667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241667).length < 2 ^ (prefixWord ++ tailWord_2241667).sum := by decide
  have hdescent : baseEnd_2241667 < baseStart_2241667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241697 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 6]
def baseStart_2241697 : Nat := 118140960795 + 2241697 * 2 ^ 59
def prefixEnd_2241697 : Nat := 4983230072969 + 3 ^ 40 * 2241697 * 2
def baseEnd_2241697 : Nat := 127896449193557898208681

theorem tailTrace_2241697 : CollatzResearch.WordTrace tailWord_2241697 prefixEnd_2241697 127896449193557898208681 := by
  unfold tailWord_2241697
  simp only [CollatzResearch.WordTrace]
  refine ⟨81761406559722095212355345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54507604373148063474903563 81761406559722095212355345)
  ·
    refine ⟨61321054919791571409266509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81761406559722095212355345 61321054919791571409266509)
    ·
      refine ⟨22995395594921839278474941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61321054919791571409266509 22995395594921839278474941)
      ·
        refine ⟨8623273348095689729428103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22995395594921839278474941 8623273348095689729428103)
        ·
          refine ⟨12934910022143534594142155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8623273348095689729428103 12934910022143534594142155)
          ·
            refine ⟨19402365033215301891213233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12934910022143534594142155 19402365033215301891213233)
            ·
              refine ⟨14551773774911476418409925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19402365033215301891213233 14551773774911476418409925)
              ·
                refine ⟨2728457582795901828451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14551773774911476418409925 2728457582795901828451861)
                ·
                  refine ⟨127896449193557898208681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2728457582795901828451861 127896449193557898208681)
                  ·
                    rfl

theorem cell23_2241697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_2241697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241697 prefixEnd_2241697 := by exact prefixLift 2241697
  have htrace : WordTrace (prefixWord ++ tailWord_2241697) baseStart_2241697 baseEnd_2241697 := by
    simpa [prefixWord, tailWord_2241697, baseEnd_2241697] using wordTrace_append hprefix tailTrace_2241697
  have hstable : (prefixWord ++ tailWord_2241697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241697).length < 2 ^ (prefixWord ++ tailWord_2241697).sum := by decide
  have hdescent : baseEnd_2241697 < baseStart_2241697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241714 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_2241714 : Nat := 118140960795 + 2241714 * 2 ^ 59
def prefixEnd_2241714 : Nat := 4983230072969 + 3 ^ 40 * 2241714 * 2
def baseEnd_2241714 : Nat := 127897419101460835262839

theorem tailTrace_2241714 : CollatzResearch.WordTrace tailWord_2241714 prefixEnd_2241714 127897419101460835262839 := by
  unfold tailWord_2241714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20440506650165126778931049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54508017733773671410482797 20440506650165126778931049)
  ·
    refine ⟨15330379987623845084198287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20440506650165126778931049 15330379987623845084198287)
    ·
      refine ⟨22995569981435767626297431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15330379987623845084198287 22995569981435767626297431)
      ·
        refine ⟨34493354972153651439446147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22995569981435767626297431 34493354972153651439446147)
        ·
          refine ⟨51740032458230477159169221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34493354972153651439446147 51740032458230477159169221)
          ·
            refine ⟨9701256085918214467344229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51740032458230477159169221 9701256085918214467344229)
            ·
              refine ⟨1818985516109665212627043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9701256085918214467344229 1818985516109665212627043)
              ·
                refine ⟨2728478274164497818940565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818985516109665212627043 2728478274164497818940565)
                ·
                  refine ⟨127897419101460835262839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2728478274164497818940565 127897419101460835262839)
                  ·
                    rfl

theorem cell23_2241714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_2241714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241714 prefixEnd_2241714 := by exact prefixLift 2241714
  have htrace : WordTrace (prefixWord ++ tailWord_2241714) baseStart_2241714 baseEnd_2241714 := by
    simpa [prefixWord, tailWord_2241714, baseEnd_2241714] using wordTrace_append hprefix tailTrace_2241714
  have hstable : (prefixWord ++ tailWord_2241714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241714).length < 2 ^ (prefixWord ++ tailWord_2241714).sum := by decide
  have hdescent : baseEnd_2241714 < baseStart_2241714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241720 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_2241720 : Nat := 118140960795 + 2241720 * 2 ^ 59
def prefixEnd_2241720 : Nat := 4983230072969 + 3 ^ 40 * 2241720 * 2
def baseEnd_2241720 : Nat := 1151079852797074493890523

theorem tailTrace_2241720 : CollatzResearch.WordTrace tailWord_2241720 prefixEnd_2241720 1151079852797074493890523 := by
  unfold tailWord_2241720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40881122719319385070221307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54508163625759180093628409 40881122719319385070221307)
  ·
    refine ⟨61321684078979077605331961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40881122719319385070221307 61321684078979077605331961)
    ·
      refine ⟨45991263059234308203998971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61321684078979077605331961 45991263059234308203998971)
      ·
        refine ⟨68986894588851462305998457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45991263059234308203998971 68986894588851462305998457)
        ·
          refine ⟨51740170941638596729498843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68986894588851462305998457 51740170941638596729498843)
          ·
            refine ⟨77610256412457895094248265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51740170941638596729498843 77610256412457895094248265)
            ·
              refine ⟨58207692309343421320686199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77610256412457895094248265 58207692309343421320686199)
              ·
                refine ⟨87311538464015131981029299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58207692309343421320686199 87311538464015131981029299)
                ·
                  refine ⟨130967307696022697971543949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87311538464015131981029299 130967307696022697971543949)
                  ·
                    refine ⟨49112740386008511739328981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130967307696022697971543949 49112740386008511739328981)
                    ·
                      refine ⟨1151079852797074493890523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49112740386008511739328981 1151079852797074493890523)
                      ·
                        rfl

theorem cell23_2241720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_2241720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241720 prefixEnd_2241720 := by exact prefixLift 2241720
  have htrace : WordTrace (prefixWord ++ tailWord_2241720) baseStart_2241720 baseEnd_2241720 := by
    simpa [prefixWord, tailWord_2241720, baseEnd_2241720] using wordTrace_append hprefix tailTrace_2241720
  have hstable : (prefixWord ++ tailWord_2241720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241720).length < 2 ^ (prefixWord ++ tailWord_2241720).sum := by decide
  have hdescent : baseEnd_2241720 < baseStart_2241720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241844 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2241844 : Nat := 118140960795 + 2241844 * 2 ^ 59
def prefixEnd_2241844 : Nat := 4983230072969 + 3 ^ 40 * 2241844 * 2
def baseEnd_2241844 : Nat := 1151143524398232008739953

theorem tailTrace_2241844 : CollatzResearch.WordTrace tailWord_2241844 prefixEnd_2241844 1151143524398232008739953 := by
  unfold tailWord_2241844
  simp only [CollatzResearch.WordTrace]
  refine ⟨40883384045094769658978293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54511178726793026211971057 40883384045094769658978293)
  ·
    refine ⟨3832817254227634655529215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40883384045094769658978293 3832817254227634655529215)
    ·
      refine ⟨5749225881341451983293823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832817254227634655529215 5749225881341451983293823)
      ·
        refine ⟨8623838822012177974940735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749225881341451983293823 8623838822012177974940735)
        ·
          refine ⟨12935758233018266962411103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8623838822012177974940735 12935758233018266962411103)
          ·
            refine ⟨19403637349527400443616655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12935758233018266962411103 19403637349527400443616655)
            ·
              refine ⟨29105456024291100665424983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19403637349527400443616655 29105456024291100665424983)
              ·
                refine ⟨43658184036436650998137475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29105456024291100665424983 43658184036436650998137475)
                ·
                  refine ⟨65487276054654976497206213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43658184036436650998137475 65487276054654976497206213)
                  ·
                    refine ⟨12278864260247808093226165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65487276054654976497206213 12278864260247808093226165)
                    ·
                      refine ⟨1151143524398232008739953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12278864260247808093226165 1151143524398232008739953)
                      ·
                        rfl

theorem cell23_2241844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2241844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241844 prefixEnd_2241844 := by exact prefixLift 2241844
  have htrace : WordTrace (prefixWord ++ tailWord_2241844) baseStart_2241844 baseEnd_2241844 := by
    simpa [prefixWord, tailWord_2241844, baseEnd_2241844] using wordTrace_append hprefix tailTrace_2241844
  have hstable : (prefixWord ++ tailWord_2241844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241844).length < 2 ^ (prefixWord ++ tailWord_2241844).sum := by decide
  have hdescent : baseEnd_2241844 < baseStart_2241844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241849 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2241849 : Nat := 118140960795 + 2241849 * 2 ^ 59
def prefixEnd_2241849 : Nat := 4983230072969 + 3 ^ 40 * 2241849 * 2
def baseEnd_2241849 : Nat := 1151146091801504489177431

theorem tailTrace_2241849 : CollatzResearch.WordTrace tailWord_2241849 prefixEnd_2241849 1151146091801504489177431 := by
  unfold tailWord_2241849
  simp only [CollatzResearch.WordTrace]
  refine ⟨81766950455171425171888601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54511300303447616781259067 81766950455171425171888601)
  ·
    refine ⟨61325212841378568878916451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81766950455171425171888601 61325212841378568878916451)
    ·
      refine ⟨91987819262067853318374677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61325212841378568878916451 91987819262067853318374677)
      ·
        refine ⟨4311929027909430624298813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91987819262067853318374677 4311929027909430624298813)
        ·
          refine ⟨1616973385466036484112055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4311929027909430624298813 1616973385466036484112055)
          ·
            refine ⟨2425460078199054726168083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616973385466036484112055 2425460078199054726168083)
            ·
              refine ⟨3638190117298582089252125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425460078199054726168083 3638190117298582089252125)
              ·
                refine ⟨1364321293986968283469547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3638190117298582089252125 1364321293986968283469547)
                ·
                  refine ⟨2046481940980452425204321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364321293986968283469547 2046481940980452425204321)
                  ·
                    refine ⟨1534861455735339318903241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2046481940980452425204321 1534861455735339318903241)
                    ·
                      refine ⟨1151146091801504489177431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534861455735339318903241 1151146091801504489177431)
                      ·
                        rfl

theorem cell23_2241849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2241849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241849 prefixEnd_2241849 := by exact prefixLift 2241849
  have htrace : WordTrace (prefixWord ++ tailWord_2241849) baseStart_2241849 baseEnd_2241849 := by
    simpa [prefixWord, tailWord_2241849, baseEnd_2241849] using wordTrace_append hprefix tailTrace_2241849
  have hstable : (prefixWord ++ tailWord_2241849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241849).length < 2 ^ (prefixWord ++ tailWord_2241849).sum := by decide
  have hdescent : baseEnd_2241849 < baseStart_2241849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241874 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2241874 : Nat := 118140960795 + 2241874 * 2 ^ 59
def prefixEnd_2241874 : Nat := 4983230072969 + 3 ^ 40 * 2241874 * 2
def baseEnd_2241874 : Nat := 1151158928817866891364815

theorem tailTrace_2241874 : CollatzResearch.WordTrace tailWord_2241874 prefixEnd_2241874 1151158928817866891364815 := by
  unfold tailWord_2241874
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441965570020213610387169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54511908186720569627699117 20441965570020213610387169)
  ·
    refine ⟨15331474177515160207790377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20441965570020213610387169 15331474177515160207790377)
    ·
      refine ⟨11498605633136370155842783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15331474177515160207790377 11498605633136370155842783)
      ·
        refine ⟨17247908449704555233764175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11498605633136370155842783 17247908449704555233764175)
        ·
          refine ⟨25871862674556832850646263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17247908449704555233764175 25871862674556832850646263)
          ·
            refine ⟨38807794011835249275969395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25871862674556832850646263 38807794011835249275969395)
            ·
              refine ⟨58211691017752873913954093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38807794011835249275969395 58211691017752873913954093)
              ·
                refine ⟨21829384131657327717732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58211691017752873913954093 21829384131657327717732785)
                ·
                  refine ⟨16372038098742995788299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21829384131657327717732785 16372038098742995788299589)
                  ·
                    refine ⟨3069757143514311710306173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16372038098742995788299589 3069757143514311710306173)
                    ·
                      refine ⟨1151158928817866891364815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069757143514311710306173 1151158928817866891364815)
                      ·
                        rfl

theorem cell23_2241874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2241874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241874 prefixEnd_2241874 := by exact prefixLift 2241874
  have htrace : WordTrace (prefixWord ++ tailWord_2241874) baseStart_2241874 baseEnd_2241874 := by
    simpa [prefixWord, tailWord_2241874, baseEnd_2241874] using wordTrace_append hprefix tailTrace_2241874
  have hstable : (prefixWord ++ tailWord_2241874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241874).length < 2 ^ (prefixWord ++ tailWord_2241874).sum := by decide
  have hdescent : baseEnd_2241874 < baseStart_2241874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241922 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2241922 : Nat := 118140960795 + 2241922 * 2 ^ 59
def prefixEnd_2241922 : Nat := 4983230072969 + 3 ^ 40 * 2241922 * 2
def baseEnd_2241922 : Nat := 1151183575889282703564595

theorem tailTrace_2241922 : CollatzResearch.WordTrace tailWord_2241922 prefixEnd_2241922 1151183575889282703564595 := by
  unfold tailWord_2241922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20442403245976739659824005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54513075322604639092864013 20442403245976739659824005)
  ·
    refine ⟨3832950608620638686217001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20442403245976739659824005 3832950608620638686217001)
    ·
      refine ⟨2874712956465479014662751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3832950608620638686217001 2874712956465479014662751)
      ·
        refine ⟨4312069434698218521994127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874712956465479014662751 4312069434698218521994127)
        ·
          refine ⟨6468104152047327782991191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312069434698218521994127 6468104152047327782991191)
          ·
            refine ⟨9702156228070991674486787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468104152047327782991191 9702156228070991674486787)
            ·
              refine ⟨14553234342106487511730181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702156228070991674486787 14553234342106487511730181)
              ·
                refine ⟨2728731439144966408449409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14553234342106487511730181 2728731439144966408449409)
                ·
                  refine ⟨2046548579358724806337057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728731439144966408449409 2046548579358724806337057)
                  ·
                    refine ⟨1534911434519043604752793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2046548579358724806337057 1534911434519043604752793)
                    ·
                      refine ⟨1151183575889282703564595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534911434519043604752793 1151183575889282703564595)
                      ·
                        rfl

theorem cell23_2241922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2241922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241922 prefixEnd_2241922 := by exact prefixLift 2241922
  have htrace : WordTrace (prefixWord ++ tailWord_2241922) baseStart_2241922 baseEnd_2241922 := by
    simpa [prefixWord, tailWord_2241922, baseEnd_2241922] using wordTrace_append hprefix tailTrace_2241922
  have hstable : (prefixWord ++ tailWord_2241922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241922).length < 2 ^ (prefixWord ++ tailWord_2241922).sum := by decide
  have hdescent : baseEnd_2241922 < baseStart_2241922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241928 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 5]
def baseStart_2241928 : Nat := 118140960795 + 2241928 * 2 ^ 59
def prefixEnd_2241928 : Nat := 4983230072969 + 3 ^ 40 * 2241928 * 2
def baseEnd_2241928 : Nat := 127909628530356631121063

theorem tailTrace_2241928 : CollatzResearch.WordTrace tailWord_2241928 prefixEnd_2241928 127909628530356631121063 := by
  unfold tailWord_2241928
  simp only [CollatzResearch.WordTrace]
  refine ⟨40884915910942610832007219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54513221214590147776009625 40884915910942610832007219)
  ·
    refine ⟨61327373866413916248010829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40884915910942610832007219 61327373866413916248010829)
    ·
      refine ⟨22997765199905218593004061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61327373866413916248010829 22997765199905218593004061)
      ·
        refine ⟨8624161949964456972376523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22997765199905218593004061 8624161949964456972376523)
        ·
          refine ⟨12936242924946685458564785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624161949964456972376523 12936242924946685458564785)
          ·
            refine ⟨9702182193710014093923589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936242924946685458564785 9702182193710014093923589)
            ·
              refine ⟨1819159161320627642610673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9702182193710014093923589 1819159161320627642610673)
              ·
                refine ⟨1364369370990470731958005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819159161320627642610673 1364369370990470731958005)
                ·
                  refine ⟨127909628530356631121063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1364369370990470731958005 127909628530356631121063)
                  ·
                    rfl

theorem cell23_2241928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 5].length) (baseStart_2241928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241928 prefixEnd_2241928 := by exact prefixLift 2241928
  have htrace : WordTrace (prefixWord ++ tailWord_2241928) baseStart_2241928 baseEnd_2241928 := by
    simpa [prefixWord, tailWord_2241928, baseEnd_2241928] using wordTrace_append hprefix tailTrace_2241928
  have hstable : (prefixWord ++ tailWord_2241928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241928).length < 2 ^ (prefixWord ++ tailWord_2241928).sum := by decide
  have hdescent : baseEnd_2241928 < baseStart_2241928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241947 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9]
def baseStart_2241947 : Nat := 118140960795 + 2241947 * 2 ^ 59
def prefixEnd_2241947 : Nat := 4983230072969 + 3 ^ 40 * 2241947 * 2
def baseEnd_2241947 : Nat := 1151196412905645105751979

theorem tailTrace_2241947 : CollatzResearch.WordTrace tailWord_2241947 prefixEnd_2241947 1151196412905645105751979 := by
  unfold tailWord_2241947
  simp only [CollatzResearch.WordTrace]
  refine ⟨81770524808816387908956095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54513683205877591939304063 81770524808816387908956095)
  ·
    refine ⟨122655787213224581863434143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81770524808816387908956095 122655787213224581863434143)
    ·
      refine ⟨183983680819836872795151215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122655787213224581863434143 183983680819836872795151215)
      ·
        refine ⟨275975521229755309192726823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183983680819836872795151215 275975521229755309192726823)
        ·
          refine ⟨413963281844632963789090235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275975521229755309192726823 413963281844632963789090235)
          ·
            refine ⟨620944922766949445683635353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413963281844632963789090235 620944922766949445683635353)
            ·
              refine ⟨465708692075212084262726515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620944922766949445683635353 465708692075212084262726515)
              ·
                refine ⟨698563038112818126394089773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465708692075212084262726515 698563038112818126394089773)
                ·
                  refine ⟨261961139292306797397783665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698563038112818126394089773 261961139292306797397783665)
                  ·
                    refine ⟨196470854469230098048337749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261961139292306797397783665 196470854469230098048337749)
                    ·
                      refine ⟨1151196412905645105751979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 196470854469230098048337749 1151196412905645105751979)
                      ·
                        rfl

theorem cell23_2241947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_2241947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241947 prefixEnd_2241947 := by exact prefixLift 2241947
  have htrace : WordTrace (prefixWord ++ tailWord_2241947) baseStart_2241947 baseEnd_2241947 := by
    simpa [prefixWord, tailWord_2241947, baseEnd_2241947] using wordTrace_append hprefix tailTrace_2241947
  have hstable : (prefixWord ++ tailWord_2241947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241947).length < 2 ^ (prefixWord ++ tailWord_2241947).sum := by decide
  have hdescent : baseEnd_2241947 < baseStart_2241947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241981 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2241981 : Nat := 118140960795 + 2241981 * 2 ^ 59
def prefixEnd_2241981 : Nat := 4983230072969 + 3 ^ 40 * 2241981 * 2
def baseEnd_2241981 : Nat := 1151213871247897972726823

theorem tailTrace_2241981 : CollatzResearch.WordTrace tailWord_2241981 prefixEnd_2241981 1151213871247897972726823 := by
  unfold tailWord_2241981
  simp only [CollatzResearch.WordTrace]
  refine ⟨81771764890693211715693797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54514509927128807810462531 81771764890693211715693797)
  ·
    refine ⟨15332205917004977196692587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81771764890693211715693797 15332205917004977196692587)
    ·
      refine ⟨22998308875507465795038881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15332205917004977196692587 22998308875507465795038881)
      ·
        refine ⟨17248731656630599346279161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22998308875507465795038881 17248731656630599346279161)
        ·
          refine ⟨12936548742472949509709371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17248731656630599346279161 12936548742472949509709371)
          ·
            refine ⟨19404823113709424264564057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12936548742472949509709371 19404823113709424264564057)
            ·
              refine ⟨14553617335282068198423043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19404823113709424264564057 14553617335282068198423043)
              ·
                refine ⟨21830426002923102297634565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14553617335282068198423043 21830426002923102297634565)
                ·
                  refine ⟨4093204875548081680806481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21830426002923102297634565 4093204875548081680806481)
                  ·
                    refine ⟨3069903656661061260604861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4093204875548081680806481 3069903656661061260604861)
                    ·
                      refine ⟨1151213871247897972726823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069903656661061260604861 1151213871247897972726823)
                      ·
                        rfl

theorem cell23_2241981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2241981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241981 prefixEnd_2241981 := by exact prefixLift 2241981
  have htrace : WordTrace (prefixWord ++ tailWord_2241981) baseStart_2241981 baseEnd_2241981 := by
    simpa [prefixWord, tailWord_2241981, baseEnd_2241981] using wordTrace_append hprefix tailTrace_2241981
  have hstable : (prefixWord ++ tailWord_2241981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241981).length < 2 ^ (prefixWord ++ tailWord_2241981).sum := by decide
  have hdescent : baseEnd_2241981 < baseStart_2241981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2241988 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2241988 : Nat := 118140960795 + 2241988 * 2 ^ 59
def prefixEnd_2241988 : Nat := 4983230072969 + 3 ^ 40 * 2241988 * 2
def baseEnd_2241988 : Nat := 383739155204159815113097

theorem tailTrace_2241988 : CollatzResearch.WordTrace tailWord_2241988 prefixEnd_2241988 383739155204159815113097 := by
  unfold tailWord_2241988
  simp only [CollatzResearch.WordTrace]
  refine ⟨40886010100833925955599309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54514680134445234607465745 40886010100833925955599309)
  ·
    refine ⟨15332253787812722233349741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40886010100833925955599309 15332253787812722233349741)
    ·
      refine ⟨5749595170429770837506153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15332253787812722233349741 5749595170429770837506153)
      ·
        refine ⟨4312196377822328128129615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5749595170429770837506153 4312196377822328128129615)
        ·
          refine ⟨6468294566733492192194423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312196377822328128129615 6468294566733492192194423)
          ·
            refine ⟨9702441850100238288291635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468294566733492192194423 9702441850100238288291635)
            ·
              refine ⟨14553662775150357432437453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702441850100238288291635 14553662775150357432437453)
              ·
                refine ⟨5457623540681384037164045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14553662775150357432437453 5457623540681384037164045)
                ·
                  refine ⟨2046608827755519013936517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5457623540681384037164045 2046608827755519013936517)
                  ·
                    refine ⟨383739155204159815113097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046608827755519013936517 383739155204159815113097)
                    ·
                      rfl

theorem cell23_2241988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2241988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2241988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2241988 prefixEnd_2241988 := by exact prefixLift 2241988
  have htrace : WordTrace (prefixWord ++ tailWord_2241988) baseStart_2241988 baseEnd_2241988 := by
    simpa [prefixWord, tailWord_2241988, baseEnd_2241988] using wordTrace_append hprefix tailTrace_2241988
  have hstable : (prefixWord ++ tailWord_2241988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2241988).length < 2 ^ (prefixWord ++ tailWord_2241988).sum := by decide
  have hdescent : baseEnd_2241988 < baseStart_2241988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2241988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242031 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 1, 5]
def baseStart_2242031 : Nat := 118140960795 + 2242031 * 2 ^ 59
def prefixEnd_2242031 : Nat := 4983230072969 + 3 ^ 40 * 2242031 * 2
def baseEnd_2242031 : Nat := 383746515093540925700531

theorem tailTrace_2242031 : CollatzResearch.WordTrace tailWord_2242031 prefixEnd_2242031 383746515093540925700531 := by
  unfold tailWord_2242031
  simp only [CollatzResearch.WordTrace]
  refine ⟨81773588540512070255013947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54515725693674713503342631 81773588540512070255013947)
  ·
    refine ⟨122660382810768105382520921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81773588540512070255013947 122660382810768105382520921)
    ·
      refine ⟨91995287108076079036890691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122660382810768105382520921 91995287108076079036890691)
      ·
        refine ⟨137992930662114118555336037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91995287108076079036890691 137992930662114118555336037)
        ·
          refine ⟨25873674499146397229125507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137992930662114118555336037 25873674499146397229125507)
          ·
            refine ⟨38810511748719595843688261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25873674499146397229125507 38810511748719595843688261)
            ·
              refine ⟨7276970952884924220691549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38810511748719595843688261 7276970952884924220691549)
              ·
                refine ⟨2728864107331846582759331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7276970952884924220691549 2728864107331846582759331)
                ·
                  refine ⟨4093296160997769874138997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728864107331846582759331 4093296160997769874138997)
                  ·
                    refine ⟨383746515093540925700531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4093296160997769874138997 383746515093540925700531)
                    ·
                      rfl

theorem cell23_2242031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_2242031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242031 prefixEnd_2242031 := by exact prefixLift 2242031
  have htrace : WordTrace (prefixWord ++ tailWord_2242031) baseStart_2242031 baseEnd_2242031 := by
    simpa [prefixWord, tailWord_2242031, baseEnd_2242031] using wordTrace_append hprefix tailTrace_2242031
  have hstable : (prefixWord ++ tailWord_2242031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242031).length < 2 ^ (prefixWord ++ tailWord_2242031).sum := by decide
  have hdescent : baseEnd_2242031 < baseStart_2242031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242045 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2242045 : Nat := 118140960795 + 2242045 * 2 ^ 59
def prefixEnd_2242045 : Nat := 4983230072969 + 3 ^ 40 * 2242045 * 2
def baseEnd_2242045 : Nat := 1151246734009785722326529

theorem tailTrace_2242045 : CollatzResearch.WordTrace tailWord_2242045 prefixEnd_2242045 1151246734009785722326529 := by
  unfold tailWord_2242045
  simp only [CollatzResearch.WordTrace]
  refine ⟨81774099162461350646023589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54516066108307567097349059 81774099162461350646023589)
  ·
    refine ⟨15332643592961503246129423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81774099162461350646023589 15332643592961503246129423)
    ·
      refine ⟨22998965389442254869194135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15332643592961503246129423 22998965389442254869194135)
      ·
        refine ⟨34498448084163382303791203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22998965389442254869194135 34498448084163382303791203)
        ·
          refine ⟨51747672126245073455686805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34498448084163382303791203 51747672126245073455686805)
          ·
            refine ⟨2425672130917737818235319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51747672126245073455686805 2425672130917737818235319)
            ·
              refine ⟨3638508196376606727352979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425672130917737818235319 3638508196376606727352979)
              ·
                refine ⟨5457762294564910091029469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638508196376606727352979 5457762294564910091029469)
                ·
                  refine ⟨2046660860461841284136051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5457762294564910091029469 2046660860461841284136051)
                  ·
                    refine ⟨3069991290692761926204077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046660860461841284136051 3069991290692761926204077)
                    ·
                      refine ⟨1151246734009785722326529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3069991290692761926204077 1151246734009785722326529)
                      ·
                        rfl

theorem cell23_2242045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2242045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242045 prefixEnd_2242045 := by exact prefixLift 2242045
  have htrace : WordTrace (prefixWord ++ tailWord_2242045) baseStart_2242045 baseEnd_2242045 := by
    simpa [prefixWord, tailWord_2242045, baseEnd_2242045] using wordTrace_append hprefix tailTrace_2242045
  have hstable : (prefixWord ++ tailWord_2242045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242045).length < 2 ^ (prefixWord ++ tailWord_2242045).sum := by decide
  have hdescent : baseEnd_2242045 < baseStart_2242045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242051 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 6, 2]
def baseStart_2242051 : Nat := 118140960795 + 2242051 * 2 ^ 59
def prefixEnd_2242051 : Nat := 4983230072969 + 3 ^ 40 * 2242051 * 2
def baseEnd_2242051 : Nat := 1151249814893712698851501

theorem tailTrace_2242051 : CollatzResearch.WordTrace tailWord_2242051 prefixEnd_2242051 1151249814893712698851501 := by
  unfold tailWord_2242051
  simp only [CollatzResearch.WordTrace]
  refine ⟨81774318000439613670742007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54516212000293075780494671 81774318000439613670742007)
  ·
    refine ⟨122661477000659420506113011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81774318000439613670742007 122661477000659420506113011)
    ·
      refine ⟨183992215500989130759169517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122661477000659420506113011 183992215500989130759169517)
      ·
        refine ⟨68997080812870924034688569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183992215500989130759169517 68997080812870924034688569)
        ·
          refine ⟨51747810609653193026016427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68997080812870924034688569 51747810609653193026016427)
          ·
            refine ⟨77621715914479789539024641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51747810609653193026016427 77621715914479789539024641)
            ·
              refine ⟨58216286935859842154268481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77621715914479789539024641 58216286935859842154268481)
              ·
                refine ⟨43662215201894881615701361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58216286935859842154268481 43662215201894881615701361)
                ·
                  refine ⟨32746661401421161211776021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43662215201894881615701361 32746661401421161211776021)
                  ·
                    refine ⟨1534999753191616931802001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32746661401421161211776021 1534999753191616931802001)
                    ·
                      refine ⟨1151249814893712698851501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1534999753191616931802001 1151249814893712698851501)
                      ·
                        rfl

theorem cell23_2242051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_2242051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242051 prefixEnd_2242051 := by exact prefixLift 2242051
  have htrace : WordTrace (prefixWord ++ tailWord_2242051) baseStart_2242051 baseEnd_2242051 := by
    simpa [prefixWord, tailWord_2242051, baseEnd_2242051] using wordTrace_append hprefix tailTrace_2242051
  have hstable : (prefixWord ++ tailWord_2242051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242051).length < 2 ^ (prefixWord ++ tailWord_2242051).sum := by decide
  have hdescent : baseEnd_2242051 < baseStart_2242051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242052 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 6]
def baseStart_2242052 : Nat := 118140960795 + 2242052 * 2 ^ 59
def prefixEnd_2242052 : Nat := 4983230072969 + 3 ^ 40 * 2242052 * 2
def baseEnd_2242052 : Nat := 127916703152707466104333

theorem tailTrace_2242052 : CollatzResearch.WordTrace tailWord_2242052 prefixEnd_2242052 127916703152707466104333 := by
  unfold tailWord_2242052
  simp only [CollatzResearch.WordTrace]
  refine ⟨40887177236717995420764205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54516236315623993894352273 40887177236717995420764205)
  ·
    refine ⟨15332691463769248282786577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40887177236717995420764205 15332691463769248282786577)
    ·
      refine ⟨11499518597826936212089933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15332691463769248282786577 11499518597826936212089933)
      ·
        refine ⟨4312319474185101079533725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11499518597826936212089933 4312319474185101079533725)
        ·
          refine ⟨1617119802819412904825147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4312319474185101079533725 1617119802819412904825147)
          ·
            refine ⟨2425679704229119357237721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617119802819412904825147 2425679704229119357237721)
            ·
              refine ⟨1819259778171839517928291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425679704229119357237721 1819259778171839517928291)
              ·
                refine ⟨2728889667257759276892437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819259778171839517928291 2728889667257759276892437)
                ·
                  refine ⟨127916703152707466104333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2728889667257759276892437 127916703152707466104333)
                  ·
                    rfl

theorem cell23_2242052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_2242052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242052 prefixEnd_2242052 := by exact prefixLift 2242052
  have htrace : WordTrace (prefixWord ++ tailWord_2242052) baseStart_2242052 baseEnd_2242052 := by
    simpa [prefixWord, tailWord_2242052, baseEnd_2242052] using wordTrace_append hprefix tailTrace_2242052
  have hstable : (prefixWord ++ tailWord_2242052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242052).length < 2 ^ (prefixWord ++ tailWord_2242052).sum := by decide
  have hdescent : baseEnd_2242052 < baseStart_2242052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242064 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_2242064 : Nat := 118140960795 + 2242064 * 2 ^ 59
def prefixEnd_2242064 : Nat := 4983230072969 + 3 ^ 40 * 2242064 * 2
def baseEnd_2242064 : Nat := 1151256490142221147988941

theorem tailTrace_2242064 : CollatzResearch.WordTrace tailWord_2242064 prefixEnd_2242064 1151256490142221147988941 := by
  unfold tailWord_2242064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40887396074696258445482623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54516528099595011260643497 40887396074696258445482623)
  ·
    refine ⟨61331094112044387668223935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40887396074696258445482623 61331094112044387668223935)
    ·
      refine ⟨91996641168066581502335903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61331094112044387668223935 91996641168066581502335903)
      ·
        refine ⟨137994961752099872253503855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91996641168066581502335903 137994961752099872253503855)
        ·
          refine ⟨206992442628149808380255783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137994961752099872253503855 206992442628149808380255783)
          ·
            refine ⟨310488663942224712570383675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206992442628149808380255783 310488663942224712570383675)
            ·
              refine ⟨465732995913337068855575513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310488663942224712570383675 465732995913337068855575513)
              ·
                refine ⟨349299746935002801641681635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465732995913337068855575513 349299746935002801641681635)
                ·
                  refine ⟨523949620402504202462522453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349299746935002801641681635 523949620402504202462522453)
                  ·
                    refine ⟨6140034614091846122607685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 523949620402504202462522453 6140034614091846122607685)
                    ·
                      refine ⟨1151256490142221147988941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6140034614091846122607685 1151256490142221147988941)
                      ·
                        rfl

theorem cell23_2242064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_2242064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242064 prefixEnd_2242064 := by exact prefixLift 2242064
  have htrace : WordTrace (prefixWord ++ tailWord_2242064) baseStart_2242064 baseEnd_2242064 := by
    simpa [prefixWord, tailWord_2242064, baseEnd_2242064] using wordTrace_append hprefix tailTrace_2242064
  have hstable : (prefixWord ++ tailWord_2242064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242064).length < 2 ^ (prefixWord ++ tailWord_2242064).sum := by decide
  have hdescent : baseEnd_2242064 < baseStart_2242064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242081 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2242081 : Nat := 118140960795 + 2242081 * 2 ^ 59
def prefixEnd_2242081 : Nat := 4983230072969 + 3 ^ 40 * 2242081 * 2
def baseEnd_2242081 : Nat := 1151265219313347581476363

theorem tailTrace_2242081 : CollatzResearch.WordTrace tailWord_2242081 prefixEnd_2242081 1151265219313347581476363 := by
  unfold tailWord_2242081
  simp only [CollatzResearch.WordTrace]
  refine ⟨81775412190330928794334097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54516941460220619196222731 81775412190330928794334097)
  ·
    refine ⟨61331559142748196595750573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81775412190330928794334097 61331559142748196595750573)
    ·
      refine ⟨22999334678530573723406465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61331559142748196595750573 22999334678530573723406465)
      ·
        refine ⟨17249501008897930292554849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22999334678530573723406465 17249501008897930292554849)
        ·
          refine ⟨12937125756673447719416137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17249501008897930292554849 12937125756673447719416137)
          ·
            refine ⟨9702844317505085789562103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12937125756673447719416137 9702844317505085789562103)
            ·
              refine ⟨14554266476257628684343155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702844317505085789562103 14554266476257628684343155)
              ·
                refine ⟨21831399714386443026514733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14554266476257628684343155 21831399714386443026514733)
                ·
                  refine ⟨8186774892894916134943025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21831399714386443026514733 8186774892894916134943025)
                  ·
                    refine ⟨6140081169671187101207269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8186774892894916134943025 6140081169671187101207269)
                    ·
                      refine ⟨1151265219313347581476363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6140081169671187101207269 1151265219313347581476363)
                      ·
                        rfl

theorem cell23_2242081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2242081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242081 prefixEnd_2242081 := by exact prefixLift 2242081
  have htrace : WordTrace (prefixWord ++ tailWord_2242081) baseStart_2242081 baseEnd_2242081 := by
    simpa [prefixWord, tailWord_2242081, baseEnd_2242081] using wordTrace_append hprefix tailTrace_2242081
  have hstable : (prefixWord ++ tailWord_2242081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242081).length < 2 ^ (prefixWord ++ tailWord_2242081).sum := by decide
  have hdescent : baseEnd_2242081 < baseStart_2242081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242108 : List Nat := [2, 2, 2, 2, 4, 2, 1, 8]
def baseStart_2242108 : Nat := 118140960795 + 2242108 * 2 ^ 59
def prefixEnd_2242108 : Nat := 4983230072969 + 3 ^ 40 * 2242108 * 2
def baseEnd_2242108 : Nat := 42639966047815517623657

theorem tailTrace_2242108 : CollatzResearch.WordTrace tailWord_2242108 prefixEnd_2242108 42639966047815517623657 := by
  unfold tailWord_2242108
  simp only [CollatzResearch.WordTrace]
  refine ⟨40888198480616556202783489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54517597974155408270377985 40888198480616556202783489)
  ·
    refine ⟨30666148860462417152087617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40888198480616556202783489 30666148860462417152087617)
    ·
      refine ⟨22999611645346812864065713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30666148860462417152087617 22999611645346812864065713)
      ·
        refine ⟨17249708734010109648049285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22999611645346812864065713 17249708734010109648049285)
        ·
          refine ⟨3234320387626895559009241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17249708734010109648049285 3234320387626895559009241)
          ·
            refine ⟨2425740290720171669256931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234320387626895559009241 2425740290720171669256931)
            ·
              refine ⟨3638610436080257503885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425740290720171669256931 3638610436080257503885397)
              ·
                refine ⟨42639966047815517623657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3638610436080257503885397 42639966047815517623657)
                ·
                  rfl

theorem cell23_2242108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 8].length) (baseStart_2242108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242108 prefixEnd_2242108 := by exact prefixLift 2242108
  have htrace : WordTrace (prefixWord ++ tailWord_2242108) baseStart_2242108 baseEnd_2242108 := by
    simpa [prefixWord, tailWord_2242108, baseEnd_2242108] using wordTrace_append hprefix tailTrace_2242108
  have hstable : (prefixWord ++ tailWord_2242108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242108).length < 2 ^ (prefixWord ++ tailWord_2242108).sum := by decide
  have hdescent : baseEnd_2242108 < baseStart_2242108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242125 : List Nat := [1, 6, 1, 1, 3, 1, 3, 7]
def baseStart_2242125 : Nat := 118140960795 + 2242125 * 2 ^ 59
def prefixEnd_2242125 : Nat := 4983230072969 + 3 ^ 40 * 2242125 * 2
def baseEnd_2242125 : Nat := 42640289350449829975043

theorem tailTrace_2242125 : CollatzResearch.WordTrace tailWord_2242125 prefixEnd_2242125 42640289350449829975043 := by
  unfold tailWord_2242125
  simp only [CollatzResearch.WordTrace]
  refine ⟨81777017002171524308935829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54518011334781016205957219 81777017002171524308935829)
  ·
    refine ⟨3833297671976790201981367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81777017002171524308935829 3833297671976790201981367)
    ·
      refine ⟨5749946507965185302972051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833297671976790201981367 5749946507965185302972051)
      ·
        refine ⟨8624919761947777954458077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749946507965185302972051 8624919761947777954458077)
        ·
          refine ⟨3234344910730416732921779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8624919761947777954458077 3234344910730416732921779)
          ·
            refine ⟨4851517366095625099382669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234344910730416732921779 4851517366095625099382669)
            ·
              refine ⟨1819319012285859412268501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4851517366095625099382669 1819319012285859412268501)
              ·
                refine ⟨42640289350449829975043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1819319012285859412268501 42640289350449829975043)
                ·
                  rfl

theorem cell23_2242125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 7].length) (baseStart_2242125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242125 prefixEnd_2242125 := by exact prefixLift 2242125
  have htrace : WordTrace (prefixWord ++ tailWord_2242125) baseStart_2242125 baseEnd_2242125 := by
    simpa [prefixWord, tailWord_2242125, baseEnd_2242125] using wordTrace_append hprefix tailTrace_2242125
  have hstable : (prefixWord ++ tailWord_2242125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242125).length < 2 ^ (prefixWord ++ tailWord_2242125).sum := by decide
  have hdescent : baseEnd_2242125 < baseStart_2242125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242128 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2]
def baseStart_2242128 : Nat := 118140960795 + 2242128 * 2 ^ 59
def prefixEnd_2242128 : Nat := 4983230072969 + 3 ^ 40 * 2242128 * 2
def baseEnd_2242128 : Nat := 1151289352904108897588647

theorem tailTrace_2242128 : CollatzResearch.WordTrace tailWord_2242128 prefixEnd_2242128 1151289352904108897588647 := by
  unfold tailWord_2242128
  simp only [CollatzResearch.WordTrace]
  refine ⟨40888563210580327910647519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54518084280773770547530025 40888563210580327910647519)
  ·
    refine ⟨61332844815870491865971279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40888563210580327910647519 61332844815870491865971279)
    ·
      refine ⟨91999267223805737798956919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61332844815870491865971279 91999267223805737798956919)
      ·
        refine ⟨137998900835708606698435379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91999267223805737798956919 137998900835708606698435379)
        ·
          refine ⟨206998351253562910047653069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137998900835708606698435379 206998351253562910047653069)
          ·
            refine ⟨77624381720086091267869901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206998351253562910047653069 77624381720086091267869901)
            ·
              refine ⟨29109143145032284225451213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77624381720086091267869901 29109143145032284225451213)
              ·
                refine ⟨10915928679387106584544205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29109143145032284225451213 10915928679387106584544205)
                ·
                  refine ⟨4093473254770164969204077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10915928679387106584544205 4093473254770164969204077)
                  ·
                    refine ⟨1535052470538811863451529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4093473254770164969204077 1535052470538811863451529)
                    ·
                      refine ⟨1151289352904108897588647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535052470538811863451529 1151289352904108897588647)
                      ·
                        rfl

theorem cell23_2242128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3, 2].length) (baseStart_2242128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242128 prefixEnd_2242128 := by exact prefixLift 2242128
  have htrace : WordTrace (prefixWord ++ tailWord_2242128) baseStart_2242128 baseEnd_2242128 := by
    simpa [prefixWord, tailWord_2242128, baseEnd_2242128] using wordTrace_append hprefix tailTrace_2242128
  have hstable : (prefixWord ++ tailWord_2242128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242128).length < 2 ^ (prefixWord ++ tailWord_2242128).sum := by decide
  have hdescent : baseEnd_2242128 < baseStart_2242128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242145 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_2242145 : Nat := 118140960795 + 2242145 * 2 ^ 59
def prefixEnd_2242145 : Nat := 4983230072969 + 3 ^ 40 * 2242145 * 2
def baseEnd_2242145 : Nat := 1151298082075235331076069

theorem tailTrace_2242145 : CollatzResearch.WordTrace tailWord_2242145 prefixEnd_2242145 1151298082075235331076069 := by
  unfold tailWord_2242145
  simp only [CollatzResearch.WordTrace]
  refine ⟨81777746462099067724663889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54518497641399378483109259 81777746462099067724663889)
  ·
    refine ⟨61333309846574300793497917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81777746462099067724663889 61333309846574300793497917)
    ·
      refine ⟨22999991192465362797561719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61333309846574300793497917 22999991192465362797561719)
      ·
        refine ⟨34499986788698044196342579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22999991192465362797561719 34499986788698044196342579)
        ·
          refine ⟨51749980183047066294513869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34499986788698044196342579 51749980183047066294513869)
          ·
            refine ⟨19406242568642649860442701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51749980183047066294513869 19406242568642649860442701)
            ·
              refine ⟨7277340963240993697666013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19406242568642649860442701 7277340963240993697666013)
              ·
                refine ⟨2729002861215372636624755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7277340963240993697666013 2729002861215372636624755)
                ·
                  refine ⟨4093504291823058954937133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729002861215372636624755 4093504291823058954937133)
                  ·
                    refine ⟨1535064109433647108101425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4093504291823058954937133 1535064109433647108101425)
                    ·
                      refine ⟨1151298082075235331076069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535064109433647108101425 1151298082075235331076069)
                      ·
                        rfl

theorem cell23_2242145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_2242145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242145 prefixEnd_2242145 := by exact prefixLift 2242145
  have htrace : WordTrace (prefixWord ++ tailWord_2242145) baseStart_2242145 baseEnd_2242145 := by
    simpa [prefixWord, tailWord_2242145, baseEnd_2242145] using wordTrace_append hprefix tailTrace_2242145
  have hstable : (prefixWord ++ tailWord_2242145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242145).length < 2 ^ (prefixWord ++ tailWord_2242145).sum := by decide
  have hdescent : baseEnd_2242145 < baseStart_2242145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242151 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 6]
def baseStart_2242151 : Nat := 118140960795 + 2242151 * 2 ^ 59
def prefixEnd_2242151 : Nat := 4983230072969 + 3 ^ 40 * 2242151 * 2
def baseEnd_2242151 : Nat := 383767054319720769200347

theorem tailTrace_2242151 : CollatzResearch.WordTrace tailWord_2242151 prefixEnd_2242151 383767054319720769200347 := by
  unfold tailWord_2242151
  simp only [CollatzResearch.WordTrace]
  refine ⟨81777965300077330749382307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54518643533384887166254871 81777965300077330749382307)
  ·
    refine ⟨122666947950115996124073461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81777965300077330749382307 122666947950115996124073461)
    ·
      refine ⟨11500026370323374636631887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122666947950115996124073461 11500026370323374636631887)
      ·
        refine ⟨17250039555485061954947831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11500026370323374636631887 17250039555485061954947831)
        ·
          refine ⟨25875059333227592932421747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17250039555485061954947831 25875059333227592932421747)
          ·
            refine ⟨38812588999841389398632621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25875059333227592932421747 38812588999841389398632621)
            ·
              refine ⟨14554720874940521024487233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38812588999841389398632621 14554720874940521024487233)
              ·
                refine ⟨10916040656205390768365425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14554720874940521024487233 10916040656205390768365425)
                ·
                  refine ⟨8187030492154043076274069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916040656205390768365425 8187030492154043076274069)
                  ·
                    refine ⟨383767054319720769200347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8187030492154043076274069 383767054319720769200347)
                    ·
                      rfl

theorem cell23_2242151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_2242151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242151 prefixEnd_2242151 := by exact prefixLift 2242151
  have htrace : WordTrace (prefixWord ++ tailWord_2242151) baseStart_2242151 baseEnd_2242151 := by
    simpa [prefixWord, tailWord_2242151, baseEnd_2242151] using wordTrace_append hprefix tailTrace_2242151
  have hstable : (prefixWord ++ tailWord_2242151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242151).length < 2 ^ (prefixWord ++ tailWord_2242151).sum := by decide
  have hdescent : baseEnd_2242151 < baseStart_2242151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242152 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2242152 : Nat := 118140960795 + 2242152 * 2 ^ 59
def prefixEnd_2242152 : Nat := 4983230072969 + 3 ^ 40 * 2242152 * 2
def baseEnd_2242152 : Nat := 1151301676439816803688537

theorem tailTrace_2242152 : CollatzResearch.WordTrace tailWord_2242152 prefixEnd_2242152 1151301676439816803688537 := by
  unfold tailWord_2242152
  simp only [CollatzResearch.WordTrace]
  refine ⟨40889000886536853960084355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54518667848715805280112473 40889000886536853960084355)
  ·
    refine ⟨61333501329805280940126533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40889000886536853960084355 61333501329805280940126533)
    ·
      refine ⟨11500031499338490176273725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61333501329805280940126533 11500031499338490176273725)
      ·
        refine ⟨4312511812251933816102647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11500031499338490176273725 4312511812251933816102647)
        ·
          refine ⟨6468767718377900724153971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312511812251933816102647 6468767718377900724153971)
          ·
            refine ⟨9703151577566851086230957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468767718377900724153971 9703151577566851086230957)
            ·
              refine ⟨3638681841587569157336609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9703151577566851086230957 3638681841587569157336609)
              ·
                refine ⟨2729011381190676868002457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638681841587569157336609 2729011381190676868002457)
                ·
                  refine ⟨2046758535893007651001843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729011381190676868002457 2046758535893007651001843)
                  ·
                    refine ⟨3070137803839511476502765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046758535893007651001843 3070137803839511476502765)
                    ·
                      refine ⟨1151301676439816803688537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070137803839511476502765 1151301676439816803688537)
                      ·
                        rfl

theorem cell23_2242152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2242152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242152 prefixEnd_2242152 := by exact prefixLift 2242152
  have htrace : WordTrace (prefixWord ++ tailWord_2242152) baseStart_2242152 baseEnd_2242152 := by
    simpa [prefixWord, tailWord_2242152, baseEnd_2242152] using wordTrace_append hprefix tailTrace_2242152
  have hstable : (prefixWord ++ tailWord_2242152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242152).length < 2 ^ (prefixWord ++ tailWord_2242152).sum := by decide
  have hdescent : baseEnd_2242152 < baseStart_2242152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242161 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_2242161 : Nat := 118140960795 + 2242161 * 2 ^ 59
def prefixEnd_2242161 : Nat := 4983230072969 + 3 ^ 40 * 2242161 * 2
def baseEnd_2242161 : Nat := 1151306297765707268475995

theorem tailTrace_2242161 : CollatzResearch.WordTrace tailWord_2242161 prefixEnd_2242161 1151306297765707268475995 := by
  unfold tailWord_2242161
  simp only [CollatzResearch.WordTrace]
  refine ⟨81778330030041102457246337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54518886686694068304830891 81778330030041102457246337)
  ·
    refine ⟨61333747522530826842934753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81778330030041102457246337 61333747522530826842934753)
    ·
      refine ⟨46000310641898120132201065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61333747522530826842934753 46000310641898120132201065)
      ·
        refine ⟨34500232981423590099150799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46000310641898120132201065 34500232981423590099150799)
        ·
          refine ⟨51750349472135385148726199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34500232981423590099150799 51750349472135385148726199)
          ·
            refine ⟨77625524208203077723089299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51750349472135385148726199 77625524208203077723089299)
            ·
              refine ⟨116438286312304616584633949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77625524208203077723089299 116438286312304616584633949)
              ·
                refine ⟨43664357367114231219237731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116438286312304616584633949 43664357367114231219237731)
                ·
                  refine ⟨65496536050671346828856597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43664357367114231219237731 65496536050671346828856597)
                  ·
                    refine ⟨3070150127375219382602653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65496536050671346828856597 3070150127375219382602653)
                    ·
                      refine ⟨1151306297765707268475995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070150127375219382602653 1151306297765707268475995)
                      ·
                        rfl

theorem cell23_2242161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_2242161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242161 prefixEnd_2242161 := by exact prefixLift 2242161
  have htrace : WordTrace (prefixWord ++ tailWord_2242161) baseStart_2242161 baseEnd_2242161 := by
    simpa [prefixWord, tailWord_2242161, baseEnd_2242161] using wordTrace_append hprefix tailTrace_2242161
  have hstable : (prefixWord ++ tailWord_2242161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242161).length < 2 ^ (prefixWord ++ tailWord_2242161).sum := by decide
  have hdescent : baseEnd_2242161 < baseStart_2242161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242171 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4]
def baseStart_2242171 : Nat := 118140960795 + 2242171 * 2 ^ 59
def prefixEnd_2242171 : Nat := 4983230072969 + 3 ^ 40 * 2242171 * 2
def baseEnd_2242171 : Nat := 1151311432572252229350949

theorem tailTrace_2242171 : CollatzResearch.WordTrace tailWord_2242171 prefixEnd_2242171 1151311432572252229350949 := by
  unfold tailWord_2242171
  simp only [CollatzResearch.WordTrace]
  refine ⟨81778694760004874165110367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54519129840003249443406911 81778694760004874165110367)
  ·
    refine ⟨122668042140007311247665551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81778694760004874165110367 122668042140007311247665551)
    ·
      refine ⟨184002063210010966871498327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122668042140007311247665551 184002063210010966871498327)
      ·
        refine ⟨276003094815016450307247491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184002063210010966871498327 276003094815016450307247491)
        ·
          refine ⟨414004642222524675460871237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276003094815016450307247491 414004642222524675460871237)
          ·
            refine ⟨77625870416723376648913357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414004642222524675460871237 77625870416723376648913357)
            ·
              refine ⟨29109701406271266243342509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77625870416723376648913357 29109701406271266243342509)
              ·
                refine ⟨10916138027351724841253441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29109701406271266243342509 10916138027351724841253441)
                ·
                  refine ⟨8187103520513793630940081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10916138027351724841253441 8187103520513793630940081)
                  ·
                    refine ⟨6140327640385345223205061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8187103520513793630940081 6140327640385345223205061)
                    ·
                      refine ⟨1151311432572252229350949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6140327640385345223205061 1151311432572252229350949)
                      ·
                        rfl

theorem cell23_2242171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 4].length) (baseStart_2242171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242171 prefixEnd_2242171 := by exact prefixLift 2242171
  have htrace : WordTrace (prefixWord ++ tailWord_2242171) baseStart_2242171 baseEnd_2242171 := by
    simpa [prefixWord, tailWord_2242171, baseEnd_2242171] using wordTrace_append hprefix tailTrace_2242171
  have hstable : (prefixWord ++ tailWord_2242171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242171).length < 2 ^ (prefixWord ++ tailWord_2242171).sum := by decide
  have hdescent : baseEnd_2242171 < baseStart_2242171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242181 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 7]
def baseStart_2242181 : Nat := 118140960795 + 2242181 * 2 ^ 59
def prefixEnd_2242181 : Nat := 4983230072969 + 3 ^ 40 * 2242181 * 2
def baseEnd_2242181 : Nat := 127924063042088576691767

theorem tailTrace_2242181 : CollatzResearch.WordTrace tailWord_2242181 prefixEnd_2242181 127924063042088576691767 := by
  unfold tailWord_2242181
  simp only [CollatzResearch.WordTrace]
  refine ⟨81779059489968645872974397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54519372993312430581982931 81779059489968645872974397)
  ·
    refine ⟨30667147308738242202365399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81779059489968645872974397 30667147308738242202365399)
    ·
      refine ⟨46000720963107363303548099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30667147308738242202365399 46000720963107363303548099)
      ·
        refine ⟨69001081444661044955322149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46000720963107363303548099 69001081444661044955322149)
        ·
          refine ⟨12937702770873945929122903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69001081444661044955322149 12937702770873945929122903)
          ·
            refine ⟨19406554156310918893684355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12937702770873945929122903 19406554156310918893684355)
            ·
              refine ⟨29109831234466378340526533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19406554156310918893684355 29109831234466378340526533)
              ·
                refine ⟨5458093356462445938848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29109831234466378340526533 5458093356462445938848725)
                ·
                  refine ⟨127924063042088576691767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5458093356462445938848725 127924063042088576691767)
                  ·
                    rfl

theorem cell23_2242181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_2242181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242181 prefixEnd_2242181 := by exact prefixLift 2242181
  have htrace : WordTrace (prefixWord ++ tailWord_2242181) baseStart_2242181 baseEnd_2242181 := by
    simpa [prefixWord, tailWord_2242181, baseEnd_2242181] using wordTrace_append hprefix tailTrace_2242181
  have hstable : (prefixWord ++ tailWord_2242181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242181).length < 2 ^ (prefixWord ++ tailWord_2242181).sum := by decide
  have hdescent : baseEnd_2242181 < baseStart_2242181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242302 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2242302 : Nat := 118140960795 + 2242302 * 2 ^ 59
def prefixEnd_2242302 : Nat := 4983230072969 + 3 ^ 40 * 2242302 * 2
def baseEnd_2242302 : Nat := 1151378698537991216812847

theorem tailTrace_2242302 : CollatzResearch.WordTrace tailWord_2242302 prefixEnd_2242302 1151378698537991216812847 := by
  unfold tailWord_2242302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222934090316285442266145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54522315148353522358752773 10222934090316285442266145)
  ·
    refine ⟨7667200567737214081699609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10222934090316285442266145 7667200567737214081699609)
    ·
      refine ⟨5750400425802910561274707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7667200567737214081699609 5750400425802910561274707)
      ·
        refine ⟨8625600638704365841912061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750400425802910561274707 8625600638704365841912061)
        ·
          refine ⟨3234600239514137190717023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8625600638704365841912061 3234600239514137190717023)
          ·
            refine ⟨4851900359271205786075535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234600239514137190717023 4851900359271205786075535)
            ·
              refine ⟨7277850538906808679113303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851900359271205786075535 7277850538906808679113303)
              ·
                refine ⟨10916775808360213018669955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7277850538906808679113303 10916775808360213018669955)
                ·
                  refine ⟨16375163712540319528004933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10916775808360213018669955 16375163712540319528004933)
                  ·
                    refine ⟨3070343196101309911500925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16375163712540319528004933 3070343196101309911500925)
                    ·
                      refine ⟨1151378698537991216812847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070343196101309911500925 1151378698537991216812847)
                      ·
                        rfl

theorem cell23_2242302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2242302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242302 prefixEnd_2242302 := by exact prefixLift 2242302
  have htrace : WordTrace (prefixWord ++ tailWord_2242302) baseStart_2242302 baseEnd_2242302 := by
    simpa [prefixWord, tailWord_2242302, baseEnd_2242302] using wordTrace_append hprefix tailTrace_2242302
  have hstable : (prefixWord ++ tailWord_2242302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242302).length < 2 ^ (prefixWord ++ tailWord_2242302).sum := by decide
  have hdescent : baseEnd_2242302 < baseStart_2242302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242322 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_2242322 : Nat := 118140960795 + 2242322 * 2 ^ 59
def prefixEnd_2242322 : Nat := 4983230072969 + 3 ^ 40 * 2242322 * 2
def baseEnd_2242322 : Nat := 127932107572342348729195

theorem tailTrace_2242322 : CollatzResearch.WordTrace tailWord_2242322 prefixEnd_2242322 127932107572342348729195 := by
  unfold tailWord_2242322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20446050545614456738464305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54522801454971884635904813 20446050545614456738464305)
  ·
    refine ⟨15334537909210842553848229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20446050545614456738464305 15334537909210842553848229)
    ·
      refine ⟨2875225857977032978846543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15334537909210842553848229 2875225857977032978846543)
      ·
        refine ⟨4312838786965549468269815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875225857977032978846543 4312838786965549468269815)
        ·
          refine ⟨6469258180448324202404723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312838786965549468269815 6469258180448324202404723)
          ·
            refine ⟨9703887270672486303607085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469258180448324202404723 9703887270672486303607085)
            ·
              refine ⟨3638957726502182363852657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9703887270672486303607085 3638957726502182363852657)
              ·
                refine ⟨2729218294876636772889493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638957726502182363852657 2729218294876636772889493)
                ·
                  refine ⟨127932107572342348729195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2729218294876636772889493 127932107572342348729195)
                  ·
                    rfl

theorem cell23_2242322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_2242322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242322 prefixEnd_2242322 := by exact prefixLift 2242322
  have htrace : WordTrace (prefixWord ++ tailWord_2242322) baseStart_2242322 baseEnd_2242322 := by
    simpa [prefixWord, tailWord_2242322, baseEnd_2242322] using wordTrace_append hprefix tailTrace_2242322
  have hstable : (prefixWord ++ tailWord_2242322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242322).length < 2 ^ (prefixWord ++ tailWord_2242322).sum := by decide
  have hdescent : baseEnd_2242322 < baseStart_2242322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242332 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2242332 : Nat := 118140960795 + 2242332 * 2 ^ 59
def prefixEnd_2242332 : Nat := 4983230072969 + 3 ^ 40 * 2242332 * 2
def baseEnd_2242332 : Nat := 1151394102957626099437709

theorem tailTrace_2242332 : CollatzResearch.WordTrace tailWord_2242332 prefixEnd_2242332 1151394102957626099437709 := by
  unfold tailWord_2242332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40892283456210799330860625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54523044608281065774480833 40892283456210799330860625)
  ·
    refine ⟨30669212592158099498145469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40892283456210799330860625 30669212592158099498145469)
    ·
      refine ⟨11500954722059287311804551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30669212592158099498145469 11500954722059287311804551)
      ·
        refine ⟨17251432083088930967706827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11500954722059287311804551 17251432083088930967706827)
        ·
          refine ⟨25877148124633396451560241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17251432083088930967706827 25877148124633396451560241)
          ·
            refine ⟨19407861093475047338670181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25877148124633396451560241 19407861093475047338670181)
            ·
              refine ⟨3638973955026571376000659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19407861093475047338670181 3638973955026571376000659)
              ·
                refine ⟨5458460932539857064000989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638973955026571376000659 5458460932539857064000989)
                ·
                  refine ⟨2046922849702446399000371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5458460932539857064000989 2046922849702446399000371)
                  ·
                    refine ⟨3070384274553669598500557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046922849702446399000371 3070384274553669598500557)
                    ·
                      refine ⟨1151394102957626099437709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070384274553669598500557 1151394102957626099437709)
                      ·
                        rfl

theorem cell23_2242332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2242332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242332 prefixEnd_2242332 := by exact prefixLift 2242332
  have htrace : WordTrace (prefixWord ++ tailWord_2242332) baseStart_2242332 baseEnd_2242332 := by
    simpa [prefixWord, tailWord_2242332, baseEnd_2242332] using wordTrace_append hprefix tailTrace_2242332
  have hstable : (prefixWord ++ tailWord_2242332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242332).length < 2 ^ (prefixWord ++ tailWord_2242332).sum := by decide
  have hdescent : baseEnd_2242332 < baseStart_2242332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242366 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_2242366 : Nat := 118140960795 + 2242366 * 2 ^ 59
def prefixEnd_2242366 : Nat := 4983230072969 + 3 ^ 40 * 2242366 * 2
def baseEnd_2242366 : Nat := 1151411561299878966412553

theorem tailTrace_2242366 : CollatzResearch.WordTrace tailWord_2242366 prefixEnd_2242366 1151411561299878966412553 := by
  unfold tailWord_2242366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223225874287302808557369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54523871329532281645639301 10223225874287302808557369)
  ·
    refine ⟨7667419405715477106418027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10223225874287302808557369 7667419405715477106418027)
    ·
      refine ⟨11501129108573215659627041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7667419405715477106418027 11501129108573215659627041)
      ·
        refine ⟨8625846831429911744720281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11501129108573215659627041 8625846831429911744720281)
        ·
          refine ⟨6469385123572433808540211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625846831429911744720281 6469385123572433808540211)
          ·
            refine ⟨9704077685358650712810317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469385123572433808540211 9704077685358650712810317)
            ·
              refine ⟨3639029132009494017303869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9704077685358650712810317 3639029132009494017303869)
              ·
                refine ⟨1364635924503560256488951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3639029132009494017303869 1364635924503560256488951)
                ·
                  refine ⟨2046953886755340384733427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364635924503560256488951 2046953886755340384733427)
                  ·
                    refine ⟨3070430830133010577100141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2046953886755340384733427 3070430830133010577100141)
                    ·
                      refine ⟨1151411561299878966412553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070430830133010577100141 1151411561299878966412553)
                      ·
                        rfl

theorem cell23_2242366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_2242366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242366 prefixEnd_2242366 := by exact prefixLift 2242366
  have htrace : WordTrace (prefixWord ++ tailWord_2242366) baseStart_2242366 baseEnd_2242366 := by
    simpa [prefixWord, tailWord_2242366, baseEnd_2242366] using wordTrace_append hprefix tailTrace_2242366
  have hstable : (prefixWord ++ tailWord_2242366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242366).length < 2 ^ (prefixWord ++ tailWord_2242366).sum := by decide
  have hdescent : baseEnd_2242366 < baseStart_2242366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242389 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2242389 : Nat := 118140960795 + 2242389 * 2 ^ 59
def prefixEnd_2242389 : Nat := 4983230072969 + 3 ^ 40 * 2242389 * 2
def baseEnd_2242389 : Nat := 1151423371354932376424947

theorem tailTrace_2242389 : CollatzResearch.WordTrace tailWord_2242389 prefixEnd_2242389 1151423371354932376424947 := by
  unfold tailWord_2242389
  simp only [CollatzResearch.WordTrace]
  refine ⟨81786645873215097396546221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54524430582143398264364147 81786645873215097396546221)
  ·
    refine ⟨30669992202455661523704833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81786645873215097396546221 30669992202455661523704833)
    ·
      refine ⟨23002494151841746142778625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30669992202455661523704833 23002494151841746142778625)
      ·
        refine ⟨17251870613881309607083969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23002494151841746142778625 17251870613881309607083969)
        ·
          refine ⟨12938902960410982205312977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17251870613881309607083969 12938902960410982205312977)
          ·
            refine ⟨9704177220308236653984733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12938902960410982205312977 9704177220308236653984733)
            ·
              refine ⟨3639066457615588745244275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9704177220308236653984733 3639066457615588745244275)
              ·
                refine ⟨5458599686423383117866413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639066457615588745244275 5458599686423383117866413)
                ·
                  refine ⟨2046974882408768669199905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5458599686423383117866413 2046974882408768669199905)
                  ·
                    refine ⟨1535231161806576501899929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2046974882408768669199905 1535231161806576501899929)
                    ·
                      refine ⟨1151423371354932376424947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535231161806576501899929 1151423371354932376424947)
                      ·
                        rfl

theorem cell23_2242389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2242389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242389 prefixEnd_2242389 := by exact prefixLift 2242389
  have htrace : WordTrace (prefixWord ++ tailWord_2242389) baseStart_2242389 baseEnd_2242389 := by
    simpa [prefixWord, tailWord_2242389, baseEnd_2242389] using wordTrace_append hprefix tailTrace_2242389
  have hstable : (prefixWord ++ tailWord_2242389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242389).length < 2 ^ (prefixWord ++ tailWord_2242389).sum := by decide
  have hdescent : baseEnd_2242389 < baseStart_2242389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242399 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 2, 4]
def baseStart_2242399 : Nat := 118140960795 + 2242399 * 2 ^ 59
def prefixEnd_2242399 : Nat := 4983230072969 + 3 ^ 40 * 2242399 * 2
def baseEnd_2242399 : Nat := 383809502053825779099967

theorem tailTrace_2242399 : CollatzResearch.WordTrace tailWord_2242399 prefixEnd_2242399 383809502053825779099967 := by
  unfold tailWord_2242399
  simp only [CollatzResearch.WordTrace]
  refine ⟨81787010603178869104410251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54524673735452579402940167 81787010603178869104410251)
  ·
    refine ⟨122680515904768303656615377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81787010603178869104410251 122680515904768303656615377)
    ·
      refine ⟨92010386928576227742461533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122680515904768303656615377 92010386928576227742461533)
      ·
        refine ⟨34503895098216085403423075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92010386928576227742461533 34503895098216085403423075)
        ·
          refine ⟨51755842647324128105134613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34503895098216085403423075 51755842647324128105134613)
          ·
            refine ⟨2426055124093318504928185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51755842647324128105134613 2426055124093318504928185)
            ·
              refine ⟨1819541343069988878696139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426055124093318504928185 1819541343069988878696139)
              ·
                refine ⟨2729312014604983318044209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819541343069988878696139 2729312014604983318044209)
                ·
                  refine ⟨2046984010953737488533157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729312014604983318044209 2046984010953737488533157)
                  ·
                    refine ⟨383809502053825779099967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046984010953737488533157 383809502053825779099967)
                    ·
                      rfl

theorem cell23_2242399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_2242399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242399 prefixEnd_2242399 := by exact prefixLift 2242399
  have htrace : WordTrace (prefixWord ++ tailWord_2242399) baseStart_2242399 baseEnd_2242399 := by
    simpa [prefixWord, tailWord_2242399, baseEnd_2242399] using wordTrace_append hprefix tailTrace_2242399
  have hstable : (prefixWord ++ tailWord_2242399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242399).length < 2 ^ (prefixWord ++ tailWord_2242399).sum := by decide
  have hdescent : baseEnd_2242399 < baseStart_2242399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242405 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2242405 : Nat := 118140960795 + 2242405 * 2 ^ 59
def prefixEnd_2242405 : Nat := 4983230072969 + 3 ^ 40 * 2242405 * 2
def baseEnd_2242405 : Nat := 1151431587045404313824873

theorem tailTrace_2242405 : CollatzResearch.WordTrace tailWord_2242405 prefixEnd_2242405 1151431587045404313824873 := by
  unfold tailWord_2242405
  simp only [CollatzResearch.WordTrace]
  refine ⟨81787229441157132129128669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54524819627438088086085779 81787229441157132129128669)
  ·
    refine ⟨30670211040433924548423251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81787229441157132129128669 30670211040433924548423251)
    ·
      refine ⟨46005316560650886822634877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30670211040433924548423251 46005316560650886822634877)
      ·
        refine ⟨17251993710244082558488079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46005316560650886822634877 17251993710244082558488079)
        ·
          refine ⟨25877990565366123837732119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17251993710244082558488079 25877990565366123837732119)
          ·
            refine ⟨38816985848049185756598179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25877990565366123837732119 38816985848049185756598179)
            ·
              refine ⟨58225478772073778634897269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38816985848049185756598179 58225478772073778634897269)
              ·
                refine ⟨5458638634881916747021619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58225478772073778634897269 5458638634881916747021619)
                ·
                  refine ⟨8187957952322875120532429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5458638634881916747021619 8187957952322875120532429)
                  ·
                    refine ⟨3070484232121078170199661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8187957952322875120532429 3070484232121078170199661)
                    ·
                      refine ⟨1151431587045404313824873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070484232121078170199661 1151431587045404313824873)
                      ·
                        rfl

theorem cell23_2242405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2242405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242405 prefixEnd_2242405 := by exact prefixLift 2242405
  have htrace : WordTrace (prefixWord ++ tailWord_2242405) baseStart_2242405 baseEnd_2242405 := by
    simpa [prefixWord, tailWord_2242405, baseEnd_2242405] using wordTrace_append hprefix tailTrace_2242405
  have hstable : (prefixWord ++ tailWord_2242405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242405).length < 2 ^ (prefixWord ++ tailWord_2242405).sum := by decide
  have hdescent : baseEnd_2242405 < baseStart_2242405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242440 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_2242440 : Nat := 118140960795 + 2242440 * 2 ^ 59
def prefixEnd_2242440 : Nat := 4983230072969 + 3 ^ 40 * 2242440 * 2
def baseEnd_2242440 : Nat := 1151449558868311676887213

theorem tailTrace_2242440 : CollatzResearch.WordTrace tailWord_2242440 prefixEnd_2242440 1151449558868311676887213 := by
  unfold tailWord_2242440
  simp only [CollatzResearch.WordTrace]
  refine ⟨40894252998015166553326387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54525670664020222071101849 40894252998015166553326387)
  ·
    refine ⟨61341379497022749829989581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40894252998015166553326387 61341379497022749829989581)
    ·
      refine ⟨23003017311383531186246093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61341379497022749829989581 23003017311383531186246093)
      ·
        refine ⟨8626131491768824194842285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23003017311383531186246093 8626131491768824194842285)
        ·
          refine ⟨3234799309413309073065857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8626131491768824194842285 3234799309413309073065857)
          ·
            refine ⟨2426099482059981804799393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234799309413309073065857 2426099482059981804799393)
            ·
              refine ⟨1819574611544986353599545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426099482059981804799393 1819574611544986353599545)
              ·
                refine ⟨1364680958658739765199659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1819574611544986353599545 1364680958658739765199659)
                ·
                  refine ⟨2047021437988109647799489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364680958658739765199659 2047021437988109647799489)
                  ·
                    refine ⟨1535266078491082235849617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2047021437988109647799489 1535266078491082235849617)
                    ·
                      refine ⟨1151449558868311676887213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535266078491082235849617 1151449558868311676887213)
                      ·
                        rfl

theorem cell23_2242440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_2242440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242440 prefixEnd_2242440 := by exact prefixLift 2242440
  have htrace : WordTrace (prefixWord ++ tailWord_2242440) baseStart_2242440 baseEnd_2242440 := by
    simpa [prefixWord, tailWord_2242440, baseEnd_2242440] using wordTrace_append hprefix tailTrace_2242440
  have hstable : (prefixWord ++ tailWord_2242440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242440).length < 2 ^ (prefixWord ++ tailWord_2242440).sum := by decide
  have hdescent : baseEnd_2242440 < baseStart_2242440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242448 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2242448 : Nat := 118140960795 + 2242448 * 2 ^ 59
def prefixEnd_2242448 : Nat := 4983230072969 + 3 ^ 40 * 2242448 * 2
def baseEnd_2242448 : Nat := 1151453666713547645587175

theorem tailTrace_2242448 : CollatzResearch.WordTrace tailWord_2242448 prefixEnd_2242448 1151453666713547645587175 := by
  unfold tailWord_2242448
  simp only [CollatzResearch.WordTrace]
  refine ⟨40894398890000675236471999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54525865186667566981962665 40894398890000675236471999)
  ·
    refine ⟨61341598335001012854707999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40894398890000675236471999 61341598335001012854707999)
    ·
      refine ⟨92012397502501519282061999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61341598335001012854707999 92012397502501519282061999)
      ·
        refine ⟨138018596253752278923092999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92012397502501519282061999 138018596253752278923092999)
        ·
          refine ⟨207027894380628418384639499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138018596253752278923092999 207027894380628418384639499)
          ·
            refine ⟨310541841570942627576959249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207027894380628418384639499 310541841570942627576959249)
            ·
              refine ⟨232906381178206970682719437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310541841570942627576959249 232906381178206970682719437)
              ·
                refine ⟨87339892941827614006019789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232906381178206970682719437 87339892941827614006019789)
                ·
                  refine ⟨32752459853185355252257421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87339892941827614006019789 32752459853185355252257421)
                  ·
                    refine ⟨12282172444944508219596533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32752459853185355252257421 12282172444944508219596533)
                    ·
                      refine ⟨1151453666713547645587175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12282172444944508219596533 1151453666713547645587175)
                      ·
                        rfl

theorem cell23_2242448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2242448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242448 prefixEnd_2242448 := by exact prefixLift 2242448
  have htrace : WordTrace (prefixWord ++ tailWord_2242448) baseStart_2242448 baseEnd_2242448 := by
    simpa [prefixWord, tailWord_2242448, baseEnd_2242448] using wordTrace_append hprefix tailTrace_2242448
  have hstable : (prefixWord ++ tailWord_2242448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242448).length < 2 ^ (prefixWord ++ tailWord_2242448).sum := by decide
  have hdescent : baseEnd_2242448 < baseStart_2242448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242455 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 6]
def baseStart_2242455 : Nat := 118140960795 + 2242455 * 2 ^ 59
def prefixEnd_2242455 : Nat := 4983230072969 + 3 ^ 40 * 2242455 * 2
def baseEnd_2242455 : Nat := 383819087026043039399881

theorem tailTrace_2242455 : CollatzResearch.WordTrace tailWord_2242455 prefixEnd_2242455 383819087026043039399881 := by
  unfold tailWord_2242455
  simp only [CollatzResearch.WordTrace]
  refine ⟨81789053090975990668448819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54526035393983993778965879 81789053090975990668448819)
  ·
    refine ⟨122683579636463986002673229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81789053090975990668448819 122683579636463986002673229)
    ·
      refine ⟨46006342363673994751002461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122683579636463986002673229 46006342363673994751002461)
      ·
        refine ⟨17252378386377748031625923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46006342363673994751002461 17252378386377748031625923)
        ·
          refine ⟨25878567579566622047438885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17252378386377748031625923 25878567579566622047438885)
          ·
            refine ⟨4852231421168741633894791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25878567579566622047438885 4852231421168741633894791)
            ·
              refine ⟨7278347131753112450842187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852231421168741633894791 7278347131753112450842187)
              ·
                refine ⟨10917520697629668676263281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7278347131753112450842187 10917520697629668676263281)
                ·
                  refine ⟨8188140523222251507197461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10917520697629668676263281 8188140523222251507197461)
                  ·
                    refine ⟨383819087026043039399881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8188140523222251507197461 383819087026043039399881)
                    ·
                      rfl

theorem cell23_2242455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_2242455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242455 prefixEnd_2242455 := by exact prefixLift 2242455
  have htrace : WordTrace (prefixWord ++ tailWord_2242455) baseStart_2242455 baseEnd_2242455 := by
    simpa [prefixWord, tailWord_2242455, baseEnd_2242455] using wordTrace_append hprefix tailTrace_2242455
  have hstable : (prefixWord ++ tailWord_2242455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242455).length < 2 ^ (prefixWord ++ tailWord_2242455).sum := by decide
  have hdescent : baseEnd_2242455 < baseStart_2242455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242495 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2242495 : Nat := 118140960795 + 2242495 * 2 ^ 59
def prefixEnd_2242495 : Nat := 4983230072969 + 3 ^ 40 * 2242495 * 2
def baseEnd_2242495 : Nat := 1151477800304308961699459

theorem tailTrace_2242495 : CollatzResearch.WordTrace tailWord_2242495 prefixEnd_2242495 1151477800304308961699459 := by
  unfold tailWord_2242495
  simp only [CollatzResearch.WordTrace]
  refine ⟨81790512010831077499904939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54527008007220718333269959 81790512010831077499904939)
  ·
    refine ⟨122685768016246616249857409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81790512010831077499904939 122685768016246616249857409)
    ·
      refine ⟨92014326012184962187393057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122685768016246616249857409 92014326012184962187393057)
      ·
        refine ⟨69010744509138721640544793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92014326012184962187393057 69010744509138721640544793)
        ·
          refine ⟨51758058381854041230408595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69010744509138721640544793 51758058381854041230408595)
          ·
            refine ⟨77637087572781061845612893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51758058381854041230408595 77637087572781061845612893)
            ·
              refine ⟨29113907839792898192104835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77637087572781061845612893 29113907839792898192104835)
              ·
                refine ⟨43670861759689347288157253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29113907839792898192104835 43670861759689347288157253)
                ·
                  refine ⟨8188286579941752616529485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43670861759689347288157253 8188286579941752616529485)
                  ·
                    refine ⟨3070607467478157231198557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8188286579941752616529485 3070607467478157231198557)
                    ·
                      refine ⟨1151477800304308961699459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070607467478157231198557 1151477800304308961699459)
                      ·
                        rfl

theorem cell23_2242495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2242495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242495 prefixEnd_2242495 := by exact prefixLift 2242495
  have htrace : WordTrace (prefixWord ++ tailWord_2242495) baseStart_2242495 baseEnd_2242495 := by
    simpa [prefixWord, tailWord_2242495, baseEnd_2242495] using wordTrace_append hprefix tailTrace_2242495
  have hstable : (prefixWord ++ tailWord_2242495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242495).length < 2 ^ (prefixWord ++ tailWord_2242495).sum := by decide
  have hdescent : baseEnd_2242495 < baseStart_2242495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242552 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_2242552 : Nat := 118140960795 + 2242552 * 2 ^ 59
def prefixEnd_2242552 : Nat := 4983230072969 + 3 ^ 40 * 2242552 * 2
def baseEnd_2242552 : Nat := 1151507068701615238686697

theorem tailTrace_2242552 : CollatzResearch.WordTrace tailWord_2242552 prefixEnd_2242552 1151507068701615238686697 := by
  unfold tailWord_2242552
  simp only [CollatzResearch.WordTrace]
  refine ⟨40896295485812288117364955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54528393981083050823153273 40896295485812288117364955)
  ·
    refine ⟨61344443228718432176047433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40896295485812288117364955 61344443228718432176047433)
    ·
      refine ⟨46008332421538824132035575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61344443228718432176047433 46008332421538824132035575)
      ·
        refine ⟨69012498632308236198053363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46008332421538824132035575 69012498632308236198053363)
        ·
          refine ⟨103518747948462354297080045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69012498632308236198053363 103518747948462354297080045)
          ·
            refine ⟨38819530480673382861405017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103518747948462354297080045 38819530480673382861405017)
            ·
              refine ⟨29114647860505037146053763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38819530480673382861405017 29114647860505037146053763)
              ·
                refine ⟨43671971790757555719080645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29114647860505037146053763 43671971790757555719080645)
                ·
                  refine ⟨8188494710767041697327621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43671971790757555719080645 8188494710767041697327621)
                  ·
                    refine ⟨1535342758268820318248929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8188494710767041697327621 1535342758268820318248929)
                    ·
                      refine ⟨1151507068701615238686697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535342758268820318248929 1151507068701615238686697)
                      ·
                        rfl

theorem cell23_2242552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_2242552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242552 prefixEnd_2242552 := by exact prefixLift 2242552
  have htrace : WordTrace (prefixWord ++ tailWord_2242552) baseStart_2242552 baseEnd_2242552 := by
    simpa [prefixWord, tailWord_2242552, baseEnd_2242552] using wordTrace_append hprefix tailTrace_2242552
  have hstable : (prefixWord ++ tailWord_2242552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242552).length < 2 ^ (prefixWord ++ tailWord_2242552).sum := by decide
  have hdescent : baseEnd_2242552 < baseStart_2242552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242572 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2242572 : Nat := 118140960795 + 2242572 * 2 ^ 59
def prefixEnd_2242572 : Nat := 4983230072969 + 3 ^ 40 * 2242572 * 2
def baseEnd_2242572 : Nat := 1151517338314705160436605

theorem tailTrace_2242572 : CollatzResearch.WordTrace tailWord_2242572 prefixEnd_2242572 1151517338314705160436605 := by
  unfold tailWord_2242572
  simp only [CollatzResearch.WordTrace]
  refine ⟨40896660215776059825228985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54528880287701413100305313 40896660215776059825228985)
  ·
    refine ⟨30672495161832044868921739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40896660215776059825228985 30672495161832044868921739)
    ·
      refine ⟨46008742742748067303382609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30672495161832044868921739 46008742742748067303382609)
      ·
        refine ⟨34506557057061050477536957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46008742742748067303382609 34506557057061050477536957)
        ·
          refine ⟨12939958896397893929076359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34506557057061050477536957 12939958896397893929076359)
          ·
            refine ⟨19409938344596840893614539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12939958896397893929076359 19409938344596840893614539)
            ·
              refine ⟨29114907516895261340421809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19409938344596840893614539 29114907516895261340421809)
              ·
                refine ⟨21836180637671446005316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29114907516895261340421809 21836180637671446005316357)
                ·
                  refine ⟨4094283869563396125996817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21836180637671446005316357 4094283869563396125996817)
                  ·
                    refine ⟨3070712902172547094497613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094283869563396125996817 3070712902172547094497613)
                    ·
                      refine ⟨1151517338314705160436605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070712902172547094497613 1151517338314705160436605)
                      ·
                        rfl

theorem cell23_2242572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2242572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242572 prefixEnd_2242572 := by exact prefixLift 2242572
  have htrace : WordTrace (prefixWord ++ tailWord_2242572) baseStart_2242572 baseEnd_2242572 := by
    simpa [prefixWord, tailWord_2242572, baseEnd_2242572] using wordTrace_append hprefix tailTrace_2242572
  have hstable : (prefixWord ++ tailWord_2242572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242572).length < 2 ^ (prefixWord ++ tailWord_2242572).sum := by decide
  have hdescent : baseEnd_2242572 < baseStart_2242572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242589 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2242589 : Nat := 118140960795 + 2242589 * 2 ^ 59
def prefixEnd_2242589 : Nat := 4983230072969 + 3 ^ 40 * 2242589 * 2
def baseEnd_2242589 : Nat := 1151526067485831593924027

theorem tailTrace_2242589 : CollatzResearch.WordTrace tailWord_2242589 prefixEnd_2242589 1151526067485831593924027 := by
  unfold tailWord_2242589
  simp only [CollatzResearch.WordTrace]
  refine ⟨81793940472490531553826821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54529293648327021035884547 81793940472490531553826821)
  ·
    refine ⟨15336363838591974666342529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81793940472490531553826821 15336363838591974666342529)
    ·
      refine ⟨11502272878943980999756897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15336363838591974666342529 11502272878943980999756897)
      ·
        refine ⟨8626704659207985749817673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11502272878943980999756897 8626704659207985749817673)
        ·
          refine ⟨6470028494405989312363255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8626704659207985749817673 6470028494405989312363255)
          ·
            refine ⟨9705042741608983968544883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470028494405989312363255 9705042741608983968544883)
            ·
              refine ⟨14557564112413475952817325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705042741608983968544883 14557564112413475952817325)
              ·
                refine ⟨5459086542155053482306497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14557564112413475952817325 5459086542155053482306497)
                ·
                  refine ⟨4094314906616290111729873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5459086542155053482306497 4094314906616290111729873)
                  ·
                    refine ⟨3070736179962217583797405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094314906616290111729873 3070736179962217583797405)
                    ·
                      refine ⟨1151526067485831593924027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070736179962217583797405 1151526067485831593924027)
                      ·
                        rfl

theorem cell23_2242589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2242589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242589 prefixEnd_2242589 := by exact prefixLift 2242589
  have htrace : WordTrace (prefixWord ++ tailWord_2242589) baseStart_2242589 baseEnd_2242589 := by
    simpa [prefixWord, tailWord_2242589, baseEnd_2242589] using wordTrace_append hprefix tailTrace_2242589
  have hstable : (prefixWord ++ tailWord_2242589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242589).length < 2 ^ (prefixWord ++ tailWord_2242589).sum := by decide
  have hdescent : baseEnd_2242589 < baseStart_2242589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242635 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 6]
def baseStart_2242635 : Nat := 118140960795 + 2242635 * 2 ^ 59
def prefixEnd_2242635 : Nat := 4983230072969 + 3 ^ 40 * 2242635 * 2
def baseEnd_2242635 : Nat := 383849895865312804649605

theorem tailTrace_2242635 : CollatzResearch.WordTrace tailWord_2242635 prefixEnd_2242635 383849895865312804649605 := by
  unfold tailWord_2242635
  simp only [CollatzResearch.WordTrace]
  refine ⟨81795618230323881410001359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54530412153549254273334239 81795618230323881410001359)
  ·
    refine ⟨122693427345485822115002039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81795618230323881410001359 122693427345485822115002039)
    ·
      refine ⟨184040141018228733172503059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122693427345485822115002039 184040141018228733172503059)
      ·
        refine ⟨276060211527343099758754589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184040141018228733172503059 276060211527343099758754589)
        ·
          refine ⟨103522579322753662409532971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276060211527343099758754589 103522579322753662409532971)
          ·
            refine ⟨155283868984130493614299457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103522579322753662409532971 155283868984130493614299457)
            ·
              refine ⟨116462901738097870210724593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155283868984130493614299457 116462901738097870210724593)
              ·
                refine ⟨87347176303573402658043445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116462901738097870210724593 87347176303573402658043445)
                ·
                  refine ⟨8188797778460006499191573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87347176303573402658043445 8188797778460006499191573)
                  ·
                    refine ⟨383849895865312804649605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8188797778460006499191573 383849895865312804649605)
                    ·
                      rfl

theorem cell23_2242635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_2242635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242635 prefixEnd_2242635 := by exact prefixLift 2242635
  have htrace : WordTrace (prefixWord ++ tailWord_2242635) baseStart_2242635 baseEnd_2242635 := by
    simpa [prefixWord, tailWord_2242635, baseEnd_2242635] using wordTrace_append hprefix tailTrace_2242635
  have hstable : (prefixWord ++ tailWord_2242635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242635).length < 2 ^ (prefixWord ++ tailWord_2242635).sum := by decide
  have hdescent : baseEnd_2242635 < baseStart_2242635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242656 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_2242656 : Nat := 118140960795 + 2242656 * 2 ^ 59
def prefixEnd_2242656 : Nat := 4983230072969 + 3 ^ 40 * 2242656 * 2
def baseEnd_2242656 : Nat := 383853490229894277262073

theorem tailTrace_2242656 : CollatzResearch.WordTrace tailWord_2242656 prefixEnd_2242656 383853490229894277262073 := by
  unfold tailWord_2242656
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898192081623900998257911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54530922775498534664343881 40898192081623900998257911)
  ·
    refine ⟨61347288122435851497386867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40898192081623900998257911 61347288122435851497386867)
    ·
      refine ⟨92020932183653777246080301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61347288122435851497386867 92020932183653777246080301)
      ·
        refine ⟨34507849568870166467280113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92020932183653777246080301 34507849568870166467280113)
        ·
          refine ⟨25880887176652624850460085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34507849568870166467280113 25880887176652624850460085)
          ·
            refine ⟨2426333172811183579730633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25880887176652624850460085 2426333172811183579730633)
            ·
              refine ⟨1819749879608387684797975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426333172811183579730633 1819749879608387684797975)
              ·
                refine ⟨2729624819412581527196963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819749879608387684797975 2729624819412581527196963)
                ·
                  refine ⟨4094437229118872290795445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729624819412581527196963 4094437229118872290795445)
                  ·
                    refine ⟨383853490229894277262073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4094437229118872290795445 383853490229894277262073)
                    ·
                      rfl

theorem cell23_2242656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_2242656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242656 prefixEnd_2242656 := by exact prefixLift 2242656
  have htrace : WordTrace (prefixWord ++ tailWord_2242656) baseStart_2242656 baseEnd_2242656 := by
    simpa [prefixWord, tailWord_2242656, baseEnd_2242656] using wordTrace_append hprefix tailTrace_2242656
  have hstable : (prefixWord ++ tailWord_2242656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242656).length < 2 ^ (prefixWord ++ tailWord_2242656).sum := by decide
  have hdescent : baseEnd_2242656 < baseStart_2242656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242665 : List Nat := [1, 2, 1, 1, 1, 5, 12]
def baseStart_2242665 : Nat := 118140960795 + 2242665 * 2 ^ 59
def prefixEnd_2242665 : Nat := 4983230072969 + 3 ^ 40 * 2242665 * 2
def baseEnd_2242665 : Nat := 14216852987846583908317

theorem tailTrace_2242665 : CollatzResearch.WordTrace tailWord_2242665 prefixEnd_2242665 14216852987846583908317 := by
  unfold tailWord_2242665
  simp only [CollatzResearch.WordTrace]
  refine ⟨81796712420215196533593449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54531141613476797689062299 81796712420215196533593449)
  ·
    refine ⟨61347534315161397400195087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81796712420215196533593449 61347534315161397400195087)
    ·
      refine ⟨92021301472742096100292631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61347534315161397400195087 92021301472742096100292631)
      ·
        refine ⟨138031952209113144150438947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92021301472742096100292631 138031952209113144150438947)
        ·
          refine ⟨207047928313669716225658421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138031952209113144150438947 207047928313669716225658421)
          ·
            refine ⟨19410743279406535896155477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207047928313669716225658421 19410743279406535896155477)
            ·
              refine ⟨14216852987846583908317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19410743279406535896155477 14216852987846583908317)
              ·
                rfl

theorem cell23_2242665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 12].length) (baseStart_2242665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242665 prefixEnd_2242665 := by exact prefixLift 2242665
  have htrace : WordTrace (prefixWord ++ tailWord_2242665) baseStart_2242665 baseEnd_2242665 := by
    simpa [prefixWord, tailWord_2242665, baseEnd_2242665] using wordTrace_append hprefix tailTrace_2242665
  have hstable : (prefixWord ++ tailWord_2242665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242665).length < 2 ^ (prefixWord ++ tailWord_2242665).sum := by decide
  have hdescent : baseEnd_2242665 < baseStart_2242665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242669 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2242669 : Nat := 118140960795 + 2242669 * 2 ^ 59
def prefixEnd_2242669 : Nat := 4983230072969 + 3 ^ 40 * 2242669 * 2
def baseEnd_2242669 : Nat := 383855715312730426974553

theorem tailTrace_2242669 : CollatzResearch.WordTrace tailWord_2242669 prefixEnd_2242669 383855715312730426974553 := by
  unfold tailWord_2242669
  simp only [CollatzResearch.WordTrace]
  refine ⟨81796858312200705216739061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54531238874800470144492707 81796858312200705216739061)
  ·
    refine ⟨7668455466768816114069287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81796858312200705216739061 7668455466768816114069287)
    ·
      refine ⟨11502683200153224171103931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668455466768816114069287 11502683200153224171103931)
      ·
        refine ⟨17254024800229836256655897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11502683200153224171103931 17254024800229836256655897)
        ·
          refine ⟨12940518600172377192491923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17254024800229836256655897 12940518600172377192491923)
          ·
            refine ⟨19410777900258565788737885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12940518600172377192491923 19410777900258565788737885)
            ·
              refine ⟨7279041712596962170776707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19410777900258565788737885 7279041712596962170776707)
              ·
                refine ⟨10918562568895443256165061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7279041712596962170776707 10918562568895443256165061)
                ·
                  refine ⟨2047230481667895610530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10918562568895443256165061 2047230481667895610530949)
                  ·
                    refine ⟨383855715312730426974553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047230481667895610530949 383855715312730426974553)
                    ·
                      rfl

theorem cell23_2242669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2242669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242669 prefixEnd_2242669 := by exact prefixLift 2242669
  have htrace : WordTrace (prefixWord ++ tailWord_2242669) baseStart_2242669 baseEnd_2242669 := by
    simpa [prefixWord, tailWord_2242669, baseEnd_2242669] using wordTrace_append hprefix tailTrace_2242669
  have hstable : (prefixWord ++ tailWord_2242669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242669).length < 2 ^ (prefixWord ++ tailWord_2242669).sum := by decide
  have hdescent : baseEnd_2242669 < baseStart_2242669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242689 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2242689 : Nat := 118140960795 + 2242689 * 2 ^ 59
def prefixEnd_2242689 : Nat := 4983230072969 + 3 ^ 40 * 2242689 * 2
def baseEnd_2242689 : Nat := 1151577415551281202673567

theorem tailTrace_2242689 : CollatzResearch.WordTrace tailWord_2242689 prefixEnd_2242689 1151577415551281202673567 := by
  unfold tailWord_2242689
  simp only [CollatzResearch.WordTrace]
  refine ⟨81797587772128248632467121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54531725181418832421644747 81797587772128248632467121)
  ·
    refine ⟨61348190829096186474350341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81797587772128248632467121 61348190829096186474350341)
    ·
      refine ⟨11502785780455534963940689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61348190829096186474350341 11502785780455534963940689)
      ·
        refine ⟨8627089335341651222955517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11502785780455534963940689 8627089335341651222955517)
        ·
          refine ⟨3235158500753119208608319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8627089335341651222955517 3235158500753119208608319)
          ·
            refine ⟨4852737751129678812912479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235158500753119208608319 4852737751129678812912479)
            ·
              refine ⟨7279106626694518219368719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852737751129678812912479 7279106626694518219368719)
              ·
                refine ⟨10918659940041777329053079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7279106626694518219368719 10918659940041777329053079)
                ·
                  refine ⟨16377989910062665993579619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10918659940041777329053079 16377989910062665993579619)
                  ·
                    refine ⟨24566984865093998990369429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16377989910062665993579619 24566984865093998990369429)
                    ·
                      refine ⟨1151577415551281202673567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24566984865093998990369429 1151577415551281202673567)
                      ·
                        rfl

theorem cell23_2242689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2242689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242689 prefixEnd_2242689 := by exact prefixLift 2242689
  have htrace : WordTrace (prefixWord ++ tailWord_2242689) baseStart_2242689 baseEnd_2242689 := by
    simpa [prefixWord, tailWord_2242689, baseEnd_2242689] using wordTrace_append hprefix tailTrace_2242689
  have hstable : (prefixWord ++ tailWord_2242689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242689).length < 2 ^ (prefixWord ++ tailWord_2242689).sum := by decide
  have hdescent : baseEnd_2242689 < baseStart_2242689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242696 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2242696 : Nat := 118140960795 + 2242696 * 2 ^ 59
def prefixEnd_2242696 : Nat := 4983230072969 + 3 ^ 40 * 2242696 * 2
def baseEnd_2242696 : Nat := 1151581009915862675286035

theorem tailTrace_2242696 : CollatzResearch.WordTrace tailWord_2242696 prefixEnd_2242696 1151581009915862675286035 := by
  unfold tailWord_2242696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898921541551444413985971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54531895388735259218647961 40898921541551444413985971)
  ·
    refine ⟨61348382312327166620978957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40898921541551444413985971 61348382312327166620978957)
    ·
      refine ⟨23005643367122687482867109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61348382312327166620978957 23005643367122687482867109)
      ·
        refine ⟨4313558131335503903037583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23005643367122687482867109 4313558131335503903037583)
        ·
          refine ⟨6470337197003255854556375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313558131335503903037583 6470337197003255854556375)
          ·
            refine ⟨9705505795504883781834563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470337197003255854556375 9705505795504883781834563)
            ·
              refine ⟨14558258693257325672751845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705505795504883781834563 14558258693257325672751845)
              ·
                refine ⟨2729673504985748563640971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14558258693257325672751845 2729673504985748563640971)
                ·
                  refine ⟨4094510257478622845461457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729673504985748563640971 4094510257478622845461457)
                  ·
                    refine ⟨3070882693108967134096093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094510257478622845461457 3070882693108967134096093)
                    ·
                      refine ⟨1151581009915862675286035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070882693108967134096093 1151581009915862675286035)
                      ·
                        rfl

theorem cell23_2242696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2242696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242696 prefixEnd_2242696 := by exact prefixLift 2242696
  have htrace : WordTrace (prefixWord ++ tailWord_2242696) baseStart_2242696 baseEnd_2242696 := by
    simpa [prefixWord, tailWord_2242696, baseEnd_2242696] using wordTrace_append hprefix tailTrace_2242696
  have hstable : (prefixWord ++ tailWord_2242696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242696).length < 2 ^ (prefixWord ++ tailWord_2242696).sum := by decide
  have hdescent : baseEnd_2242696 < baseStart_2242696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242709 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_2242709 : Nat := 118140960795 + 2242709 * 2 ^ 59
def prefixEnd_2242709 : Nat := 4983230072969 + 3 ^ 40 * 2242709 * 2
def baseEnd_2242709 : Nat := 1151587685164371124423475

theorem tailTrace_2242709 : CollatzResearch.WordTrace tailWord_2242709 prefixEnd_2242709 1151587685164371124423475 := by
  unfold tailWord_2242709
  simp only [CollatzResearch.WordTrace]
  refine ⟨81798317232055792048195181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54532211488037194698796787 81798317232055792048195181)
  ·
    refine ⟨30674368962020922018073193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81798317232055792048195181 30674368962020922018073193)
    ·
      refine ⟨23005776721515691513554895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30674368962020922018073193 23005776721515691513554895)
      ·
        refine ⟨34508665082273537270332343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23005776721515691513554895 34508665082273537270332343)
        ·
          refine ⟨51762997623410305905498515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34508665082273537270332343 51762997623410305905498515)
          ·
            refine ⟨77644496435115458858247773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51762997623410305905498515 77644496435115458858247773)
            ·
              refine ⟨29116686163168297071842915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77644496435115458858247773 29116686163168297071842915)
              ·
                refine ⟨43675029244752445607764373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29116686163168297071842915 43675029244752445607764373)
                ·
                  refine ⟨2047266995847770887863955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43675029244752445607764373 2047266995847770887863955)
                  ·
                    refine ⟨3070900493771656331795933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2047266995847770887863955 3070900493771656331795933)
                    ·
                      refine ⟨1151587685164371124423475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070900493771656331795933 1151587685164371124423475)
                      ·
                        rfl

theorem cell23_2242709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_2242709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242709 prefixEnd_2242709 := by exact prefixLift 2242709
  have htrace : WordTrace (prefixWord ++ tailWord_2242709) baseStart_2242709 baseEnd_2242709 := by
    simpa [prefixWord, tailWord_2242709, baseEnd_2242709] using wordTrace_append hprefix tailTrace_2242709
  have hstable : (prefixWord ++ tailWord_2242709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242709).length < 2 ^ (prefixWord ++ tailWord_2242709).sum := by decide
  have hdescent : baseEnd_2242709 < baseStart_2242709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242727 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2242727 : Nat := 118140960795 + 2242727 * 2 ^ 59
def prefixEnd_2242727 : Nat := 4983230072969 + 3 ^ 40 * 2242727 * 2
def baseEnd_2242727 : Nat := 1151596927816152053998393

theorem tailTrace_2242727 : CollatzResearch.WordTrace tailWord_2242727 prefixEnd_2242727 1151596927816152053998393 := by
  unfold tailWord_2242727
  simp only [CollatzResearch.WordTrace]
  refine ⟨81798973745990581122350435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54532649163993720748233623 81798973745990581122350435)
  ·
    refine ⟨122698460618985871683525653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81798973745990581122350435 122698460618985871683525653)
    ·
      refine ⟨5751490341514962735165265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122698460618985871683525653 5751490341514962735165265)
      ·
        refine ⟨4313617756136222051373949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751490341514962735165265 4313617756136222051373949)
        ·
          refine ⟨1617606658551083269265231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4313617756136222051373949 1617606658551083269265231)
          ·
            refine ⟨2426409987826624903897847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617606658551083269265231 2426409987826624903897847)
            ·
              refine ⟨3639614981739937355846771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426409987826624903897847 3639614981739937355846771)
              ·
                refine ⟨5459422472609906033770157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3639614981739937355846771 5459422472609906033770157)
                ·
                  refine ⟨2047283427228714762663809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5459422472609906033770157 2047283427228714762663809)
                  ·
                    refine ⟨1535462570421536071997857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2047283427228714762663809 1535462570421536071997857)
                    ·
                      refine ⟨1151596927816152053998393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535462570421536071997857 1151596927816152053998393)
                      ·
                        rfl

theorem cell23_2242727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2242727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242727 prefixEnd_2242727 := by exact prefixLift 2242727
  have htrace : WordTrace (prefixWord ++ tailWord_2242727) baseStart_2242727 baseEnd_2242727 := by
    simpa [prefixWord, tailWord_2242727, baseEnd_2242727] using wordTrace_append hprefix tailTrace_2242727
  have hstable : (prefixWord ++ tailWord_2242727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242727).length < 2 ^ (prefixWord ++ tailWord_2242727).sum := by decide
  have hdescent : baseEnd_2242727 < baseStart_2242727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242743 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_2242743 : Nat := 118140960795 + 2242743 * 2 ^ 59
def prefixEnd_2242743 : Nat := 4983230072969 + 3 ^ 40 * 2242743 * 2
def baseEnd_2242743 : Nat := 1151605143506623991398319

theorem tailTrace_2242743 : CollatzResearch.WordTrace tailWord_2242743 prefixEnd_2242743 1151605143506623991398319 := by
  unfold tailWord_2242743
  simp only [CollatzResearch.WordTrace]
  refine ⟨81799557313932615854932883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54533038209288410569955255 81799557313932615854932883)
  ·
    refine ⟨122699335970898923782399325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81799557313932615854932883 122699335970898923782399325)
    ·
      refine ⟨46012250989087096418399747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122699335970898923782399325 46012250989087096418399747)
      ·
        refine ⟨69018376483630644627599621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46012250989087096418399747 69018376483630644627599621)
        ·
          refine ⟨12940945590680745867674929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69018376483630644627599621 12940945590680745867674929)
          ·
            refine ⟨9705709193010559400756197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12940945590680745867674929 9705709193010559400756197)
            ·
              refine ⟨1819820473689479887641787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9705709193010559400756197 1819820473689479887641787)
              ·
                refine ⟨2729730710534219831462681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819820473689479887641787 2729730710534219831462681)
                ·
                  refine ⟨2047298032900664873597011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729730710534219831462681 2047298032900664873597011)
                  ·
                    refine ⟨3070947049350997310395517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2047298032900664873597011 3070947049350997310395517)
                    ·
                      refine ⟨1151605143506623991398319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3070947049350997310395517 1151605143506623991398319)
                      ·
                        rfl

theorem cell23_2242743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_2242743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242743 prefixEnd_2242743 := by exact prefixLift 2242743
  have htrace : WordTrace (prefixWord ++ tailWord_2242743) baseStart_2242743 baseEnd_2242743 := by
    simpa [prefixWord, tailWord_2242743, baseEnd_2242743] using wordTrace_append hprefix tailTrace_2242743
  have hstable : (prefixWord ++ tailWord_2242743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242743).length < 2 ^ (prefixWord ++ tailWord_2242743).sum := by decide
  have hdescent : baseEnd_2242743 < baseStart_2242743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242766 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_2242766 : Nat := 118140960795 + 2242766 * 2 ^ 59
def prefixEnd_2242766 : Nat := 4983230072969 + 3 ^ 40 * 2242766 * 2
def baseEnd_2242766 : Nat := 1151616953561677401410713

theorem tailTrace_2242766 : CollatzResearch.WordTrace tailWord_2242766 prefixEnd_2242766 1151616953561677401410713 := by
  unfold tailWord_2242766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225049524106161347877519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54533597461899527188680101 10225049524106161347877519)
  ·
    refine ⟨15337574286159242021816279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10225049524106161347877519 15337574286159242021816279)
    ·
      refine ⟨23006361429238863032724419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15337574286159242021816279 23006361429238863032724419)
      ·
        refine ⟨34509542143858294549086629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23006361429238863032724419 34509542143858294549086629)
        ·
          refine ⟨6470539151973430227953743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34509542143858294549086629 6470539151973430227953743)
          ·
            refine ⟨9705808727960145341930615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470539151973430227953743 9705808727960145341930615)
            ·
              refine ⟨14558713091940218012895923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705808727960145341930615 14558713091940218012895923)
              ·
                refine ⟨21838069637910327019343885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14558713091940218012895923 21838069637910327019343885)
                ·
                  refine ⟨8189276114216372632253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21838069637910327019343885 8189276114216372632253957)
                  ·
                    refine ⟨1535489271415569868547617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8189276114216372632253957 1535489271415569868547617)
                    ·
                      refine ⟨1151616953561677401410713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535489271415569868547617 1151616953561677401410713)
                      ·
                        rfl

theorem cell23_2242766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_2242766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242766 prefixEnd_2242766 := by exact prefixLift 2242766
  have htrace : WordTrace (prefixWord ++ tailWord_2242766) baseStart_2242766 baseEnd_2242766 := by
    simpa [prefixWord, tailWord_2242766, baseEnd_2242766] using wordTrace_append hprefix tailTrace_2242766
  have hstable : (prefixWord ++ tailWord_2242766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242766).length < 2 ^ (prefixWord ++ tailWord_2242766).sum := by decide
  have hdescent : baseEnd_2242766 < baseStart_2242766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242770 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2242770 : Nat := 118140960795 + 2242770 * 2 ^ 59
def prefixEnd_2242770 : Nat := 4983230072969 + 3 ^ 40 * 2242770 * 2
def baseEnd_2242770 : Nat := 1151619007484295385760695

theorem tailTrace_2242770 : CollatzResearch.WordTrace tailWord_2242770 prefixEnd_2242770 1151619007484295385760695 := by
  unfold tailWord_2242770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450135521208699866541441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54533694723223199644110509 20450135521208699866541441)
  ·
    refine ⟨15337601640906524899906081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20450135521208699866541441 15337601640906524899906081)
    ·
      refine ⟨11503201230679893674929561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15337601640906524899906081 11503201230679893674929561)
      ·
        refine ⟨8627400923009920256197171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11503201230679893674929561 8627400923009920256197171)
        ·
          refine ⟨12941101384514880384295757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8627400923009920256197171 12941101384514880384295757)
          ·
            refine ⟨4852913019193080144110909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12941101384514880384295757 4852913019193080144110909)
            ·
              refine ⟨1819842382197405054041591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4852913019193080144110909 1819842382197405054041591)
              ·
                refine ⟨2729763573296107581062387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819842382197405054041591 2729763573296107581062387)
                ·
                  refine ⟨4094645359944161371593581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2729763573296107581062387 4094645359944161371593581)
                  ·
                    refine ⟨1535492009979060514347593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4094645359944161371593581 1535492009979060514347593)
                    ·
                      refine ⟨1151619007484295385760695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535492009979060514347593 1151619007484295385760695)
                      ·
                        rfl

theorem cell23_2242770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2242770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242770 prefixEnd_2242770 := by exact prefixLift 2242770
  have htrace : WordTrace (prefixWord ++ tailWord_2242770) baseStart_2242770 baseEnd_2242770 := by
    simpa [prefixWord, tailWord_2242770, baseEnd_2242770] using wordTrace_append hprefix tailTrace_2242770
  have hstable : (prefixWord ++ tailWord_2242770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242770).length < 2 ^ (prefixWord ++ tailWord_2242770).sum := by decide
  have hdescent : baseEnd_2242770 < baseStart_2242770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242799 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_2242799 : Nat := 118140960795 + 2242799 * 2 ^ 59
def prefixEnd_2242799 : Nat := 4983230072969 + 3 ^ 40 * 2242799 * 2
def baseEnd_2242799 : Nat := 1151633898423275772298061

theorem tailTrace_2242799 : CollatzResearch.WordTrace tailWord_2242799 prefixEnd_2242799 1151633898423275772298061 := by
  unfold tailWord_2242799
  simp only [CollatzResearch.WordTrace]
  refine ⟨81801599801729737418971451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54534399867819824945980967 81801599801729737418971451)
  ·
    refine ⟨122702399702594606128457177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81801599801729737418971451 122702399702594606128457177)
    ·
      refine ⟨92026799776945954596342883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122702399702594606128457177 92026799776945954596342883)
      ·
        refine ⟨138040199665418931894514325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92026799776945954596342883 138040199665418931894514325)
        ·
          refine ⟨6470634359316512432555359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138040199665418931894514325 6470634359316512432555359)
          ·
            refine ⟨9705951538974768648833039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6470634359316512432555359 9705951538974768648833039)
            ·
              refine ⟨14558927308462152973249559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9705951538974768648833039 14558927308462152973249559)
              ·
                refine ⟨21838390962693229459874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14558927308462152973249559 21838390962693229459874339)
                ·
                  refine ⟨32757586444039844189811509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21838390962693229459874339 32757586444039844189811509)
                  ·
                    refine ⟨3071023729128735392794829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32757586444039844189811509 3071023729128735392794829)
                    ·
                      refine ⟨1151633898423275772298061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071023729128735392794829 1151633898423275772298061)
                      ·
                        rfl

theorem cell23_2242799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_2242799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242799 prefixEnd_2242799 := by exact prefixLift 2242799
  have htrace : WordTrace (prefixWord ++ tailWord_2242799) baseStart_2242799 baseEnd_2242799 := by
    simpa [prefixWord, tailWord_2242799, baseEnd_2242799] using wordTrace_append hprefix tailTrace_2242799
  have hstable : (prefixWord ++ tailWord_2242799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242799).length < 2 ^ (prefixWord ++ tailWord_2242799).sum := by decide
  have hdescent : baseEnd_2242799 < baseStart_2242799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242869 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2242869 : Nat := 118140960795 + 2242869 * 2 ^ 59
def prefixEnd_2242869 : Nat := 4983230072969 + 3 ^ 40 * 2242869 * 2
def baseEnd_2242869 : Nat := 1151669842069090498422739

theorem tailTrace_2242869 : CollatzResearch.WordTrace tailWord_2242869 prefixEnd_2242869 1151669842069090498422739 := by
  unfold tailWord_2242869
  simp only [CollatzResearch.WordTrace]
  refine ⟨81804152911476139374019661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54536101940984092916013107 81804152911476139374019661)
  ·
    refine ⟨30676557341803552265257373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81804152911476139374019661 30676557341803552265257373)
    ·
      refine ⟨11503709003176332099471515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30676557341803552265257373 11503709003176332099471515)
      ·
        refine ⟨17255563504764498149207273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503709003176332099471515 17255563504764498149207273)
        ·
          refine ⟨12941672628573373611905455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17255563504764498149207273 12941672628573373611905455)
          ·
            refine ⟨19412508942860060417858183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12941672628573373611905455 19412508942860060417858183)
            ·
              refine ⟨29118763414290090626787275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19412508942860060417858183 29118763414290090626787275)
              ·
                refine ⟨43678145121435135940180913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29118763414290090626787275 43678145121435135940180913)
                ·
                  refine ⟨32758608841076351955135685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43678145121435135940180913 32758608841076351955135685)
                  ·
                    refine ⟨6142239157701815991587941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32758608841076351955135685 6142239157701815991587941)
                    ·
                      refine ⟨1151669842069090498422739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6142239157701815991587941 1151669842069090498422739)
                      ·
                        rfl

theorem cell23_2242869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2242869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242869 prefixEnd_2242869 := by exact prefixLift 2242869
  have htrace : WordTrace (prefixWord ++ tailWord_2242869) baseStart_2242869 baseEnd_2242869 := by
    simpa [prefixWord, tailWord_2242869, baseEnd_2242869] using wordTrace_append hprefix tailTrace_2242869
  have hstable : (prefixWord ++ tailWord_2242869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242869).length < 2 ^ (prefixWord ++ tailWord_2242869).sum := by decide
  have hdescent : baseEnd_2242869 < baseStart_2242869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242876 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_2242876 : Nat := 118140960795 + 2242876 * 2 ^ 59
def prefixEnd_2242876 : Nat := 4983230072969 + 3 ^ 40 * 2242876 * 2
def baseEnd_2242876 : Nat := 1151673436433671971035207

theorem tailTrace_2242876 : CollatzResearch.WordTrace tailWord_2242876 prefixEnd_2242876 1151673436433671971035207 := by
  unfold tailWord_2242876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40902204111225389784762241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54536272148300519713016321 40902204111225389784762241)
  ·
    refine ⟨30676653083419042338571681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40902204111225389784762241 30676653083419042338571681)
    ·
      refine ⟨23007489812564281753928761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30676653083419042338571681 23007489812564281753928761)
      ·
        refine ⟨17255617359423211315446571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23007489812564281753928761 17255617359423211315446571)
        ·
          refine ⟨25883426039134816973169857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17255617359423211315446571 25883426039134816973169857)
          ·
            refine ⟨19412569529351112729877393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25883426039134816973169857 19412569529351112729877393)
            ·
              refine ⟨14559427147013334547408045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19412569529351112729877393 14559427147013334547408045)
              ·
                refine ⟨5459785180130000455278017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14559427147013334547408045 5459785180130000455278017)
                ·
                  refine ⟨4094838885097500341458513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5459785180130000455278017 4094838885097500341458513)
                  ·
                    refine ⟨3071129163823125256093885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4094838885097500341458513 3071129163823125256093885)
                    ·
                      refine ⟨1151673436433671971035207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071129163823125256093885 1151673436433671971035207)
                      ·
                        rfl

theorem cell23_2242876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_2242876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242876 prefixEnd_2242876 := by exact prefixLift 2242876
  have htrace : WordTrace (prefixWord ++ tailWord_2242876) baseStart_2242876 baseEnd_2242876 := by
    simpa [prefixWord, tailWord_2242876, baseEnd_2242876] using wordTrace_append hprefix tailTrace_2242876
  have hstable : (prefixWord ++ tailWord_2242876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242876).length < 2 ^ (prefixWord ++ tailWord_2242876).sum := by decide
  have hdescent : baseEnd_2242876 < baseStart_2242876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242883 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 1, 4]
def baseStart_2242883 : Nat := 118140960795 + 2242883 * 2 ^ 59
def prefixEnd_2242883 : Nat := 4983230072969 + 3 ^ 40 * 2242883 * 2
def baseEnd_2242883 : Nat := 383892343599417814549225

theorem tailTrace_2242883 : CollatzResearch.WordTrace tailWord_2242883 prefixEnd_2242883 383892343599417814549225 := by
  unfold tailWord_2242883
  simp only [CollatzResearch.WordTrace]
  refine ⟨81804663533425419765029303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54536442355616946510019535 81804663533425419765029303)
  ·
    refine ⟨122706995300138129647543955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81804663533425419765029303 122706995300138129647543955)
    ·
      refine ⟨184060492950207194471315933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122706995300138129647543955 184060492950207194471315933)
      ·
        refine ⟨69022684856327697926743475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184060492950207194471315933 69022684856327697926743475)
        ·
          refine ⟨103534027284491546890115213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69022684856327697926743475 103534027284491546890115213)
          ·
            refine ⟨38825260231684330083793205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103534027284491546890115213 38825260231684330083793205)
            ·
              refine ⟨3639868146720405945355613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38825260231684330083793205 3639868146720405945355613)
              ·
                refine ⟨1364950555020152229508355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3639868146720405945355613 1364950555020152229508355)
                ·
                  refine ⟨2047425832530228344262533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364950555020152229508355 2047425832530228344262533)
                  ·
                    refine ⟨383892343599417814549225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047425832530228344262533 383892343599417814549225)
                    ·
                      rfl

theorem cell23_2242883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 1, 4].length) (baseStart_2242883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242883 prefixEnd_2242883 := by exact prefixLift 2242883
  have htrace : WordTrace (prefixWord ++ tailWord_2242883) baseStart_2242883 baseEnd_2242883 := by
    simpa [prefixWord, tailWord_2242883, baseEnd_2242883] using wordTrace_append hprefix tailTrace_2242883
  have hstable : (prefixWord ++ tailWord_2242883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242883).length < 2 ^ (prefixWord ++ tailWord_2242883).sum := by decide
  have hdescent : baseEnd_2242883 < baseStart_2242883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242939 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 6]
def baseStart_2242939 : Nat := 118140960795 + 2242939 * 2 ^ 59
def prefixEnd_2242939 : Nat := 4983230072969 + 3 ^ 40 * 2242939 * 2
def baseEnd_2242939 : Nat := 383901928571635074849139

theorem tailTrace_2242939 : CollatzResearch.WordTrace tailWord_2242939 prefixEnd_2242939 383901928571635074849139 := by
  unfold tailWord_2242939
  simp only [CollatzResearch.WordTrace]
  refine ⟨81806706021222541329067871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54537804014148360886045247 81806706021222541329067871)
  ·
    refine ⟨122710059031833811993601807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81806706021222541329067871 122710059031833811993601807)
    ·
      refine ⟨184065088547750717990402711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122710059031833811993601807 184065088547750717990402711)
      ·
        refine ⟨276097632821626076985604067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184065088547750717990402711 276097632821626076985604067)
        ·
          refine ⟨414146449232439115478406101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276097632821626076985604067 414146449232439115478406101)
          ·
            refine ⟨9706557403885291769025143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 414146449232439115478406101 9706557403885291769025143)
            ·
              refine ⟨14559836105827937653537715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706557403885291769025143 14559836105827937653537715)
              ·
                refine ⟨21839754158741906480306573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14559836105827937653537715 21839754158741906480306573)
                ·
                  refine ⟨8189907809528214930114965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21839754158741906480306573 8189907809528214930114965)
                  ·
                    refine ⟨383901928571635074849139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8189907809528214930114965 383901928571635074849139)
                    ·
                      rfl

theorem cell23_2242939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_2242939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242939 prefixEnd_2242939 := by exact prefixLift 2242939
  have htrace : WordTrace (prefixWord ++ tailWord_2242939) baseStart_2242939 baseEnd_2242939 := by
    simpa [prefixWord, tailWord_2242939, baseEnd_2242939] using wordTrace_append hprefix tailTrace_2242939
  have hstable : (prefixWord ++ tailWord_2242939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242939).length < 2 ^ (prefixWord ++ tailWord_2242939).sum := by decide
  have hdescent : baseEnd_2242939 < baseStart_2242939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242973 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2242973 : Nat := 118140960795 + 2242973 * 2 ^ 59
def prefixEnd_2242973 : Nat := 4983230072969 + 3 ^ 40 * 2242973 * 2
def baseEnd_2242973 : Nat := 383907748019052697174087

theorem tailTrace_2242973 : CollatzResearch.WordTrace tailWord_2242973 prefixEnd_2242973 383907748019052697174087 := by
  unfold tailWord_2242973
  simp only [CollatzResearch.WordTrace]
  refine ⟨81807946103099365135805573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54538630735399576757203715 81807946103099365135805573)
  ·
    refine ⟨15338989894331130962963545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81807946103099365135805573 15338989894331130962963545)
    ·
      refine ⟨11504242420748348222222659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15338989894331130962963545 11504242420748348222222659)
      ·
        refine ⟨17256363631122522333333989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11504242420748348222222659 17256363631122522333333989)
        ·
          refine ⟨3235568180835472937500123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17256363631122522333333989 3235568180835472937500123)
          ·
            refine ⟨4853352271253209406250185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235568180835472937500123 4853352271253209406250185)
            ·
              refine ⟨3640014203439907054687639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4853352271253209406250185 3640014203439907054687639)
              ·
                refine ⟨5460021305159860582031459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3640014203439907054687639 5460021305159860582031459)
                ·
                  refine ⟨8190031957739790873047189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5460021305159860582031459 8190031957739790873047189)
                  ·
                    refine ⟨383907748019052697174087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8190031957739790873047189 383907748019052697174087)
                    ·
                      rfl

theorem cell23_2242973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2242973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242973 prefixEnd_2242973 := by exact prefixLift 2242973
  have htrace : WordTrace (prefixWord ++ tailWord_2242973) baseStart_2242973 baseEnd_2242973 := by
    simpa [prefixWord, tailWord_2242973, baseEnd_2242973] using wordTrace_append hprefix tailTrace_2242973
  have hstable : (prefixWord ++ tailWord_2242973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242973).length < 2 ^ (prefixWord ++ tailWord_2242973).sum := by decide
  have hdescent : baseEnd_2242973 < baseStart_2242973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242976 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2242976 : Nat := 118140960795 + 2242976 * 2 ^ 59
def prefixEnd_2242976 : Nat := 4983230072969 + 3 ^ 40 * 2242976 * 2
def baseEnd_2242976 : Nat := 1151724784499121579784747

theorem tailTrace_2242976 : CollatzResearch.WordTrace tailWord_2242976 prefixEnd_2242976 1151724784499121579784747 := by
  unfold tailWord_2242976
  simp only [CollatzResearch.WordTrace]
  refine ⟨40904027761044248324082391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54538703681392331098776521 40904027761044248324082391)
  ·
    refine ⟨61356041641566372486123587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40904027761044248324082391 61356041641566372486123587)
    ·
      refine ⟨92034062462349558729185381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61356041641566372486123587 92034062462349558729185381)
      ·
        refine ⟨17256386711690542261722259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92034062462349558729185381 17256386711690542261722259)
        ·
          refine ⟨25884580067535813392583389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17256386711690542261722259 25884580067535813392583389)
          ·
            refine ⟨9706717525325930022218771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25884580067535813392583389 9706717525325930022218771)
            ·
              refine ⟨14560076287988895033328157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9706717525325930022218771 14560076287988895033328157)
              ·
                refine ⟨5460028607995835637498059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14560076287988895033328157 5460028607995835637498059)
                ·
                  refine ⟨8190042911993753456247089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5460028607995835637498059 8190042911993753456247089)
                  ·
                    refine ⟨6142532183995315092185317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8190042911993753456247089 6142532183995315092185317)
                    ·
                      refine ⟨1151724784499121579784747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6142532183995315092185317 1151724784499121579784747)
                      ·
                        rfl

theorem cell23_2242976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2242976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242976 prefixEnd_2242976 := by exact prefixLift 2242976
  have htrace : WordTrace (prefixWord ++ tailWord_2242976) baseStart_2242976 baseEnd_2242976 := by
    simpa [prefixWord, tailWord_2242976, baseEnd_2242976] using wordTrace_append hprefix tailTrace_2242976
  have hstable : (prefixWord ++ tailWord_2242976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242976).length < 2 ^ (prefixWord ++ tailWord_2242976).sum := by decide
  have hdescent : baseEnd_2242976 < baseStart_2242976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242983 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_2242983 : Nat := 118140960795 + 2242983 * 2 ^ 59
def prefixEnd_2242983 : Nat := 4983230072969 + 3 ^ 40 * 2242983 * 2
def baseEnd_2242983 : Nat := 1151728378863703052397215

theorem tailTrace_2242983 : CollatzResearch.WordTrace tailWord_2242983 prefixEnd_2242983 1151728378863703052397215 := by
  unfold tailWord_2242983
  simp only [CollatzResearch.WordTrace]
  refine ⟨81808310833063136843669603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54538873888708757895779735 81808310833063136843669603)
  ·
    refine ⟨122712466249594705265504405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81808310833063136843669603 122712466249594705265504405)
    ·
      refine ⟨5752146855449751809320519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122712466249594705265504405 5752146855449751809320519)
      ·
        refine ⟨8628220283174627713980779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752146855449751809320519 8628220283174627713980779)
        ·
          refine ⟨12942330424761941570971169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628220283174627713980779 12942330424761941570971169)
          ·
            refine ⟨9706747818571456178228377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12942330424761941570971169 9706747818571456178228377)
            ·
              refine ⟨7280060863928592133671283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9706747818571456178228377 7280060863928592133671283)
              ·
                refine ⟨10920091295892888200506925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7280060863928592133671283 10920091295892888200506925)
                ·
                  refine ⟨4095034235959833075190097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10920091295892888200506925 4095034235959833075190097)
                  ·
                    refine ⟨3071275676969874806392573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095034235959833075190097 3071275676969874806392573)
                    ·
                      refine ⟨1151728378863703052397215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071275676969874806392573 1151728378863703052397215)
                      ·
                        rfl

theorem cell23_2242983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_2242983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242983 prefixEnd_2242983 := by exact prefixLift 2242983
  have htrace : WordTrace (prefixWord ++ tailWord_2242983) baseStart_2242983 baseEnd_2242983 := by
    simpa [prefixWord, tailWord_2242983, baseEnd_2242983] using wordTrace_append hprefix tailTrace_2242983
  have hstable : (prefixWord ++ tailWord_2242983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242983).length < 2 ^ (prefixWord ++ tailWord_2242983).sum := by decide
  have hdescent : baseEnd_2242983 < baseStart_2242983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2242997 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_2242997 : Nat := 118140960795 + 2242997 * 2 ^ 59
def prefixEnd_2242997 : Nat := 4983230072969 + 3 ^ 40 * 2242997 * 2
def baseEnd_2242997 : Nat := 1151735567592865997622151

theorem tailTrace_2242997 : CollatzResearch.WordTrace tailWord_2242997 prefixEnd_2242997 1151735567592865997622151 := by
  unfold tailWord_2242997
  simp only [CollatzResearch.WordTrace]
  refine ⟨81808821455012417234679245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54539214303341611489786163 81808821455012417234679245)
  ·
    refine ⟨30678308045629656463004717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81808821455012417234679245 30678308045629656463004717)
    ·
      refine ⟨11504365517111121173626769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30678308045629656463004717 11504365517111121173626769)
      ·
        refine ⟨8628274137833340880220077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11504365517111121173626769 8628274137833340880220077)
        ·
          refine ⟨3235602801687502830082529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8628274137833340880220077 3235602801687502830082529)
          ·
            refine ⟨2426702101265627122561897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235602801687502830082529 2426702101265627122561897)
            ·
              refine ⟨1820026575949220341921423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426702101265627122561897 1820026575949220341921423)
              ·
                refine ⟨2730039863923830512882135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820026575949220341921423 2730039863923830512882135)
                ·
                  refine ⟨4095059795885745769323203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730039863923830512882135 4095059795885745769323203)
                  ·
                    refine ⟨6142589693828618653984805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4095059795885745769323203 6142589693828618653984805)
                    ·
                      refine ⟨1151735567592865997622151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6142589693828618653984805 1151735567592865997622151)
                      ·
                        rfl

theorem cell23_2242997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_2242997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2242997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2242997 prefixEnd_2242997 := by exact prefixLift 2242997
  have htrace : WordTrace (prefixWord ++ tailWord_2242997) baseStart_2242997 baseEnd_2242997 := by
    simpa [prefixWord, tailWord_2242997, baseEnd_2242997] using wordTrace_append hprefix tailTrace_2242997
  have hstable : (prefixWord ++ tailWord_2242997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2242997).length < 2 ^ (prefixWord ++ tailWord_2242997).sum := by decide
  have hdescent : baseEnd_2242997 < baseStart_2242997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2242997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243040 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2]
def baseStart_2243040 : Nat := 118140960795 + 2243040 * 2 ^ 59
def prefixEnd_2243040 : Nat := 4983230072969 + 3 ^ 40 * 2243040 * 2
def baseEnd_2243040 : Nat := 1151757647261009329384453

theorem tailTrace_2243040 : CollatzResearch.WordTrace tailWord_2243040 prefixEnd_2243040 1151757647261009329384453 := by
  unfold tailWord_2243040
  simp only [CollatzResearch.WordTrace]
  refine ⟨40905194896928317789247287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54540259862571090385663049 40905194896928317789247287)
  ·
    refine ⟨61357792345392476683870931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40905194896928317789247287 61357792345392476683870931)
    ·
      refine ⟨92036688518088715025806397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61357792345392476683870931 92036688518088715025806397)
      ·
        refine ⟨34513758194283268134677399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92036688518088715025806397 34513758194283268134677399)
        ·
          refine ⟨51770637291424902202016099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34513758194283268134677399 51770637291424902202016099)
          ·
            refine ⟨77655955937137353303024149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51770637291424902202016099 77655955937137353303024149)
            ·
              refine ⟨3640122934553313436079257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77655955937137353303024149 3640122934553313436079257)
              ·
                refine ⟨2730092200914985077059443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640122934553313436079257 2730092200914985077059443)
                ·
                  refine ⟨4095138301372477615589165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730092200914985077059443 4095138301372477615589165)
                  ·
                    refine ⟨1535676863014679105845937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4095138301372477615589165 1535676863014679105845937)
                    ·
                      refine ⟨1151757647261009329384453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535676863014679105845937 1151757647261009329384453)
                      ·
                        rfl

theorem cell23_2243040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_2243040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243040 prefixEnd_2243040 := by exact prefixLift 2243040
  have htrace : WordTrace (prefixWord ++ tailWord_2243040) baseStart_2243040 baseEnd_2243040 := by
    simpa [prefixWord, tailWord_2243040, baseEnd_2243040] using wordTrace_append hprefix tailTrace_2243040
  have hstable : (prefixWord ++ tailWord_2243040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243040).length < 2 ^ (prefixWord ++ tailWord_2243040).sum := by decide
  have hdescent : baseEnd_2243040 < baseStart_2243040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243056 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_2243056 : Nat := 118140960795 + 2243056 * 2 ^ 59
def prefixEnd_2243056 : Nat := 4983230072969 + 3 ^ 40 * 2243056 * 2
def baseEnd_2243056 : Nat := 1151765862951481266784379

theorem tailTrace_2243056 : CollatzResearch.WordTrace tailWord_2243056 prefixEnd_2243056 1151765862951481266784379 := by
  unfold tailWord_2243056
  simp only [CollatzResearch.WordTrace]
  refine ⟨40905486680899335155538511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54540648907865780207384681 40905486680899335155538511)
  ·
    refine ⟨61358230021349002733307767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40905486680899335155538511 61358230021349002733307767)
    ·
      refine ⟨92037345032023504099961651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61358230021349002733307767 92037345032023504099961651)
      ·
        refine ⟨138056017548035256149942477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92037345032023504099961651 138056017548035256149942477)
        ·
          refine ⟨51771006580513221056228429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138056017548035256149942477 51771006580513221056228429)
          ·
            refine ⟨19414127467692457896085661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51771006580513221056228429 19414127467692457896085661)
            ·
              refine ⟨7280297800384671711032123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19414127467692457896085661 7280297800384671711032123)
              ·
                refine ⟨10920446700577007566548185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7280297800384671711032123 10920446700577007566548185)
                ·
                  refine ⟨8190335025432755674911139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10920446700577007566548185 8190335025432755674911139)
                  ·
                    refine ⟨12285502538149133512366709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8190335025432755674911139 12285502538149133512366709)
                    ·
                      refine ⟨1151765862951481266784379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12285502538149133512366709 1151765862951481266784379)
                      ·
                        rfl

theorem cell23_2243056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_2243056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243056 prefixEnd_2243056 := by exact prefixLift 2243056
  have htrace : WordTrace (prefixWord ++ tailWord_2243056) baseStart_2243056 baseEnd_2243056 := by
    simpa [prefixWord, tailWord_2243056, baseEnd_2243056] using wordTrace_append hprefix tailTrace_2243056
  have hstable : (prefixWord ++ tailWord_2243056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243056).length < 2 ^ (prefixWord ++ tailWord_2243056).sum := by decide
  have hdescent : baseEnd_2243056 < baseStart_2243056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243066 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_2243066 : Nat := 118140960795 + 2243066 * 2 ^ 59
def prefixEnd_2243066 : Nat := 4983230072969 + 3 ^ 40 * 2243066 * 2
def baseEnd_2243066 : Nat := 1151770997758026227659333

theorem tailTrace_2243066 : CollatzResearch.WordTrace tailWord_2243066 prefixEnd_2243066 1151770997758026227659333 := by
  unfold tailWord_2243066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20452834522940610504735263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54540892061174961345960701 20452834522940610504735263)
  ·
    refine ⟨30679251784410915757102895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20452834522940610504735263 30679251784410915757102895)
    ·
      refine ⟨46018877676616373635654343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30679251784410915757102895 46018877676616373635654343)
      ·
        refine ⟨69028316514924560453481515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46018877676616373635654343 69028316514924560453481515)
        ·
          refine ⟨103542474772386840680222273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69028316514924560453481515 103542474772386840680222273)
          ·
            refine ⟨77656856079290130510166705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103542474772386840680222273 77656856079290130510166705)
            ·
              refine ⟨58242642059467597882625029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77656856079290130510166705 58242642059467597882625029)
              ·
                refine ⟨10920495386150174602992193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58242642059467597882625029 10920495386150174602992193)
                ·
                  refine ⟨8190371539612630952244145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10920495386150174602992193 8190371539612630952244145)
                  ·
                    refine ⟨6142778654709473214183109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8190371539612630952244145 6142778654709473214183109)
                    ·
                      refine ⟨1151770997758026227659333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6142778654709473214183109 1151770997758026227659333)
                      ·
                        rfl

theorem cell23_2243066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_2243066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243066 prefixEnd_2243066 := by exact prefixLift 2243066
  have htrace : WordTrace (prefixWord ++ tailWord_2243066) baseStart_2243066 baseEnd_2243066 := by
    simpa [prefixWord, tailWord_2243066, baseEnd_2243066] using wordTrace_append hprefix tailTrace_2243066
  have hstable : (prefixWord ++ tailWord_2243066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243066).length < 2 ^ (prefixWord ++ tailWord_2243066).sum := by decide
  have hdescent : baseEnd_2243066 < baseStart_2243066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243133 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2243133 : Nat := 118140960795 + 2243133 * 2 ^ 59
def prefixEnd_2243133 : Nat := 4983230072969 + 3 ^ 40 * 2243133 * 2
def baseEnd_2243133 : Nat := 1151805400961877465521525

theorem tailTrace_2243133 : CollatzResearch.WordTrace tailWord_2243133 prefixEnd_2243133 1151805400961877465521525 := by
  unfold tailWord_2243133
  simp only [CollatzResearch.WordTrace]
  refine ⟨81813781782519712461630053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54542521188346474974420035 81813781782519712461630053)
  ·
    refine ⟨15340084084222446086555635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81813781782519712461630053 15340084084222446086555635)
    ·
      refine ⟨23010126126333669129833453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15340084084222446086555635 23010126126333669129833453)
      ·
        refine ⟨8628797297375125923687545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23010126126333669129833453 8628797297375125923687545)
        ·
          refine ⟨6471597973031344442765659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8628797297375125923687545 6471597973031344442765659)
          ·
            refine ⟨9707396959547016664148489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6471597973031344442765659 9707396959547016664148489)
            ·
              refine ⟨7280547719660262498111367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9707396959547016664148489 7280547719660262498111367)
              ·
                refine ⟨10920821579490393747167051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7280547719660262498111367 10920821579490393747167051)
                ·
                  refine ⟨16381232369235590620750577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10920821579490393747167051 16381232369235590620750577)
                  ·
                    refine ⟨12285924276926692965562933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16381232369235590620750577 12285924276926692965562933)
                    ·
                      refine ⟨1151805400961877465521525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12285924276926692965562933 1151805400961877465521525)
                      ·
                        rfl

theorem cell23_2243133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2243133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243133 prefixEnd_2243133 := by exact prefixLift 2243133
  have htrace : WordTrace (prefixWord ++ tailWord_2243133) baseStart_2243133 baseEnd_2243133 := by
    simpa [prefixWord, tailWord_2243133, baseEnd_2243133] using wordTrace_append hprefix tailTrace_2243133
  have hstable : (prefixWord ++ tailWord_2243133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243133).length < 2 ^ (prefixWord ++ tailWord_2243133).sum := by decide
  have hdescent : baseEnd_2243133 < baseStart_2243133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243153 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_2243153 : Nat := 118140960795 + 2243153 * 2 ^ 59
def prefixEnd_2243153 : Nat := 4983230072969 + 3 ^ 40 * 2243153 * 2
def baseEnd_2243153 : Nat := 383938556858322462423811

theorem tailTrace_2243153 : CollatzResearch.WordTrace tailWord_2243153 prefixEnd_2243153 383938556858322462423811 := by
  unfold tailWord_2243153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81814511242447255877358113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54543007494964837251572075 81814511242447255877358113)
  ·
    refine ⟨61360883431835441908018585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81814511242447255877358113 61360883431835441908018585)
    ·
      refine ⟨46020662573876581431013939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61360883431835441908018585 46020662573876581431013939)
      ·
        refine ⟨69030993860814872146520909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46020662573876581431013939 69030993860814872146520909)
        ·
          refine ⟨25886622697805577054945341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69030993860814872146520909 25886622697805577054945341)
          ·
            refine ⟨9707483511677091395604503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25886622697805577054945341 9707483511677091395604503)
            ·
              refine ⟨14561225267515637093406755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9707483511677091395604503 14561225267515637093406755)
              ·
                refine ⟨21841837901273455640110133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14561225267515637093406755 21841837901273455640110133)
                ·
                  refine ⟨2047672303244386466260325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21841837901273455640110133 2047672303244386466260325)
                  ·
                    refine ⟨383938556858322462423811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047672303244386466260325 383938556858322462423811)
                    ·
                      rfl

theorem cell23_2243153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_2243153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243153 prefixEnd_2243153 := by exact prefixLift 2243153
  have htrace : WordTrace (prefixWord ++ tailWord_2243153) baseStart_2243153 baseEnd_2243153 := by
    simpa [prefixWord, tailWord_2243153, baseEnd_2243153] using wordTrace_append hprefix tailTrace_2243153
  have hstable : (prefixWord ++ tailWord_2243153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243153).length < 2 ^ (prefixWord ++ tailWord_2243153).sum := by decide
  have hdescent : baseEnd_2243153 < baseStart_2243153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243183 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 6]
def baseStart_2243183 : Nat := 118140960795 + 2243183 * 2 ^ 59
def prefixEnd_2243183 : Nat := 4983230072969 + 3 ^ 40 * 2243183 * 2
def baseEnd_2243183 : Nat := 127981230554955807766255

theorem tailTrace_2243183 : CollatzResearch.WordTrace tailWord_2243183 prefixEnd_2243183 127981230554955807766255 := by
  unfold tailWord_2243183
  simp only [CollatzResearch.WordTrace]
  refine ⟨81815605432338571000950203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54543736954892380667300135 81815605432338571000950203)
  ·
    refine ⟨122723408148507856501425305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81815605432338571000950203 122723408148507856501425305)
    ·
      refine ⟨92042556111380892376068979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122723408148507856501425305 92042556111380892376068979)
      ·
        refine ⟨138063834167071338564103469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92042556111380892376068979 138063834167071338564103469)
        ·
          refine ⟨51773937812651751961538801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138063834167071338564103469 51773937812651751961538801)
          ·
            refine ⟨38830453359488813971154101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51773937812651751961538801 38830453359488813971154101)
            ·
              refine ⟨3640355002452076309795697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38830453359488813971154101 3640355002452076309795697)
              ·
                refine ⟨2730266251839057232346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640355002452076309795697 2730266251839057232346773)
                ·
                  refine ⟨127981230554955807766255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2730266251839057232346773 127981230554955807766255)
                  ·
                    rfl

theorem cell23_2243183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 6].length) (baseStart_2243183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243183 prefixEnd_2243183 := by exact prefixLift 2243183
  have htrace : WordTrace (prefixWord ++ tailWord_2243183) baseStart_2243183 baseEnd_2243183 := by
    simpa [prefixWord, tailWord_2243183, baseEnd_2243183] using wordTrace_append hprefix tailTrace_2243183
  have hstable : (prefixWord ++ tailWord_2243183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243183).length < 2 ^ (prefixWord ++ tailWord_2243183).sum := by decide
  have hdescent : baseEnd_2243183 < baseStart_2243183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243200 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 6]
def baseStart_2243200 : Nat := 118140960795 + 2243200 * 2 ^ 59
def prefixEnd_2243200 : Nat := 4983230072969 + 3 ^ 40 * 2243200 * 2
def baseEnd_2243200 : Nat := 127982200462858744820413

theorem tailTrace_2243200 : CollatzResearch.WordTrace tailWord_2243200 prefixEnd_2243200 127982200462858744820413 := by
  unfold tailWord_2243200
  simp only [CollatzResearch.WordTrace]
  refine ⟨40908112736638491452159527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54544150315517988602879369 40908112736638491452159527)
  ·
    refine ⟨61362169104957737178239291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40908112736638491452159527 61362169104957737178239291)
    ·
      refine ⟨92043253657436605767358937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61362169104957737178239291 92043253657436605767358937)
      ·
        refine ⟨69032440243077454325519203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92043253657436605767358937 69032440243077454325519203)
        ·
          refine ⟨103548660364616181488278805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69032440243077454325519203 103548660364616181488278805)
          ·
            refine ⟨4853843454591383507263069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103548660364616181488278805 4853843454591383507263069)
            ·
              refine ⟨1820191295471768815223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4853843454591383507263069 1820191295471768815223651)
              ·
                refine ⟨2730286943207653222835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820191295471768815223651 2730286943207653222835477)
                ·
                  refine ⟨127982200462858744820413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2730286943207653222835477 127982200462858744820413)
                  ·
                    rfl

theorem cell23_2243200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_2243200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243200 prefixEnd_2243200 := by exact prefixLift 2243200
  have htrace : WordTrace (prefixWord ++ tailWord_2243200) baseStart_2243200 baseEnd_2243200 := by
    simpa [prefixWord, tailWord_2243200, baseEnd_2243200] using wordTrace_append hprefix tailTrace_2243200
  have hstable : (prefixWord ++ tailWord_2243200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243200).length < 2 ^ (prefixWord ++ tailWord_2243200).sum := by decide
  have hdescent : baseEnd_2243200 < baseStart_2243200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243263 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_2243263 : Nat := 118140960795 + 2243263 * 2 ^ 59
def prefixEnd_2243263 : Nat := 4983230072969 + 3 ^ 40 * 2243263 * 2
def baseEnd_2243263 : Nat := 1151872153446961956895927

theorem tailTrace_2243263 : CollatzResearch.WordTrace tailWord_2243263 prefixEnd_2243263 1151872153446961956895927 := by
  unfold tailWord_2243263
  simp only [CollatzResearch.WordTrace]
  refine ⟨81818523272048744663862443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54545682181365829775908295 81818523272048744663862443)
  ·
    refine ⟨122727784908073116995793665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81818523272048744663862443 122727784908073116995793665)
    ·
      refine ⟨92045838681054837746845249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122727784908073116995793665 92045838681054837746845249)
      ·
        refine ⟨69034379010791128310133937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92045838681054837746845249 69034379010791128310133937)
        ·
          refine ⟨51775784258093346232600453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69034379010791128310133937 51775784258093346232600453)
          ·
            refine ⟨9707959548392502418612585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51775784258093346232600453 9707959548392502418612585)
            ·
              refine ⟨7280969661294376813959439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9707959548392502418612585 7280969661294376813959439)
              ·
                refine ⟨10921454491941565220939159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7280969661294376813959439 10921454491941565220939159)
                ·
                  refine ⟨16382181737912347831408739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10921454491941565220939159 16382181737912347831408739)
                  ·
                    refine ⟨24573272606868521747113109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16382181737912347831408739 24573272606868521747113109)
                    ·
                      refine ⟨1151872153446961956895927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24573272606868521747113109 1151872153446961956895927)
                      ·
                        rfl

theorem cell23_2243263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_2243263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243263 prefixEnd_2243263 := by exact prefixLift 2243263
  have htrace : WordTrace (prefixWord ++ tailWord_2243263) baseStart_2243263 baseEnd_2243263 := by
    simpa [prefixWord, tailWord_2243263, baseEnd_2243263] using wordTrace_append hprefix tailTrace_2243263
  have hstable : (prefixWord ++ tailWord_2243263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243263).length < 2 ^ (prefixWord ++ tailWord_2243263).sum := by decide
  have hdescent : baseEnd_2243263 < baseStart_2243263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243301 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2243301 : Nat := 118140960795 + 2243301 * 2 ^ 59
def prefixEnd_2243301 : Nat := 4983230072969 + 3 ^ 40 * 2243301 * 2
def baseEnd_2243301 : Nat := 1151891665711832808220753

theorem tailTrace_2243301 : CollatzResearch.WordTrace tailWord_2243301 prefixEnd_2243301 1151891665711832808220753 := by
  unfold tailWord_2243301
  simp only [CollatzResearch.WordTrace]
  refine ⟨81819909245911077153745757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54546606163940718102497171 81819909245911077153745757)
  ·
    refine ⟨30682465967216653932654659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81819909245911077153745757 30682465967216653932654659)
    ·
      refine ⟨46023698950824980898981989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30682465967216653932654659 46023698950824980898981989)
      ·
        refine ⟨8629443553279683918559123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46023698950824980898981989 8629443553279683918559123)
        ·
          refine ⟨12944165329919525877838685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8629443553279683918559123 12944165329919525877838685)
          ·
            refine ⟨4854061998719822204189507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12944165329919525877838685 4854061998719822204189507)
            ·
              refine ⟨7281092998079733306284261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854061998719822204189507 7281092998079733306284261)
              ·
                refine ⟨1365204937139949994928299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7281092998079733306284261 1365204937139949994928299)
                ·
                  refine ⟨2047807405709924992392449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365204937139949994928299 2047807405709924992392449)
                  ·
                    refine ⟨1535855554282443744294337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2047807405709924992392449 1535855554282443744294337)
                    ·
                      refine ⟨1151891665711832808220753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535855554282443744294337 1151891665711832808220753)
                      ·
                        rfl

theorem cell23_2243301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2243301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243301 prefixEnd_2243301 := by exact prefixLift 2243301
  have htrace : WordTrace (prefixWord ++ tailWord_2243301) baseStart_2243301 baseEnd_2243301 := by
    simpa [prefixWord, tailWord_2243301, baseEnd_2243301] using wordTrace_append hprefix tailTrace_2243301
  have hstable : (prefixWord ++ tailWord_2243301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243301).length < 2 ^ (prefixWord ++ tailWord_2243301).sum := by decide
  have hdescent : baseEnd_2243301 < baseStart_2243301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243327 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 1, 3, 2]
def baseStart_2243327 : Nat := 118140960795 + 2243327 * 2 ^ 59
def prefixEnd_2243327 : Nat := 4983230072969 + 3 ^ 40 * 2243327 * 2
def baseEnd_2243327 : Nat := 1151905016208849706495633

theorem tailTrace_2243327 : CollatzResearch.WordTrace tailWord_2243327 prefixEnd_2243327 1151905016208849706495633 := by
  unfold tailWord_2243327
  simp only [CollatzResearch.WordTrace]
  refine ⟨81820857543816883594192235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54547238362544589062794823 81820857543816883594192235)
  ·
    refine ⟨122731286315725325391288353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81820857543816883594192235 122731286315725325391288353)
    ·
      refine ⟨92048464736793994043466265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122731286315725325391288353 92048464736793994043466265)
      ·
        refine ⟨69036348552595495532599699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92048464736793994043466265 69036348552595495532599699)
        ·
          refine ⟨103554522828893243298899549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69036348552595495532599699 103554522828893243298899549)
          ·
            refine ⟨38832946060834966237087331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103554522828893243298899549 38832946060834966237087331)
            ·
              refine ⟨58249419091252449355630997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38832946060834966237087331 58249419091252449355630997)
              ·
                refine ⟨2730441519902458563545203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58249419091252449355630997 2730441519902458563545203)
                ·
                  refine ⟨4095662279853687845317805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730441519902458563545203 4095662279853687845317805)
                  ·
                    refine ⟨1535873354945132941994177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4095662279853687845317805 1535873354945132941994177)
                    ·
                      refine ⟨1151905016208849706495633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1535873354945132941994177 1151905016208849706495633)
                      ·
                        rfl

theorem cell23_2243327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_2243327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243327 prefixEnd_2243327 := by exact prefixLift 2243327
  have htrace : WordTrace (prefixWord ++ tailWord_2243327) baseStart_2243327 baseEnd_2243327 := by
    simpa [prefixWord, tailWord_2243327, baseEnd_2243327] using wordTrace_append hprefix tailTrace_2243327
  have hstable : (prefixWord ++ tailWord_2243327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243327).length < 2 ^ (prefixWord ++ tailWord_2243327).sum := by decide
  have hdescent : baseEnd_2243327 < baseStart_2243327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243343 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_2243343 : Nat := 118140960795 + 2243343 * 2 ^ 59
def prefixEnd_2243343 : Nat := 4983230072969 + 3 ^ 40 * 2243343 * 2
def baseEnd_2243343 : Nat := 1151913231899321643895559

theorem tailTrace_2243343 : CollatzResearch.WordTrace tailWord_2243343 prefixEnd_2243343 1151913231899321643895559 := by
  unfold tailWord_2243343
  simp only [CollatzResearch.WordTrace]
  refine ⟨81821441111758918326774683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54547627407839278884516455 81821441111758918326774683)
  ·
    refine ⟨122732161667638377490162025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81821441111758918326774683 122732161667638377490162025)
    ·
      refine ⟨92049121250728783117621519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122732161667638377490162025 92049121250728783117621519)
      ·
        refine ⟨138073681876093174676432279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92049121250728783117621519 138073681876093174676432279)
        ·
          refine ⟨207110522814139762014648419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138073681876093174676432279 207110522814139762014648419)
          ·
            refine ⟨310665784221209643021972629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207110522814139762014648419 310665784221209643021972629)
            ·
              refine ⟨14562458635369202016654967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 310665784221209643021972629 14562458635369202016654967)
              ·
                refine ⟨21843687953053803024982451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14562458635369202016654967 21843687953053803024982451)
                ·
                  refine ⟨32765531929580704537473677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21843687953053803024982451 32765531929580704537473677)
                  ·
                    refine ⟨12287074473592764201552629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32765531929580704537473677 12287074473592764201552629)
                    ·
                      refine ⟨1151913231899321643895559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12287074473592764201552629 1151913231899321643895559)
                      ·
                        rfl

theorem cell23_2243343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_2243343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243343 prefixEnd_2243343 := by exact prefixLift 2243343
  have htrace : WordTrace (prefixWord ++ tailWord_2243343) baseStart_2243343 baseEnd_2243343 := by
    simpa [prefixWord, tailWord_2243343, baseEnd_2243343] using wordTrace_append hprefix tailTrace_2243343
  have hstable : (prefixWord ++ tailWord_2243343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243343).length < 2 ^ (prefixWord ++ tailWord_2243343).sum := by decide
  have hdescent : baseEnd_2243343 < baseStart_2243343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243351 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2243351 : Nat := 118140960795 + 2243351 * 2 ^ 59
def prefixEnd_2243351 : Nat := 4983230072969 + 3 ^ 40 * 2243351 * 2
def baseEnd_2243351 : Nat := 1151917339744557612595523

theorem tailTrace_2243351 : CollatzResearch.WordTrace tailWord_2243351 prefixEnd_2243351 1151917339744557612595523 := by
  unfold tailWord_2243351
  simp only [CollatzResearch.WordTrace]
  refine ⟨81821732895729935693065907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54547821930486623795377271 81821732895729935693065907)
  ·
    refine ⟨122732599343594903539598861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81821732895729935693065907 122732599343594903539598861)
    ·
      refine ⟨46024724753848088827349573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122732599343594903539598861 46024724753848088827349573)
      ·
        refine ⟨8629635891346516655128045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46024724753848088827349573 8629635891346516655128045)
        ·
          refine ⟨3236113459254943745673017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8629635891346516655128045 3236113459254943745673017)
          ·
            refine ⟨2427085094441207809254763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3236113459254943745673017 2427085094441207809254763)
            ·
              refine ⟨3640627641661811713882145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427085094441207809254763 3640627641661811713882145)
              ·
                refine ⟨2730470731246358785411609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640627641661811713882145 2730470731246358785411609)
                ·
                  refine ⟨2047853048434769089058707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730470731246358785411609 2047853048434769089058707)
                  ·
                    refine ⟨3071779572652153633588061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2047853048434769089058707 3071779572652153633588061)
                    ·
                      refine ⟨1151917339744557612595523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071779572652153633588061 1151917339744557612595523)
                      ·
                        rfl

theorem cell23_2243351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2243351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243351 prefixEnd_2243351 := by exact prefixLift 2243351
  have htrace : WordTrace (prefixWord ++ tailWord_2243351) baseStart_2243351 baseEnd_2243351 := by
    simpa [prefixWord, tailWord_2243351, baseEnd_2243351] using wordTrace_append hprefix tailTrace_2243351
  have hstable : (prefixWord ++ tailWord_2243351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243351).length < 2 ^ (prefixWord ++ tailWord_2243351).sum := by decide
  have hdescent : baseEnd_2243351 < baseStart_2243351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243403 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_2243403 : Nat := 118140960795 + 2243403 * 2 ^ 59
def prefixEnd_2243403 : Nat := 4983230072969 + 3 ^ 40 * 2243403 * 2
def baseEnd_2243403 : Nat := 1151944040738591409145283

theorem tailTrace_2243403 : CollatzResearch.WordTrace tailWord_2243403 prefixEnd_2243403 1151944040738591409145283 := by
  unfold tailWord_2243403
  simp only [CollatzResearch.WordTrace]
  refine ⟨81823629491541548573958863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54549086327694365715972575 81823629491541548573958863)
  ·
    refine ⟨122735444237312322860938295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81823629491541548573958863 122735444237312322860938295)
    ·
      refine ⟨184103166355968484291407443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122735444237312322860938295 184103166355968484291407443)
      ·
        refine ⟨276154749533952726437111165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184103166355968484291407443 276154749533952726437111165)
        ·
          refine ⟨103558031075232272413916687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276154749533952726437111165 103558031075232272413916687)
          ·
            refine ⟨155337046612848408620875031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103558031075232272413916687 155337046612848408620875031)
            ·
              refine ⟨233005569919272612931312547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155337046612848408620875031 233005569919272612931312547)
              ·
                refine ⟨349508354878908919396968821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233005569919272612931312547 349508354878908919396968821)
                ·
                  refine ⟨32766408269897711193465827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 349508354878908919396968821 32766408269897711193465827)
                  ·
                    refine ⟨49149612404846566790198741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32766408269897711193465827 49149612404846566790198741)
                    ·
                      refine ⟨1151944040738591409145283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49149612404846566790198741 1151944040738591409145283)
                      ·
                        rfl

theorem cell23_2243403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_2243403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243403 prefixEnd_2243403 := by exact prefixLift 2243403
  have htrace : WordTrace (prefixWord ++ tailWord_2243403) baseStart_2243403 baseEnd_2243403 := by
    simpa [prefixWord, tailWord_2243403, baseEnd_2243403] using wordTrace_append hprefix tailTrace_2243403
  have hstable : (prefixWord ++ tailWord_2243403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243403).length < 2 ^ (prefixWord ++ tailWord_2243403).sum := by decide
  have hdescent : baseEnd_2243403 < baseStart_2243403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243460 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2243460 : Nat := 118140960795 + 2243460 * 2 ^ 59
def prefixEnd_2243460 : Nat := 4983230072969 + 3 ^ 40 * 2243460 * 2
def baseEnd_2243460 : Nat := 1151973309135897686132521

theorem tailTrace_2243460 : CollatzResearch.WordTrace tailWord_2243460 prefixEnd_2243460 1151973309135897686132521 := by
  unfold tailWord_2243460
  simp only [CollatzResearch.WordTrace]
  refine ⟨40912854226167523654391917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54550472301556698205855889 40912854226167523654391917)
  ·
    refine ⟨15342320334812821370396969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40912854226167523654391917 15342320334812821370396969)
    ·
      refine ⟨11506740251109616027797727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15342320334812821370396969 11506740251109616027797727)
      ·
        refine ⟨17260110376664424041696591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11506740251109616027797727 17260110376664424041696591)
        ·
          refine ⟨25890165564996636062544887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17260110376664424041696591 25890165564996636062544887)
          ·
            refine ⟨38835248347494954093817331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25890165564996636062544887 38835248347494954093817331)
            ·
              refine ⟨58252872521242431140725997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38835248347494954093817331 58252872521242431140725997)
              ·
                refine ⟨21844827195465911677772249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58252872521242431140725997 21844827195465911677772249)
                ·
                  refine ⟨16383620396599433758329187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21844827195465911677772249 16383620396599433758329187)
                  ·
                    refine ⟨24575430594899150637493781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16383620396599433758329187 24575430594899150637493781)
                    ·
                      refine ⟨1151973309135897686132521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24575430594899150637493781 1151973309135897686132521)
                      ·
                        rfl

theorem cell23_2243460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2243460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243460 prefixEnd_2243460 := by exact prefixLift 2243460
  have htrace : WordTrace (prefixWord ++ tailWord_2243460) baseStart_2243460 baseEnd_2243460 := by
    simpa [prefixWord, tailWord_2243460, baseEnd_2243460] using wordTrace_append hprefix tailTrace_2243460
  have hstable : (prefixWord ++ tailWord_2243460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243460).length < 2 ^ (prefixWord ++ tailWord_2243460).sum := by decide
  have hdescent : baseEnd_2243460 < baseStart_2243460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243467 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3]
def baseStart_2243467 : Nat := 118140960795 + 2243467 * 2 ^ 59
def prefixEnd_2243467 : Nat := 4983230072969 + 3 ^ 40 * 2243467 * 2
def baseEnd_2243467 : Nat := 1151976903500479158744989

theorem tailTrace_2243467 : CollatzResearch.WordTrace tailWord_2243467 prefixEnd_2243467 1151976903500479158744989 := by
  unfold tailWord_2243467
  simp only [CollatzResearch.WordTrace]
  refine ⟨81825963763309687504288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54550642508873125002859103 81825963763309687504288655)
  ·
    refine ⟨122738945644964531256432983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81825963763309687504288655 122738945644964531256432983)
    ·
      refine ⟨184108418467446796884649475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122738945644964531256432983 184108418467446796884649475)
      ·
        refine ⟨276162627701170195326974213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184108418467446796884649475 276162627701170195326974213)
        ·
          refine ⟨51780492693969411623807665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 276162627701170195326974213 51780492693969411623807665)
          ·
            refine ⟨38835369520477058717855749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51780492693969411623807665 38835369520477058717855749)
            ·
              refine ⟨7281631785089448509597953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38835369520477058717855749 7281631785089448509597953)
              ·
                refine ⟨5461223838817086382198465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7281631785089448509597953 5461223838817086382198465)
                ·
                  refine ⟨4095917879112814786648849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461223838817086382198465 4095917879112814786648849)
                  ·
                    refine ⟨3071938409334611089986637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4095917879112814786648849 3071938409334611089986637)
                    ·
                      refine ⟨1151976903500479158744989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071938409334611089986637 1151976903500479158744989)
                      ·
                        rfl

theorem cell23_2243467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 3].length) (baseStart_2243467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243467 prefixEnd_2243467 := by exact prefixLift 2243467
  have htrace : WordTrace (prefixWord ++ tailWord_2243467) baseStart_2243467 baseEnd_2243467 := by
    simpa [prefixWord, tailWord_2243467, baseEnd_2243467] using wordTrace_append hprefix tailTrace_2243467
  have hstable : (prefixWord ++ tailWord_2243467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243467).length < 2 ^ (prefixWord ++ tailWord_2243467).sum := by decide
  have hdescent : baseEnd_2243467 < baseStart_2243467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243487 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 6]
def baseStart_2243487 : Nat := 118140960795 + 2243487 * 2 ^ 59
def prefixEnd_2243487 : Nat := 4983230072969 + 3 ^ 40 * 2243487 * 2
def baseEnd_2243487 : Nat := 127998574790396564499433

theorem tailTrace_2243487 : CollatzResearch.WordTrace tailWord_2243487 prefixEnd_2243487 127998574790396564499433 := by
  unfold tailWord_2243487
  simp only [CollatzResearch.WordTrace]
  refine ⟨81826693223237230920016715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54551128815491487280011143 81826693223237230920016715)
  ·
    refine ⟨122740039834855846380025073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81826693223237230920016715 122740039834855846380025073)
    ·
      refine ⟨92055029876141884785018805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122740039834855846380025073 92055029876141884785018805)
      ·
        refine ⟨8630159050888301698595513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92055029876141884785018805 8630159050888301698595513)
        ·
          refine ⟨6472619288166226273946635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630159050888301698595513 6472619288166226273946635)
          ·
            refine ⟨9708928932249339410919953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472619288166226273946635 9708928932249339410919953)
            ·
              refine ⟨7281696699187004558189965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9708928932249339410919953 7281696699187004558189965)
              ·
                refine ⟨2730636262195126709321237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7281696699187004558189965 2730636262195126709321237)
                ·
                  refine ⟨127998574790396564499433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2730636262195126709321237 127998574790396564499433)
                  ·
                    rfl

theorem cell23_2243487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 6].length) (baseStart_2243487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243487 prefixEnd_2243487 := by exact prefixLift 2243487
  have htrace : WordTrace (prefixWord ++ tailWord_2243487) baseStart_2243487 baseEnd_2243487 := by
    simpa [prefixWord, tailWord_2243487, baseEnd_2243487] using wordTrace_append hprefix tailTrace_2243487
  have hstable : (prefixWord ++ tailWord_2243487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243487).length < 2 ^ (prefixWord ++ tailWord_2243487).sum := by decide
  have hdescent : baseEnd_2243487 < baseStart_2243487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243501 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2243501 : Nat := 118140960795 + 2243501 * 2 ^ 59
def prefixEnd_2243501 : Nat := 4983230072969 + 3 ^ 40 * 2243501 * 2
def baseEnd_2243501 : Nat := 1151994361842732025719833

theorem tailTrace_2243501 : CollatzResearch.WordTrace tailWord_2243501 prefixEnd_2243501 1151994361842732025719833 := by
  unfold tailWord_2243501
  simp only [CollatzResearch.WordTrace]
  refine ⟨81827203845186511311026357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54551469230124340874017571 81827203845186511311026357)
  ·
    refine ⟨7671300360486235435408721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81827203845186511311026357 7671300360486235435408721)
    ·
      refine ⟨5753475270364676576556541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7671300360486235435408721 5753475270364676576556541)
      ·
        refine ⟨2157553226386753716208703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5753475270364676576556541 2157553226386753716208703)
        ·
          refine ⟨3236329839580130574313055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157553226386753716208703 3236329839580130574313055)
          ·
            refine ⟨4854494759370195861469583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236329839580130574313055 4854494759370195861469583)
            ·
              refine ⟨7281742139055293792204375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4854494759370195861469583 7281742139055293792204375)
              ·
                refine ⟨10922613208582940688306563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7281742139055293792204375 10922613208582940688306563)
                ·
                  refine ⟨16383919812874411032459845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10922613208582940688306563 16383919812874411032459845)
                  ·
                    refine ⟨3071984964913952068586221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16383919812874411032459845 3071984964913952068586221)
                    ·
                      refine ⟨1151994361842732025719833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3071984964913952068586221 1151994361842732025719833)
                      ·
                        rfl

theorem cell23_2243501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2243501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243501 prefixEnd_2243501 := by exact prefixLift 2243501
  have htrace : WordTrace (prefixWord ++ tailWord_2243501) baseStart_2243501 baseEnd_2243501 := by
    simpa [prefixWord, tailWord_2243501, baseEnd_2243501] using wordTrace_append hprefix tailTrace_2243501
  have hstable : (prefixWord ++ tailWord_2243501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243501).length < 2 ^ (prefixWord ++ tailWord_2243501).sum := by decide
  have hdescent : baseEnd_2243501 < baseStart_2243501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243508 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2243508 : Nat := 118140960795 + 2243508 * 2 ^ 59
def prefixEnd_2243508 : Nat := 4983230072969 + 3 ^ 40 * 2243508 * 2
def baseEnd_2243508 : Nat := 383999318735771166110767

theorem tailTrace_2243508 : CollatzResearch.WordTrace tailWord_2243508 prefixEnd_2243508 383999318735771166110767 := by
  unfold tailWord_2243508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40913729578080575753265589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54551639437440767671020785 40913729578080575753265589)
  ·
    refine ⟨3835662147945053976868649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40913729578080575753265589 3835662147945053976868649)
    ·
      refine ⟨2876746610958790482651487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3835662147945053976868649 2876746610958790482651487)
      ·
        refine ⟨4315119916438185723977231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876746610958790482651487 4315119916438185723977231)
        ·
          refine ⟨6472679874657278585965847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315119916438185723977231 6472679874657278585965847)
          ·
            refine ⟨9709019811985917878948771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472679874657278585965847 9709019811985917878948771)
            ·
              refine ⟨14563529717978876818423157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709019811985917878948771 14563529717978876818423157)
              ·
                refine ⟨1365330911060519701727171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14563529717978876818423157 1365330911060519701727171)
                ·
                  refine ⟨2047996366590779552590757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365330911060519701727171 2047996366590779552590757)
                  ·
                    refine ⟨383999318735771166110767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047996366590779552590757 383999318735771166110767)
                    ·
                      rfl

theorem cell23_2243508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2243508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243508 prefixEnd_2243508 := by exact prefixLift 2243508
  have htrace : WordTrace (prefixWord ++ tailWord_2243508) baseStart_2243508 baseEnd_2243508 := by
    simpa [prefixWord, tailWord_2243508, baseEnd_2243508] using wordTrace_append hprefix tailTrace_2243508
  have hstable : (prefixWord ++ tailWord_2243508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243508).length < 2 ^ (prefixWord ++ tailWord_2243508).sum := by decide
  have hdescent : baseEnd_2243508 < baseStart_2243508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243531 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 1, 1, 3]
def baseStart_2243531 : Nat := 118140960795 + 2243531 * 2 ^ 59
def prefixEnd_2243531 : Nat := 4983230072969 + 3 ^ 40 * 2243531 * 2
def baseEnd_2243531 : Nat := 1152009766262366908344695

theorem tailTrace_2243531 : CollatzResearch.WordTrace tailWord_2243531 prefixEnd_2243531 1152009766262366908344695 := by
  unfold tailWord_2243531
  simp only [CollatzResearch.WordTrace]
  refine ⟨81828298035077826434618447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54552198690051884289745631 81828298035077826434618447)
  ·
    refine ⟨122742447052616739651927671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81828298035077826434618447 122742447052616739651927671)
    ·
      refine ⟨184113670578925109477891507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122742447052616739651927671 184113670578925109477891507)
      ·
        refine ⟨276170505868387664216837261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184113670578925109477891507 276170505868387664216837261)
        ·
          refine ⟨103563939700645374081313973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 276170505868387664216837261 103563939700645374081313973)
          ·
            refine ⟨9709119346935503820123185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103563939700645374081313973 9709119346935503820123185)
            ·
              refine ⟨7281839510201627865092389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9709119346935503820123185 7281839510201627865092389)
              ·
                refine ⟨1365344908162805224704823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7281839510201627865092389 1365344908162805224704823)
                ·
                  refine ⟨2048017362244207837057235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365344908162805224704823 2048017362244207837057235)
                  ·
                    refine ⟨3072026043366311755585853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048017362244207837057235 3072026043366311755585853)
                    ·
                      refine ⟨1152009766262366908344695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072026043366311755585853 1152009766262366908344695)
                      ·
                        rfl

theorem cell23_2243531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 1, 3].length) (baseStart_2243531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243531 prefixEnd_2243531 := by exact prefixLift 2243531
  have htrace : WordTrace (prefixWord ++ tailWord_2243531) baseStart_2243531 baseEnd_2243531 := by
    simpa [prefixWord, tailWord_2243531, baseEnd_2243531] using wordTrace_append hprefix tailTrace_2243531
  have hstable : (prefixWord ++ tailWord_2243531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243531).length < 2 ^ (prefixWord ++ tailWord_2243531).sum := by decide
  have hdescent : baseEnd_2243531 < baseStart_2243531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243574 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2243574 : Nat := 118140960795 + 2243574 * 2 ^ 59
def prefixEnd_2243574 : Nat := 4983230072969 + 3 ^ 40 * 2243574 * 2
def baseEnd_2243574 : Nat := 1152031845930510240106997

theorem tailTrace_2243574 : CollatzResearch.WordTrace tailWord_2243574 prefixEnd_2243574 1152031845930510240106997 := by
  unfold tailWord_2243574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114366648370127798652111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54553244249281363185622517 5114366648370127798652111)
  ·
    refine ⟨7671549972555191697978167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114366648370127798652111 7671549972555191697978167)
    ·
      refine ⟨11507324958832787546967251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671549972555191697978167 11507324958832787546967251)
      ·
        refine ⟨17260987438249181320450877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11507324958832787546967251 17260987438249181320450877)
        ·
          refine ⟨6472870289343442995169079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17260987438249181320450877 6472870289343442995169079)
          ·
            refine ⟨9709305434015164492753619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6472870289343442995169079 9709305434015164492753619)
            ·
              refine ⟨14563958151022746739130429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709305434015164492753619 14563958151022746739130429)
              ·
                refine ⟨5461484306633530027173911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14563958151022746739130429 5461484306633530027173911)
                ·
                  refine ⟨8192226459950295040760867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5461484306633530027173911 8192226459950295040760867)
                  ·
                    refine ⟨12288339689925442561141301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8192226459950295040760867 12288339689925442561141301)
                    ·
                      refine ⟨1152031845930510240106997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12288339689925442561141301 1152031845930510240106997)
                      ·
                        rfl

theorem cell23_2243574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2243574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243574 prefixEnd_2243574 := by exact prefixLift 2243574
  have htrace : WordTrace (prefixWord ++ tailWord_2243574) baseStart_2243574 baseEnd_2243574 := by
    simpa [prefixWord, tailWord_2243574, baseEnd_2243574] using wordTrace_append hprefix tailTrace_2243574
  have hstable : (prefixWord ++ tailWord_2243574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243574).length < 2 ^ (prefixWord ++ tailWord_2243574).sum := by decide
  have hdescent : baseEnd_2243574 < baseStart_2243574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243582 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2243582 : Nat := 118140960795 + 2243582 * 2 ^ 59
def prefixEnd_2243582 : Nat := 4983230072969 + 3 ^ 40 * 2243582 * 2
def baseEnd_2243582 : Nat := 1152035953775746208806961

theorem tailTrace_2243582 : CollatzResearch.WordTrace tailWord_2243582 prefixEnd_2243582 1152035953775746208806961 := by
  unfold tailWord_2243582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228769769736632768090625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54553438771928708096483333 10228769769736632768090625)
  ·
    refine ⟨7671577327302474576067969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10228769769736632768090625 7671577327302474576067969)
    ·
      refine ⟨5753682995476855932050977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7671577327302474576067969 5753682995476855932050977)
      ·
        refine ⟨4315262246607641949038233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5753682995476855932050977 4315262246607641949038233)
        ·
          refine ⟨3236446684955731461778675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315262246607641949038233 3236446684955731461778675)
          ·
            refine ⟨4854670027433597192668013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236446684955731461778675 4854670027433597192668013)
            ·
              refine ⟨1820501260287598947250505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854670027433597192668013 1820501260287598947250505)
              ·
                refine ⟨1365375945215699210437879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820501260287598947250505 1365375945215699210437879)
                ·
                  refine ⟨2048063917823548815656819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365375945215699210437879 2048063917823548815656819)
                  ·
                    refine ⟨3072095876735323223485229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048063917823548815656819 3072095876735323223485229)
                    ·
                      refine ⟨1152035953775746208806961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072095876735323223485229 1152035953775746208806961)
                      ·
                        rfl

theorem cell23_2243582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2243582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243582 prefixEnd_2243582 := by exact prefixLift 2243582
  have htrace : WordTrace (prefixWord ++ tailWord_2243582) baseStart_2243582 baseEnd_2243582 := by
    simpa [prefixWord, tailWord_2243582, baseEnd_2243582] using wordTrace_append hprefix tailTrace_2243582
  have hstable : (prefixWord ++ tailWord_2243582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243582).length < 2 ^ (prefixWord ++ tailWord_2243582).sum := by decide
  have hdescent : baseEnd_2243582 < baseStart_2243582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243598 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2243598 : Nat := 118140960795 + 2243598 * 2 ^ 59
def prefixEnd_2243598 : Nat := 4983230072969 + 3 ^ 40 * 2243598 * 2
def baseEnd_2243598 : Nat := 384014723155406048735629

theorem tailTrace_2243598 : CollatzResearch.WordTrace tailWord_2243598 prefixEnd_2243598 384014723155406048735629 := by
  unfold tailWord_2243598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228842715729387109663431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54553827817223397918204965 10228842715729387109663431)
  ·
    refine ⟨15343264073594080664495147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10228842715729387109663431 15343264073594080664495147)
    ·
      refine ⟨23014896110391120996742721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15343264073594080664495147 23014896110391120996742721)
      ·
        refine ⟨17261172082793340747557041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23014896110391120996742721 17261172082793340747557041)
        ·
          refine ⟨12945879062095005560667781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17261172082793340747557041 12945879062095005560667781)
          ·
            refine ⟨2427352324142813542625209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12945879062095005560667781 2427352324142813542625209)
            ·
              refine ⟨1820514243107110156968907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427352324142813542625209 1820514243107110156968907)
              ·
                refine ⟨2730771364660665235453361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820514243107110156968907 2730771364660665235453361)
                ·
                  refine ⟨2048078523495498926590021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730771364660665235453361 2048078523495498926590021)
                  ·
                    refine ⟨384014723155406048735629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048078523495498926590021 384014723155406048735629)
                    ·
                      rfl

theorem cell23_2243598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2243598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243598 prefixEnd_2243598 := by exact prefixLift 2243598
  have htrace : WordTrace (prefixWord ++ tailWord_2243598) baseStart_2243598 baseEnd_2243598 := by
    simpa [prefixWord, tailWord_2243598, baseEnd_2243598] using wordTrace_append hprefix tailTrace_2243598
  have hstable : (prefixWord ++ tailWord_2243598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243598).length < 2 ^ (prefixWord ++ tailWord_2243598).sum := by decide
  have hdescent : baseEnd_2243598 < baseStart_2243598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243602 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2243602 : Nat := 118140960795 + 2243602 * 2 ^ 59
def prefixEnd_2243602 : Nat := 4983230072969 + 3 ^ 40 * 2243602 * 2
def baseEnd_2243602 : Nat := 384015407796278710185623

theorem tailTrace_2243602 : CollatzResearch.WordTrace tailWord_2243602 prefixEnd_2243602 384015407796278710185623 := by
  unfold tailWord_2243602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457721904455151390113265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54553925078547070373635373 20457721904455151390113265)
  ·
    refine ⟨15343291428341363542584949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20457721904455151390113265 15343291428341363542584949)
    ·
      refine ⟨1438433571407002832117339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15343291428341363542584949 1438433571407002832117339)
      ·
        refine ⟨2157650357110504248176009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438433571407002832117339 2157650357110504248176009)
        ·
          refine ⟨1618237767832878186132007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157650357110504248176009 1618237767832878186132007)
          ·
            refine ⟨2427356651749317279198011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618237767832878186132007 2427356651749317279198011)
            ·
              refine ⟨3641034977623975918797017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427356651749317279198011 3641034977623975918797017)
              ·
                refine ⟨2730776233217981939097763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641034977623975918797017 2730776233217981939097763)
                ·
                  refine ⟨4096164349826972908646645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730776233217981939097763 4096164349826972908646645)
                  ·
                    refine ⟨384015407796278710185623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4096164349826972908646645 384015407796278710185623)
                    ·
                      rfl

theorem cell23_2243602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2243602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243602 prefixEnd_2243602 := by exact prefixLift 2243602
  have htrace : WordTrace (prefixWord ++ tailWord_2243602) baseStart_2243602 baseEnd_2243602 := by
    simpa [prefixWord, tailWord_2243602, baseEnd_2243602] using wordTrace_append hprefix tailTrace_2243602
  have hstable : (prefixWord ++ tailWord_2243602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243602).length < 2 ^ (prefixWord ++ tailWord_2243602).sum := by decide
  have hdescent : baseEnd_2243602 < baseStart_2243602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243637 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2243637 : Nat := 118140960795 + 2243637 * 2 ^ 59
def prefixEnd_2243637 : Nat := 4983230072969 + 3 ^ 40 * 2243637 * 2
def baseEnd_2243637 : Nat := 384021398403914497873069

theorem tailTrace_2243637 : CollatzResearch.WordTrace tailWord_2243637 prefixEnd_2243637 384021398403914497873069 := by
  unfold tailWord_2243637
  simp only [CollatzResearch.WordTrace]
  refine ⟨81832164172693806537977165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54554776115129204358651443 81832164172693806537977165)
  ·
    refine ⟨30687061564760177451741437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81832164172693806537977165 30687061564760177451741437)
    ·
      refine ⟨11507648086785066544403039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30687061564760177451741437 11507648086785066544403039)
      ·
        refine ⟨17261472130177599816604559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11507648086785066544403039 17261472130177599816604559)
        ·
          refine ⟨25892208195266399724906839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17261472130177599816604559 25892208195266399724906839)
          ·
            refine ⟨38838312292899599587360259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25892208195266399724906839 38838312292899599587360259)
            ·
              refine ⟨58257468439349399381040389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38838312292899599587360259 58257468439349399381040389)
              ·
                refine ⟨10923275332378012383945073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58257468439349399381040389 10923275332378012383945073)
                ·
                  refine ⟨8192456499283509287958805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10923275332378012383945073 8192456499283509287958805)
                  ·
                    refine ⟨384021398403914497873069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8192456499283509287958805 384021398403914497873069)
                    ·
                      rfl

theorem cell23_2243637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2243637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243637 prefixEnd_2243637 := by exact prefixLift 2243637
  have htrace : WordTrace (prefixWord ++ tailWord_2243637) baseStart_2243637 baseEnd_2243637 := by
    simpa [prefixWord, tailWord_2243637, baseEnd_2243637] using wordTrace_append hprefix tailTrace_2243637
  have hstable : (prefixWord ++ tailWord_2243637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243637).length < 2 ^ (prefixWord ++ tailWord_2243637).sum := by decide
  have hdescent : baseEnd_2243637 < baseStart_2243637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243638 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2243638 : Nat := 118140960795 + 2243638 * 2 ^ 59
def prefixEnd_2243638 : Nat := 4983230072969 + 3 ^ 40 * 2243638 * 2
def baseEnd_2243638 : Nat := 1152064708692397989706703

theorem tailTrace_2243638 : CollatzResearch.WordTrace tailWord_2243638 prefixEnd_2243638 1152064708692397989706703 := by
  unfold tailWord_2243638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114512540355636481797723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54554800430460122472509045 5114512540355636481797723)
  ·
    refine ⟨7671768810533454722696585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114512540355636481797723 7671768810533454722696585)
    ·
      refine ⟨5753826607900091042022439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7671768810533454722696585 5753826607900091042022439)
      ·
        refine ⟨8630739911850136563033659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5753826607900091042022439 8630739911850136563033659)
        ·
          refine ⟨12946109867775204844550489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8630739911850136563033659 12946109867775204844550489)
          ·
            refine ⟨9709582400831403633412867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12946109867775204844550489 9709582400831403633412867)
            ·
              refine ⟨14564373601247105450119301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9709582400831403633412867 14564373601247105450119301)
              ·
                refine ⟨2730820050233832271897369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14564373601247105450119301 2730820050233832271897369)
                ·
                  refine ⟨2048115037675374203923027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730820050233832271897369 2048115037675374203923027)
                  ·
                    refine ⟨3072172556513061305884541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048115037675374203923027 3072172556513061305884541)
                    ·
                      refine ⟨1152064708692397989706703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072172556513061305884541 1152064708692397989706703)
                      ·
                        rfl

theorem cell23_2243638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2243638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243638 prefixEnd_2243638 := by exact prefixLift 2243638
  have htrace : WordTrace (prefixWord ++ tailWord_2243638) baseStart_2243638 baseEnd_2243638 := by
    simpa [prefixWord, tailWord_2243638, baseEnd_2243638] using wordTrace_append hprefix tailTrace_2243638
  have hstable : (prefixWord ++ tailWord_2243638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243638).length < 2 ^ (prefixWord ++ tailWord_2243638).sum := by decide
  have hdescent : baseEnd_2243638 < baseStart_2243638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243682 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2243682 : Nat := 118140960795 + 2243682 * 2 ^ 59
def prefixEnd_2243682 : Nat := 4983230072969 + 3 ^ 40 * 2243682 * 2
def baseEnd_2243682 : Nat := 1152087301841195817556501

theorem tailTrace_2243682 : CollatzResearch.WordTrace tailWord_2243682 prefixEnd_2243682 1152087301841195817556501 := by
  unfold tailWord_2243682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458451364382694805841325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54555870305020519482243533 20458451364382694805841325)
  ·
    refine ⟨7671919261643510552190497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20458451364382694805841325 7671919261643510552190497)
    ·
      refine ⟨5753939446232632914142873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7671919261643510552190497 5753939446232632914142873)
      ·
        refine ⟨4315454584674474685607155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5753939446232632914142873 4315454584674474685607155)
        ·
          refine ⟨6473181877011712028410733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315454584674474685607155 6473181877011712028410733)
          ·
            refine ⟨2427443203879392010654025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6473181877011712028410733 2427443203879392010654025)
            ·
              refine ⟨1820582402909544007990519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427443203879392010654025 1820582402909544007990519)
              ·
                refine ⟨2730873604364316011985779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820582402909544007990519 2730873604364316011985779)
                ·
                  refine ⟨4096310406546474017978669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2730873604364316011985779 4096310406546474017978669)
                  ·
                    refine ⟨1536116402454927756742001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4096310406546474017978669 1536116402454927756742001)
                    ·
                      refine ⟨1152087301841195817556501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536116402454927756742001 1152087301841195817556501)
                      ·
                        rfl

theorem cell23_2243682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2243682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243682 prefixEnd_2243682 := by exact prefixLift 2243682
  have htrace : WordTrace (prefixWord ++ tailWord_2243682) baseStart_2243682 baseEnd_2243682 := by
    simpa [prefixWord, tailWord_2243682, baseEnd_2243682] using wordTrace_append hprefix tailTrace_2243682
  have hstable : (prefixWord ++ tailWord_2243682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243682).length < 2 ^ (prefixWord ++ tailWord_2243682).sum := by decide
  have hdescent : baseEnd_2243682 < baseStart_2243682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243704 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_2243704 : Nat := 118140960795 + 2243704 * 2 ^ 59
def prefixEnd_2243704 : Nat := 4983230072969 + 3 ^ 40 * 2243704 * 2
def baseEnd_2243704 : Nat := 1152098598415594731481399

theorem tailTrace_2243704 : CollatzResearch.WordTrace tailWord_2243704 prefixEnd_2243704 1152098598415594731481399 := by
  unfold tailWord_2243704
  simp only [CollatzResearch.WordTrace]
  refine ⟨40917303931725538490333083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54556405242300717987110777 40917303931725538490333083)
  ·
    refine ⟨61375955897588307735499625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40917303931725538490333083 61375955897588307735499625)
    ·
      refine ⟨46031966923191230801624719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61375955897588307735499625 46031966923191230801624719)
      ·
        refine ⟨69047950384786846202437079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46031966923191230801624719 69047950384786846202437079)
        ·
          refine ⟨103571925577180269303655619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69047950384786846202437079 103571925577180269303655619)
          ·
            refine ⟨155357888365770403955483429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103571925577180269303655619 155357888365770403955483429)
            ·
              refine ⟨29129604068581950741653143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155357888365770403955483429 29129604068581950741653143)
              ·
                refine ⟨43694406102872926112479715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29129604068581950741653143 43694406102872926112479715)
                ·
                  refine ⟨65541609154309389168719573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43694406102872926112479715 65541609154309389168719573)
                  ·
                    refine ⟨1536131464554126308641865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 65541609154309389168719573 1536131464554126308641865)
                    ·
                      refine ⟨1152098598415594731481399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536131464554126308641865 1152098598415594731481399)
                      ·
                        rfl

theorem cell23_2243704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_2243704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243704 prefixEnd_2243704 := by exact prefixLift 2243704
  have htrace : WordTrace (prefixWord ++ tailWord_2243704) baseStart_2243704 baseEnd_2243704 := by
    simpa [prefixWord, tailWord_2243704, baseEnd_2243704] using wordTrace_append hprefix tailTrace_2243704
  have hstable : (prefixWord ++ tailWord_2243704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243704).length < 2 ^ (prefixWord ++ tailWord_2243704).sum := by decide
  have hdescent : baseEnd_2243704 < baseStart_2243704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243707 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_2243707 : Nat := 118140960795 + 2243707 * 2 ^ 59
def prefixEnd_2243707 : Nat := 4983230072969 + 3 ^ 40 * 2243707 * 2
def baseEnd_2243707 : Nat := 1152100138857558219743885

theorem tailTrace_2243707 : CollatzResearch.WordTrace tailWord_2243707 prefixEnd_2243707 1152100138857558219743885 := by
  unfold tailWord_2243707
  simp only [CollatzResearch.WordTrace]
  refine ⟨81834717282440208493025375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54556478188293472328683583 81834717282440208493025375)
  ·
    refine ⟨122752075923660312739538063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81834717282440208493025375 122752075923660312739538063)
    ·
      refine ⟨184128113885490469109307095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122752075923660312739538063 184128113885490469109307095)
      ·
        refine ⟨276192170828235703663960643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184128113885490469109307095 276192170828235703663960643)
        ·
          refine ⟨414288256242353555495940965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276192170828235703663960643 414288256242353555495940965)
          ·
            refine ⟨77679048045441291655488931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 414288256242353555495940965 77679048045441291655488931)
            ·
              refine ⟨116518572068161937483233397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77679048045441291655488931 116518572068161937483233397)
              ·
                refine ⟨10923616131390181639053131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116518572068161937483233397 10923616131390181639053131)
                ·
                  refine ⟨16385424197085272458579697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10923616131390181639053131 16385424197085272458579697)
                  ·
                    refine ⟨12289068147813954343934773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16385424197085272458579697 12289068147813954343934773)
                    ·
                      refine ⟨1152100138857558219743885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12289068147813954343934773 1152100138857558219743885)
                      ·
                        rfl

theorem cell23_2243707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_2243707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243707 prefixEnd_2243707 := by exact prefixLift 2243707
  have htrace : WordTrace (prefixWord ++ tailWord_2243707) baseStart_2243707 baseEnd_2243707 := by
    simpa [prefixWord, tailWord_2243707, baseEnd_2243707] using wordTrace_append hprefix tailTrace_2243707
  have hstable : (prefixWord ++ tailWord_2243707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243707).length < 2 ^ (prefixWord ++ tailWord_2243707).sum := by decide
  have hdescent : baseEnd_2243707 < baseStart_2243707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243737 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_2243737 : Nat := 118140960795 + 2243737 * 2 ^ 59
def prefixEnd_2243737 : Nat := 4983230072969 + 3 ^ 40 * 2243737 * 2
def baseEnd_2243737 : Nat := 1152115543277193102368747

theorem tailTrace_2243737 : CollatzResearch.WordTrace tailWord_2243737 prefixEnd_2243737 1152115543277193102368747 := by
  unfold tailWord_2243737
  simp only [CollatzResearch.WordTrace]
  refine ⟨81835811472331523616617465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54557207648221015744411643 81835811472331523616617465)
  ·
    refine ⟨61376858604248642712463099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81835811472331523616617465 61376858604248642712463099)
    ·
      refine ⟨92065287906372964068694649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61376858604248642712463099 92065287906372964068694649)
      ·
        refine ⟨69048965929779723051520987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92065287906372964068694649 69048965929779723051520987)
        ·
          refine ⟨103573448894669584577281481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69048965929779723051520987 103573448894669584577281481)
          ·
            refine ⟨77680086671002188432961111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103573448894669584577281481 77680086671002188432961111)
            ·
              refine ⟨116520130006503282649441667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77680086671002188432961111 116520130006503282649441667)
              ·
                refine ⟨174780195009754923974162501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116520130006503282649441667 174780195009754923974162501)
                ·
                  refine ⟨32771286564329048245155469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174780195009754923974162501 32771286564329048245155469)
                  ·
                    refine ⟨12289232461623393091933301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32771286564329048245155469 12289232461623393091933301)
                    ·
                      refine ⟨1152115543277193102368747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12289232461623393091933301 1152115543277193102368747)
                      ·
                        rfl

theorem cell23_2243737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_2243737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243737 prefixEnd_2243737 := by exact prefixLift 2243737
  have htrace : WordTrace (prefixWord ++ tailWord_2243737) baseStart_2243737 baseEnd_2243737 := by
    simpa [prefixWord, tailWord_2243737, baseEnd_2243737] using wordTrace_append hprefix tailTrace_2243737
  have hstable : (prefixWord ++ tailWord_2243737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243737).length < 2 ^ (prefixWord ++ tailWord_2243737).sum := by decide
  have hdescent : baseEnd_2243737 < baseStart_2243737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243747 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2243747 : Nat := 118140960795 + 2243747 * 2 ^ 59
def prefixEnd_2243747 : Nat := 4983230072969 + 3 ^ 40 * 2243747 * 2
def baseEnd_2243747 : Nat := 1152120678083738063243701

theorem tailTrace_2243747 : CollatzResearch.WordTrace tailWord_2243747 prefixEnd_2243747 1152120678083738063243701 := by
  unfold tailWord_2243747
  simp only [CollatzResearch.WordTrace]
  refine ⟨81836176202295295324481495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54557450801530196882987663 81836176202295295324481495)
  ·
    refine ⟨122754264303442942986722243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81836176202295295324481495 122754264303442942986722243)
    ·
      refine ⟨184131396455164414480083365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122754264303442942986722243 184131396455164414480083365)
      ·
        refine ⟨34524636835343327715015631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184131396455164414480083365 34524636835343327715015631)
        ·
          refine ⟨51786955253014991572523447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34524636835343327715015631 51786955253014991572523447)
          ·
            refine ⟨77680432879522487358785171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51786955253014991572523447 77680432879522487358785171)
            ·
              refine ⟨116520649319283731038177757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77680432879522487358785171 116520649319283731038177757)
              ·
                refine ⟨43695243494731399139316659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116520649319283731038177757 43695243494731399139316659)
                ·
                  refine ⟨65542865242097098708974989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43695243494731399139316659 65542865242097098708974989)
                  ·
                    refine ⟨24578574465786412015865621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65542865242097098708974989 24578574465786412015865621)
                    ·
                      refine ⟨1152120678083738063243701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24578574465786412015865621 1152120678083738063243701)
                      ·
                        rfl

theorem cell23_2243747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2243747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243747 prefixEnd_2243747 := by exact prefixLift 2243747
  have htrace : WordTrace (prefixWord ++ tailWord_2243747) baseStart_2243747 baseEnd_2243747 := by
    simpa [prefixWord, tailWord_2243747, baseEnd_2243747] using wordTrace_append hprefix tailTrace_2243747
  have hstable : (prefixWord ++ tailWord_2243747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243747).length < 2 ^ (prefixWord ++ tailWord_2243747).sum := by decide
  have hdescent : baseEnd_2243747 < baseStart_2243747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243751 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2243751 : Nat := 118140960795 + 2243751 * 2 ^ 59
def prefixEnd_2243751 : Nat := 4983230072969 + 3 ^ 40 * 2243751 * 2
def baseEnd_2243751 : Nat := 1152122732006356047593683

theorem tailTrace_2243751 : CollatzResearch.WordTrace tailWord_2243751 prefixEnd_2243751 1152122732006356047593683 := by
  unfold tailWord_2243751
  simp only [CollatzResearch.WordTrace]
  refine ⟨81836322094280804007627107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54557548062853869338418071 81836322094280804007627107)
  ·
    refine ⟨122754483141421206011440661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81836322094280804007627107 122754483141421206011440661)
    ·
      refine ⟨5754116397254119031786281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122754483141421206011440661 5754116397254119031786281)
      ·
        refine ⟨4315587297940589273839711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5754116397254119031786281 4315587297940589273839711)
        ·
          refine ⟨6473380946910883910759567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315587297940589273839711 6473380946910883910759567)
          ·
            refine ⟨9710071420366325866139351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473380946910883910759567 9710071420366325866139351)
            ·
              refine ⟨14565107130549488799209027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710071420366325866139351 14565107130549488799209027)
              ·
                refine ⟨21847660695824233198813541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14565107130549488799209027 21847660695824233198813541)
                ·
                  refine ⟨4096436380467043724777539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21847660695824233198813541 4096436380467043724777539)
                  ·
                    refine ⟨6144654570700565587166309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4096436380467043724777539 6144654570700565587166309)
                    ·
                      refine ⟨1152122732006356047593683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6144654570700565587166309 1152122732006356047593683)
                      ·
                        rfl

theorem cell23_2243751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2243751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243751 prefixEnd_2243751 := by exact prefixLift 2243751
  have htrace : WordTrace (prefixWord ++ tailWord_2243751) baseStart_2243751 baseEnd_2243751 := by
    simpa [prefixWord, tailWord_2243751, baseEnd_2243751] using wordTrace_append hprefix tailTrace_2243751
  have hstable : (prefixWord ++ tailWord_2243751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243751).length < 2 ^ (prefixWord ++ tailWord_2243751).sum := by decide
  have hdescent : baseEnd_2243751 < baseStart_2243751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243782 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2243782 : Nat := 118140960795 + 2243782 * 2 ^ 59
def prefixEnd_2243782 : Nat := 4983230072969 + 3 ^ 40 * 2243782 * 2
def baseEnd_2243782 : Nat := 384046216635548475435347

theorem tailTrace_2243782 : CollatzResearch.WordTrace tailWord_2243782 prefixEnd_2243782 384046216635548475435347 := by
  unfold tailWord_2243782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557420398661515509437675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54558301838112330868003733 2557420398661515509437675)
  ·
    refine ⟨3836130597992273264156513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557420398661515509437675 3836130597992273264156513)
    ·
      refine ⟨2877097948494204948117385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3836130597992273264156513 2877097948494204948117385)
      ·
        refine ⟨2157823461370653711088039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2877097948494204948117385 2157823461370653711088039)
        ·
          refine ⟨3236735192055980566632059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157823461370653711088039 3236735192055980566632059)
          ·
            refine ⟨4855102788083970849948089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236735192055980566632059 4855102788083970849948089)
            ·
              refine ⟨3641327091062978137461067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855102788083970849948089 3641327091062978137461067)
              ·
                refine ⟨5461990636594467206191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641327091062978137461067 5461990636594467206191601)
                ·
                  refine ⟨4096492977445850404643701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5461990636594467206191601 4096492977445850404643701)
                  ·
                    refine ⟨384046216635548475435347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4096492977445850404643701 384046216635548475435347)
                    ·
                      rfl

theorem cell23_2243782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2243782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243782 prefixEnd_2243782 := by exact prefixLift 2243782
  have htrace : WordTrace (prefixWord ++ tailWord_2243782) baseStart_2243782 baseEnd_2243782 := by
    simpa [prefixWord, tailWord_2243782, baseEnd_2243782] using wordTrace_append hprefix tailTrace_2243782
  have hstable : (prefixWord ++ tailWord_2243782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243782).length < 2 ^ (prefixWord ++ tailWord_2243782).sum := by decide
  have hdescent : baseEnd_2243782 < baseStart_2243782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243784 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_2243784 : Nat := 118140960795 + 2243784 * 2 ^ 59
def prefixEnd_2243784 : Nat := 4983230072969 + 3 ^ 40 * 2243784 * 2
def baseEnd_2243784 : Nat := 1152139676867954418481031

theorem tailTrace_2243784 : CollatzResearch.WordTrace tailWord_2243784 prefixEnd_2243784 1152139676867954418481031 := by
  unfold tailWord_2243784
  simp only [CollatzResearch.WordTrace]
  refine ⟨40918762851580625321789203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54558350468774167095718937 40918762851580625321789203)
  ·
    refine ⟨61378144277370937982683805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40918762851580625321789203 61378144277370937982683805)
    ·
      refine ⟨23016804104014101743506427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61378144277370937982683805 23016804104014101743506427)
      ·
        refine ⟨34525206156021152615259641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23016804104014101743506427 34525206156021152615259641)
        ·
          refine ⟨25893904617015864461444731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34525206156021152615259641 25893904617015864461444731)
          ·
            refine ⟨38840856925523796692167097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25893904617015864461444731 38840856925523796692167097)
            ·
              refine ⟨29130642694142847519125323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38840856925523796692167097 29130642694142847519125323)
              ·
                refine ⟨43695964041214271278687985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29130642694142847519125323 43695964041214271278687985)
                ·
                  refine ⟨32771973030910703459015989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43695964041214271278687985 32771973030910703459015989)
                  ·
                    refine ⟨3072372471647878449282749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32771973030910703459015989 3072372471647878449282749)
                    ·
                      refine ⟨1152139676867954418481031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072372471647878449282749 1152139676867954418481031)
                      ·
                        rfl

theorem cell23_2243784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_2243784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243784 prefixEnd_2243784 := by exact prefixLift 2243784
  have htrace : WordTrace (prefixWord ++ tailWord_2243784) baseStart_2243784 baseEnd_2243784 := by
    simpa [prefixWord, tailWord_2243784, baseEnd_2243784] using wordTrace_append hprefix tailTrace_2243784
  have hstable : (prefixWord ++ tailWord_2243784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243784).length < 2 ^ (prefixWord ++ tailWord_2243784).sum := by decide
  have hdescent : baseEnd_2243784 < baseStart_2243784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243821 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2243821 : Nat := 118140960795 + 2243821 * 2 ^ 59
def prefixEnd_2243821 : Nat := 4983230072969 + 3 ^ 40 * 2243821 * 2
def baseEnd_2243821 : Nat := 384052891884056924572787

theorem tailTrace_2243821 : CollatzResearch.WordTrace tailWord_2243821 prefixEnd_2243821 384052891884056924572787 := by
  unfold tailWord_2243821
  simp only [CollatzResearch.WordTrace]
  refine ⟨81838875204027205962675317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54559250136018137308450211 81838875204027205962675317)
  ·
    refine ⟨7672394550377550559000811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81838875204027205962675317 7672394550377550559000811)
    ·
      refine ⟨11508591825566325838501217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672394550377550559000811 11508591825566325838501217)
      ·
        refine ⟨8631443869174744378875913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11508591825566325838501217 8631443869174744378875913)
        ·
          refine ⟨6473582901881058284156935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8631443869174744378875913 6473582901881058284156935)
          ·
            refine ⟨9710374352821587426235403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6473582901881058284156935 9710374352821587426235403)
            ·
              refine ⟨14565561529232381139353105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9710374352821587426235403 14565561529232381139353105)
              ·
                refine ⟨10924171146924285854514829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14565561529232381139353105 10924171146924285854514829)
                ·
                  refine ⟨4096564180096607195443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10924171146924285854514829 4096564180096607195443061)
                  ·
                    refine ⟨384052891884056924572787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4096564180096607195443061 384052891884056924572787)
                    ·
                      rfl

theorem cell23_2243821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2243821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243821 prefixEnd_2243821 := by exact prefixLift 2243821
  have htrace : WordTrace (prefixWord ++ tailWord_2243821) baseStart_2243821 baseEnd_2243821 := by
    simpa [prefixWord, tailWord_2243821, baseEnd_2243821] using wordTrace_append hprefix tailTrace_2243821
  have hstable : (prefixWord ++ tailWord_2243821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243821).length < 2 ^ (prefixWord ++ tailWord_2243821).sum := by decide
  have hdescent : baseEnd_2243821 < baseStart_2243821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243841 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2243841 : Nat := 118140960795 + 2243841 * 2 ^ 59
def prefixEnd_2243841 : Nat := 4983230072969 + 3 ^ 40 * 2243841 * 2
def baseEnd_2243841 : Nat := 1152168945265260695468269

theorem tailTrace_2243841 : CollatzResearch.WordTrace tailWord_2243841 prefixEnd_2243841 1152168945265260695468269 := by
  unfold tailWord_2243841
  simp only [CollatzResearch.WordTrace]
  refine ⟨81839604663954749378403377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54559736442636499585602251 81839604663954749378403377)
  ·
    refine ⟨61379703497966062033802533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81839604663954749378403377 61379703497966062033802533)
    ·
      refine ⟨11508694405868636631337975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61379703497966062033802533 11508694405868636631337975)
      ·
        refine ⟨17263041608802954947006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508694405868636631337975 17263041608802954947006963)
        ·
          refine ⟨25894562413204432420510445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17263041608802954947006963 25894562413204432420510445)
          ·
            refine ⟨9710460904951662157691417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25894562413204432420510445 9710460904951662157691417)
            ·
              refine ⟨7282845678713746618268563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9710460904951662157691417 7282845678713746618268563)
              ·
                refine ⟨10924268518070619927402845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7282845678713746618268563 10924268518070619927402845)
                ·
                  refine ⟨4096600694276482472776067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10924268518070619927402845 4096600694276482472776067)
                  ·
                    refine ⟨6144901041414723709164101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4096600694276482472776067 6144901041414723709164101)
                    ·
                      refine ⟨1152168945265260695468269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6144901041414723709164101 1152168945265260695468269)
                      ·
                        rfl

theorem cell23_2243841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2243841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243841 prefixEnd_2243841 := by exact prefixLift 2243841
  have htrace : WordTrace (prefixWord ++ tailWord_2243841) baseStart_2243841 baseEnd_2243841 := by
    simpa [prefixWord, tailWord_2243841, baseEnd_2243841] using wordTrace_append hprefix tailTrace_2243841
  have hstable : (prefixWord ++ tailWord_2243841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243841).length < 2 ^ (prefixWord ++ tailWord_2243841).sum := by decide
  have hdescent : baseEnd_2243841 < baseStart_2243841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243864 : List Nat := [2, 1, 2, 3, 1, 4, 10]
def baseStart_2243864 : Nat := 118140960795 + 2243864 * 2 ^ 59
def prefixEnd_2243864 : Nat := 4983230072969 + 3 ^ 40 * 2243864 * 2
def baseEnd_2243864 : Nat := 14224453769386593894823

theorem tailTrace_2243864 : CollatzResearch.WordTrace tailWord_2243864 prefixEnd_2243864 14224453769386593894823 := by
  unfold tailWord_2243864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40920221771435712153245323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54560295695247616204327097 40920221771435712153245323)
  ·
    refine ⟨61380332657153568229867985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40920221771435712153245323 61380332657153568229867985)
    ·
      refine ⟨46035249492865176172400989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61380332657153568229867985 46035249492865176172400989)
      ·
        refine ⟨17263218559824441064650371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46035249492865176172400989 17263218559824441064650371)
        ·
          refine ⟨25894827839736661596975557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17263218559824441064650371 25894827839736661596975557)
          ·
            refine ⟨4855280219950624049432917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25894827839736661596975557 4855280219950624049432917)
            ·
              refine ⟨14224453769386593894823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4855280219950624049432917 14224453769386593894823)
              ·
                rfl

theorem cell23_2243864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 10].length) (baseStart_2243864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243864 prefixEnd_2243864 := by exact prefixLift 2243864
  have htrace : WordTrace (prefixWord ++ tailWord_2243864) baseStart_2243864 baseEnd_2243864 := by
    simpa [prefixWord, tailWord_2243864, baseEnd_2243864] using wordTrace_append hprefix tailTrace_2243864
  have hstable : (prefixWord ++ tailWord_2243864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243864).length < 2 ^ (prefixWord ++ tailWord_2243864).sum := by decide
  have hdescent : baseEnd_2243864 < baseStart_2243864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243868 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2243868 : Nat := 118140960795 + 2243868 * 2 ^ 59
def prefixEnd_2243868 : Nat := 4983230072969 + 3 ^ 40 * 2243868 * 2
def baseEnd_2243868 : Nat := 384060936414310696610215

theorem tailTrace_2243868 : CollatzResearch.WordTrace tailWord_2243868 prefixEnd_2243868 384060936414310696610215 := by
  unfold tailWord_2243868
  simp only [CollatzResearch.WordTrace]
  refine ⟨40920294717428466494818129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54560392956571288659757505 40920294717428466494818129)
  ·
    refine ⟨30690221038071349871113597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40920294717428466494818129 30690221038071349871113597)
    ·
      refine ⟨11508832889276756201667599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30690221038071349871113597 11508832889276756201667599)
      ·
        refine ⟨17263249333915134302501399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508832889276756201667599 17263249333915134302501399)
        ·
          refine ⟨25894874000872701453752099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17263249333915134302501399 25894874000872701453752099)
          ·
            refine ⟨38842311001309052180628149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25894874000872701453752099 38842311001309052180628149)
            ·
              refine ⟨3641466656372723641933889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38842311001309052180628149 3641466656372723641933889)
              ·
                refine ⟨2731099992279542731450417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641466656372723641933889 2731099992279542731450417)
                ·
                  refine ⟨2048324994209657048587813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731099992279542731450417 2048324994209657048587813)
                  ·
                    refine ⟨384060936414310696610215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048324994209657048587813 384060936414310696610215)
                    ·
                      rfl

theorem cell23_2243868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2243868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243868 prefixEnd_2243868 := by exact prefixLift 2243868
  have htrace : WordTrace (prefixWord ++ tailWord_2243868) baseStart_2243868 baseEnd_2243868 := by
    simpa [prefixWord, tailWord_2243868, baseEnd_2243868] using wordTrace_append hprefix tailTrace_2243868
  have hstable : (prefixWord ++ tailWord_2243868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243868).length < 2 ^ (prefixWord ++ tailWord_2243868).sum := by decide
  have hdescent : baseEnd_2243868 < baseStart_2243868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243875 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 3, 2, 2]
def baseStart_2243875 : Nat := 118140960795 + 2243875 * 2 ^ 59
def prefixEnd_2243875 : Nat := 4983230072969 + 3 ^ 40 * 2243875 * 2
def baseEnd_2243875 : Nat := 1152186403607513562443113

theorem tailTrace_2243875 : CollatzResearch.WordTrace tailWord_2243875 prefixEnd_2243875 1152186403607513562443113 := by
  unfold tailWord_2243875
  simp only [CollatzResearch.WordTrace]
  refine ⟨81840844745831573185141079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54560563163887715456760719 81840844745831573185141079)
  ·
    refine ⟨122761267118747359777711619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81840844745831573185141079 122761267118747359777711619)
    ·
      refine ⟨184141900678121039666567429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122761267118747359777711619 184141900678121039666567429)
      ·
        refine ⟨34526606377147694937481393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184141900678121039666567429 34526606377147694937481393)
        ·
          refine ⟨25894954782860771203111045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34526606377147694937481393 25894954782860771203111045)
          ·
            refine ⟨4855304021786394600583321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25894954782860771203111045 4855304021786394600583321)
            ·
              refine ⟨3641478016339795950437491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855304021786394600583321 3641478016339795950437491)
              ·
                refine ⟨5462217024509693925656237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641478016339795950437491 5462217024509693925656237)
                ·
                  refine ⟨2048331384191135222121089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5462217024509693925656237 2048331384191135222121089)
                  ·
                    refine ⟨1536248538143351416590817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048331384191135222121089 1536248538143351416590817)
                    ·
                      refine ⟨1152186403607513562443113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536248538143351416590817 1152186403607513562443113)
                      ·
                        rfl

theorem cell23_2243875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_2243875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243875 prefixEnd_2243875 := by exact prefixLift 2243875
  have htrace : WordTrace (prefixWord ++ tailWord_2243875) baseStart_2243875 baseEnd_2243875 := by
    simpa [prefixWord, tailWord_2243875, baseEnd_2243875] using wordTrace_append hprefix tailTrace_2243875
  have hstable : (prefixWord ++ tailWord_2243875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243875).length < 2 ^ (prefixWord ++ tailWord_2243875).sum := by decide
  have hdescent : baseEnd_2243875 < baseStart_2243875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243885 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2243885 : Nat := 118140960795 + 2243885 * 2 ^ 59
def prefixEnd_2243885 : Nat := 4983230072969 + 3 ^ 40 * 2243885 * 2
def baseEnd_2243885 : Nat := 384063846138019507772689

theorem tailTrace_2243885 : CollatzResearch.WordTrace tailWord_2243885 prefixEnd_2243885 384063846138019507772689 := by
  unfold tailWord_2243885
  simp only [CollatzResearch.WordTrace]
  refine ⟨81841209475795344893005109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54560806317196896595336739 81841209475795344893005109)
  ·
    refine ⟨7672613388355813583719229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81841209475795344893005109 7672613388355813583719229)
    ·
      refine ⟨2877230020633430093894711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7672613388355813583719229 2877230020633430093894711)
      ·
        refine ⟨4315845030950145140842067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877230020633430093894711 4315845030950145140842067)
        ·
          refine ⟨6473767546425217711263101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315845030950145140842067 6473767546425217711263101)
          ·
            refine ⟨2427662829909456641723663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6473767546425217711263101 2427662829909456641723663)
            ·
              refine ⟨3641494244864184962585495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427662829909456641723663 3641494244864184962585495)
              ·
                refine ⟨5462241367296277443878243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641494244864184962585495 5462241367296277443878243)
                ·
                  refine ⟨8193362050944416165817365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5462241367296277443878243 8193362050944416165817365)
                  ·
                    refine ⟨384063846138019507772689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8193362050944416165817365 384063846138019507772689)
                    ·
                      rfl

theorem cell23_2243885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2243885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243885 prefixEnd_2243885 := by exact prefixLift 2243885
  have htrace : WordTrace (prefixWord ++ tailWord_2243885) baseStart_2243885 baseEnd_2243885 := by
    simpa [prefixWord, tailWord_2243885, baseEnd_2243885] using wordTrace_append hprefix tailTrace_2243885
  have hstable : (prefixWord ++ tailWord_2243885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243885).length < 2 ^ (prefixWord ++ tailWord_2243885).sum := by decide
  have hdescent : baseEnd_2243885 < baseStart_2243885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243904 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2243904 : Nat := 118140960795 + 2243904 * 2 ^ 59
def prefixEnd_2243904 : Nat := 4983230072969 + 3 ^ 40 * 2243904 * 2
def baseEnd_2243904 : Nat := 1152201294546493948980479

theorem tailTrace_2243904 : CollatzResearch.WordTrace tailWord_2243904 prefixEnd_2243904 1152201294546493948980479 := by
  unfold tailWord_2243904
  simp only [CollatzResearch.WordTrace]
  refine ⟨40920951231363255568973383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54561268308484340758631177 40920951231363255568973383)
  ·
    refine ⟨61381426847044883353460075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40920951231363255568973383 61381426847044883353460075)
    ·
      refine ⟨92072140270567325030190113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61381426847044883353460075 92072140270567325030190113)
      ·
        refine ⟨69054105202925493772642585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92072140270567325030190113 69054105202925493772642585)
        ·
          refine ⟨51790578902194120329481939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69054105202925493772642585 51790578902194120329481939)
          ·
            refine ⟨77685868353291180494222909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51790578902194120329481939 77685868353291180494222909)
            ·
              refine ⟨29132200632484192685333591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77685868353291180494222909 29132200632484192685333591)
              ·
                refine ⟨43698300948726289028000387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29132200632484192685333591 43698300948726289028000387)
                ·
                  refine ⟨65547451423089433542000581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43698300948726289028000387 65547451423089433542000581)
                  ·
                    refine ⟨12290147141829268789125109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65547451423089433542000581 12290147141829268789125109)
                    ·
                      refine ⟨1152201294546493948980479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12290147141829268789125109 1152201294546493948980479)
                      ·
                        rfl

theorem cell23_2243904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2243904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243904 prefixEnd_2243904 := by exact prefixLift 2243904
  have htrace : WordTrace (prefixWord ++ tailWord_2243904) baseStart_2243904 baseEnd_2243904 := by
    simpa [prefixWord, tailWord_2243904, baseEnd_2243904] using wordTrace_append hprefix tailTrace_2243904
  have hstable : (prefixWord ++ tailWord_2243904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243904).length < 2 ^ (prefixWord ++ tailWord_2243904).sum := by decide
  have hdescent : baseEnd_2243904 < baseStart_2243904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243914 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_2243914 : Nat := 118140960795 + 2243914 * 2 ^ 59
def prefixEnd_2243914 : Nat := 4983230072969 + 3 ^ 40 * 2243914 * 2
def baseEnd_2243914 : Nat := 1152206429353038909855433

theorem tailTrace_2243914 : CollatzResearch.WordTrace tailWord_2243914 prefixEnd_2243914 1152206429353038909855433 := by
  unfold tailWord_2243914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20460566798172570711452699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54561511461793521897207197 20460566798172570711452699)
  ·
    refine ⟨30690850197258856067179049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20460566798172570711452699 30690850197258856067179049)
    ·
      refine ⟨23018137647944142050384287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30690850197258856067179049 23018137647944142050384287)
      ·
        refine ⟨34527206471916213075576431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23018137647944142050384287 34527206471916213075576431)
        ·
          refine ⟨51790809707874319613364647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34527206471916213075576431 51790809707874319613364647)
          ·
            refine ⟨77686214561811479420046971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51790809707874319613364647 77686214561811479420046971)
            ·
              refine ⟨116529321842717219130070457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77686214561811479420046971 116529321842717219130070457)
              ·
                refine ⟨87396991382037914347552843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116529321842717219130070457 87396991382037914347552843)
                ·
                  refine ⟨131095487073056871521329265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87396991382037914347552843 131095487073056871521329265)
                  ·
                    refine ⟨98321615304792653640996949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131095487073056871521329265 98321615304792653640996949)
                    ·
                      refine ⟨1152206429353038909855433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 98321615304792653640996949 1152206429353038909855433)
                      ·
                        rfl

theorem cell23_2243914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_2243914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243914 prefixEnd_2243914 := by exact prefixLift 2243914
  have htrace : WordTrace (prefixWord ++ tailWord_2243914) baseStart_2243914 baseEnd_2243914 := by
    simpa [prefixWord, tailWord_2243914, baseEnd_2243914] using wordTrace_append hprefix tailTrace_2243914
  have hstable : (prefixWord ++ tailWord_2243914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243914).length < 2 ^ (prefixWord ++ tailWord_2243914).sum := by decide
  have hdescent : baseEnd_2243914 < baseStart_2243914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2243969 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2243969 : Nat := 118140960795 + 2243969 * 2 ^ 59
def prefixEnd_2243969 : Nat := 4983230072969 + 3 ^ 40 * 2243969 * 2
def baseEnd_2243969 : Nat := 1152234670789036194667681

theorem tailTrace_2243969 : CollatzResearch.WordTrace tailWord_2243969 prefixEnd_2243969 1152234670789036194667681 := by
  unfold tailWord_2243969
  simp only [CollatzResearch.WordTrace]
  refine ⟨81844273207491027239062961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54562848804994018159375307 81844273207491027239062961)
  ·
    refine ⟨61383204905618270429297221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81844273207491027239062961 61383204905618270429297221)
    ·
      refine ⟨11509350919803425705493229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61383204905618270429297221 11509350919803425705493229)
      ·
        refine ⟨4316006594926284639559961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11509350919803425705493229 4316006594926284639559961)
        ·
          refine ⟨3237004946194713479669971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316006594926284639559961 3237004946194713479669971)
          ·
            refine ⟨4855507419292070219504957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237004946194713479669971 4855507419292070219504957)
            ·
              refine ⟨1820815282234526332314359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4855507419292070219504957 1820815282234526332314359)
              ·
                refine ⟨2731222923351789498471539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820815282234526332314359 2731222923351789498471539)
                ·
                  refine ⟨4096834385027684247707309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731222923351789498471539 4096834385027684247707309)
                  ·
                    refine ⟨1536312894385381592890241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4096834385027684247707309 1536312894385381592890241)
                    ·
                      refine ⟨1152234670789036194667681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536312894385381592890241 1152234670789036194667681)
                      ·
                        rfl

theorem cell23_2243969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2243969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2243969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2243969 prefixEnd_2243969 := by exact prefixLift 2243969
  have htrace : WordTrace (prefixWord ++ tailWord_2243969) baseStart_2243969 baseEnd_2243969 := by
    simpa [prefixWord, tailWord_2243969, baseEnd_2243969] using wordTrace_append hprefix tailTrace_2243969
  have hstable : (prefixWord ++ tailWord_2243969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2243969).length < 2 ^ (prefixWord ++ tailWord_2243969).sum := by decide
  have hdescent : baseEnd_2243969 < baseStart_2243969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2243969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244058 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_2244058 : Nat := 118140960795 + 2244058 * 2 ^ 59
def prefixEnd_2244058 : Nat := 4983230072969 + 3 ^ 40 * 2244058 * 2
def baseEnd_2244058 : Nat := 1152280370567286346454771

theorem tailTrace_2244058 : CollatzResearch.WordTrace tailWord_2244058 prefixEnd_2244058 1152280370567286346454771 := by
  unfold tailWord_2244058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20461879826042148859763207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54565012869445730292701885 20461879826042148859763207)
  ·
    refine ⟨30692819739063223289644811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20461879826042148859763207 30692819739063223289644811)
    ·
      refine ⟨46039229608594834934467217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30692819739063223289644811 46039229608594834934467217)
      ·
        refine ⟨34529422206446126200850413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46039229608594834934467217 34529422206446126200850413)
        ·
          refine ⟨12948533327417297325318905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34529422206446126200850413 12948533327417297325318905)
          ·
            refine ⟨9711399995562972993989179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12948533327417297325318905 9711399995562972993989179)
            ·
              refine ⟨14567099993344459490983769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9711399995562972993989179 14567099993344459490983769)
              ·
                refine ⟨10925324995008344618237827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14567099993344459490983769 10925324995008344618237827)
                ·
                  refine ⟨16387987492512516927356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10925324995008344618237827 16387987492512516927356741)
                  ·
                    refine ⟨3072747654846096923879389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16387987492512516927356741 3072747654846096923879389)
                    ·
                      refine ⟨1152280370567286346454771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072747654846096923879389 1152280370567286346454771)
                      ·
                        rfl

theorem cell23_2244058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_2244058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244058 prefixEnd_2244058 := by exact prefixLift 2244058
  have htrace : WordTrace (prefixWord ++ tailWord_2244058) baseStart_2244058 baseEnd_2244058 := by
    simpa [prefixWord, tailWord_2244058, baseEnd_2244058] using wordTrace_append hprefix tailTrace_2244058
  have hstable : (prefixWord ++ tailWord_2244058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244058).length < 2 ^ (prefixWord ++ tailWord_2244058).sum := by decide
  have hdescent : baseEnd_2244058 < baseStart_2244058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244101 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_2244101 : Nat := 118140960795 + 2244101 * 2 ^ 59
def prefixEnd_2244101 : Nat := 4983230072969 + 3 ^ 40 * 2244101 * 2
def baseEnd_2244101 : Nat := 1152302450235429678217073

theorem tailTrace_2244101 : CollatzResearch.WordTrace tailWord_2244101 prefixEnd_2244101 1152302450235429678217073 := by
  unfold tailWord_2244101
  simp only [CollatzResearch.WordTrace]
  refine ⟨81849087643012813782868157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54566058428675209188578771 81849087643012813782868157)
  ·
    refine ⟨30693407866129805168575559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81849087643012813782868157 30693407866129805168575559)
    ·
      refine ⟨46040111799194707752863339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30693407866129805168575559 46040111799194707752863339)
      ·
        refine ⟨69060167698792061629295009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46040111799194707752863339 69060167698792061629295009)
        ·
          refine ⟨51795125774094046221971257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69060167698792061629295009 51795125774094046221971257)
          ·
            refine ⟨38846344330570534666478443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51795125774094046221971257 38846344330570534666478443)
            ·
              refine ⟨58269516495855801999717665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38846344330570534666478443 58269516495855801999717665)
              ·
                refine ⟨43702137371891851499788249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58269516495855801999717665 43702137371891851499788249)
                ·
                  refine ⟨32776603028918888624841187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43702137371891851499788249 32776603028918888624841187)
                  ·
                    refine ⟨49164904543378332937261781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32776603028918888624841187 49164904543378332937261781)
                    ·
                      refine ⟨1152302450235429678217073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49164904543378332937261781 1152302450235429678217073)
                      ·
                        rfl

theorem cell23_2244101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_2244101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244101 prefixEnd_2244101 := by exact prefixLift 2244101
  have htrace : WordTrace (prefixWord ++ tailWord_2244101) baseStart_2244101 baseEnd_2244101 := by
    simpa [prefixWord, tailWord_2244101, baseEnd_2244101] using wordTrace_append hprefix tailTrace_2244101
  have hstable : (prefixWord ++ tailWord_2244101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244101).length < 2 ^ (prefixWord ++ tailWord_2244101).sum := by decide
  have hdescent : baseEnd_2244101 < baseStart_2244101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244151 : List Nat := [1, 1, 3, 1, 2, 15]
def baseStart_2244151 : Nat := 118140960795 + 2244151 * 2 ^ 59
def prefixEnd_2244151 : Nat := 4983230072969 + 3 ^ 40 * 2244151 * 2
def baseEnd_2244151 : Nat := 4742091046371006101201

theorem tailTrace_2244151 : CollatzResearch.WordTrace tailWord_2244151 prefixEnd_2244151 4742091046371006101201 := by
  unfold tailWord_2244151
  simp only [CollatzResearch.WordTrace]
  refine ⟨81850911292831672322188307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54567274195221114881458871 81850911292831672322188307)
  ·
    refine ⟨122776366939247508483282461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81850911292831672322188307 122776366939247508483282461)
    ·
      refine ⟨46041137602217815681230923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122776366939247508483282461 46041137602217815681230923)
      ·
        refine ⟨69061706403326723521846385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46041137602217815681230923 69061706403326723521846385)
        ·
          refine ⟨51796279802495042641384789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69061706403326723521846385 51796279802495042641384789)
          ·
            refine ⟨4742091046371006101201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 51796279802495042641384789 4742091046371006101201)
            ·
              rfl

theorem cell23_2244151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 15].length) (baseStart_2244151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244151 prefixEnd_2244151 := by exact prefixLift 2244151
  have htrace : WordTrace (prefixWord ++ tailWord_2244151) baseStart_2244151 baseEnd_2244151 := by
    simpa [prefixWord, tailWord_2244151, baseEnd_2244151] using wordTrace_append hprefix tailTrace_2244151
  have hstable : (prefixWord ++ tailWord_2244151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244151).length < 2 ^ (prefixWord ++ tailWord_2244151).sum := by decide
  have hdescent : baseEnd_2244151 < baseStart_2244151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244195 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2244195 : Nat := 118140960795 + 2244195 * 2 ^ 59
def prefixEnd_2244195 : Nat := 4983230072969 + 3 ^ 40 * 2244195 * 2
def baseEnd_2244195 : Nat := 1152350717416952310441641

theorem tailTrace_2244195 : CollatzResearch.WordTrace tailWord_2244195 prefixEnd_2244195 1152350717416952310441641 := by
  unfold tailWord_2244195
  simp only [CollatzResearch.WordTrace]
  refine ⟨81852516104672267836790039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54568344069781511891193359 81852516104672267836790039)
  ·
    refine ⟨122778774157008401755185059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81852516104672267836790039 122778774157008401755185059)
    ·
      refine ⟨184168161235512602632777589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122778774157008401755185059 184168161235512602632777589)
      ·
        refine ⟨17265765115829306496822899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184168161235512602632777589 17265765115829306496822899)
        ·
          refine ⟨25898647673743959745234349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17265765115829306496822899 25898647673743959745234349)
          ·
            refine ⟨9711992877653984904462881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25898647673743959745234349 9711992877653984904462881)
            ·
              refine ⟨7283994658240488678347161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9711992877653984904462881 7283994658240488678347161)
              ·
                refine ⟨5462995993680366508760371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7283994658240488678347161 5462995993680366508760371)
                ·
                  refine ⟨8194493990520549763140557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5462995993680366508760371 8194493990520549763140557)
                  ·
                    refine ⟨3072935246445206161177709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8194493990520549763140557 3072935246445206161177709)
                    ·
                      refine ⟨1152350717416952310441641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072935246445206161177709 1152350717416952310441641)
                      ·
                        rfl

theorem cell23_2244195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2244195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244195 prefixEnd_2244195 := by exact prefixLift 2244195
  have htrace : WordTrace (prefixWord ++ tailWord_2244195) baseStart_2244195 baseEnd_2244195 := by
    simpa [prefixWord, tailWord_2244195, baseEnd_2244195] using wordTrace_append hprefix tailTrace_2244195
  have hstable : (prefixWord ++ tailWord_2244195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244195).length < 2 ^ (prefixWord ++ tailWord_2244195).sum := by decide
  have hdescent : baseEnd_2244195 < baseStart_2244195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244196 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_2244196 : Nat := 118140960795 + 2244196 * 2 ^ 59
def prefixEnd_2244196 : Nat := 4983230072969 + 3 ^ 40 * 2244196 * 2
def baseEnd_2244196 : Nat := 1152351230897606806529137

theorem tailTrace_2244196 : CollatzResearch.WordTrace tailWord_2244196 prefixEnd_2244196 1152351230897606806529137 := by
  unfold tailWord_2244196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40926276288834322503788221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54568368385112430005050961 40926276288834322503788221)
  ·
    refine ⟨15347353608312870938920583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40926276288834322503788221 15347353608312870938920583)
    ·
      refine ⟨23021030412469306408380875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347353608312870938920583 23021030412469306408380875)
      ·
        refine ⟨34531545618703959612571313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23021030412469306408380875 34531545618703959612571313)
        ·
          refine ⟨25898659214027969709428485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34531545618703959612571313 25898659214027969709428485)
          ·
            refine ⟨4855998602630244320517841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25898659214027969709428485 4855998602630244320517841)
            ·
              refine ⟨3641998951972683240388381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855998602630244320517841 3641998951972683240388381)
              ·
                refine ⟨1365749606989756215145643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3641998951972683240388381 1365749606989756215145643)
                ·
                  refine ⟨2048624410484634322718465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365749606989756215145643 2048624410484634322718465)
                  ·
                    refine ⟨1536468307863475742038849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048624410484634322718465 1536468307863475742038849)
                    ·
                      refine ⟨1152351230897606806529137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536468307863475742038849 1152351230897606806529137)
                      ·
                        rfl

theorem cell23_2244196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_2244196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244196 prefixEnd_2244196 := by exact prefixLift 2244196
  have htrace : WordTrace (prefixWord ++ tailWord_2244196) baseStart_2244196 baseEnd_2244196 := by
    simpa [prefixWord, tailWord_2244196, baseEnd_2244196] using wordTrace_append hprefix tailTrace_2244196
  have hstable : (prefixWord ++ tailWord_2244196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244196).length < 2 ^ (prefixWord ++ tailWord_2244196).sum := by decide
  have hdescent : baseEnd_2244196 < baseStart_2244196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244206 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2244206 : Nat := 118140960795 + 2244206 * 2 ^ 59
def prefixEnd_2244206 : Nat := 4983230072969 + 3 ^ 40 * 2244206 * 2
def baseEnd_2244206 : Nat := 384118788568050589134697

theorem tailTrace_2244206 : CollatzResearch.WordTrace tailWord_2244206 prefixEnd_2244206 384118788568050589134697 := by
  unfold tailWord_2244206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231614663454052089430059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54568611538421611143626981 10231614663454052089430059)
  ·
    refine ⟨15347421995181078134145089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10231614663454052089430059 15347421995181078134145089)
    ·
      refine ⟨11510566496385808600608817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15347421995181078134145089 11510566496385808600608817)
      ·
        refine ⟨8632924872289356450456613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11510566496385808600608817 8632924872289356450456613)
        ·
          refine ⟨1618673413554254334460615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8632924872289356450456613 1618673413554254334460615)
          ·
            refine ⟨2428010120331381501690923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618673413554254334460615 2428010120331381501690923)
            ·
              refine ⟨3642015180497072252536385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428010120331381501690923 3642015180497072252536385)
              ·
                refine ⟨2731511385372804189402289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3642015180497072252536385 2731511385372804189402289)
                ·
                  refine ⟨2048633539029603142051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731511385372804189402289 2048633539029603142051717)
                  ·
                    refine ⟨384118788568050589134697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048633539029603142051717 384118788568050589134697)
                    ·
                      rfl

theorem cell23_2244206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2244206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244206 prefixEnd_2244206 := by exact prefixLift 2244206
  have htrace : WordTrace (prefixWord ++ tailWord_2244206) baseStart_2244206 baseEnd_2244206 := by
    simpa [prefixWord, tailWord_2244206, baseEnd_2244206] using wordTrace_append hprefix tailTrace_2244206
  have hstable : (prefixWord ++ tailWord_2244206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244206).length < 2 ^ (prefixWord ++ tailWord_2244206).sum := by decide
  have hdescent : baseEnd_2244206 < baseStart_2244206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244218 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_2244218 : Nat := 118140960795 + 2244218 * 2 ^ 59
def prefixEnd_2244218 : Nat := 4983230072969 + 3 ^ 40 * 2244218 * 2
def baseEnd_2244218 : Nat := 1152362527472005720454035

theorem tailTrace_2244218 : CollatzResearch.WordTrace tailWord_2244218 prefixEnd_2244218 1152362527472005720454035 := by
  unfold tailWord_2244218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20463338745897235691219327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54568903322392628509918205 20463338745897235691219327)
  ·
    refine ⟨30695008118845853536828991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20463338745897235691219327 30695008118845853536828991)
    ·
      refine ⟨46042512178268780305243487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30695008118845853536828991 46042512178268780305243487)
      ·
        refine ⟨69063768267403170457865231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46042512178268780305243487 69063768267403170457865231)
        ·
          refine ⟨103595652401104755686797847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69063768267403170457865231 103595652401104755686797847)
          ·
            refine ⟨155393478601657133530196771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103595652401104755686797847 155393478601657133530196771)
            ·
              refine ⟨233090217902485700295295157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155393478601657133530196771 233090217902485700295295157)
              ·
                refine ⟨21852207928358034402683921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233090217902485700295295157 21852207928358034402683921)
                ·
                  refine ⟨16389155946268525802012941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21852207928358034402683921 16389155946268525802012941)
                  ·
                    refine ⟨6145933479850697175754853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16389155946268525802012941 6145933479850697175754853)
                    ·
                      refine ⟨1152362527472005720454035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6145933479850697175754853 1152362527472005720454035)
                      ·
                        rfl

theorem cell23_2244218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_2244218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244218 prefixEnd_2244218 := by exact prefixLift 2244218
  have htrace : WordTrace (prefixWord ++ tailWord_2244218) baseStart_2244218 baseEnd_2244218 := by
    simpa [prefixWord, tailWord_2244218, baseEnd_2244218] using wordTrace_append hprefix tailTrace_2244218
  have hstable : (prefixWord ++ tailWord_2244218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244218).length < 2 ^ (prefixWord ++ tailWord_2244218).sum := by decide
  have hdescent : baseEnd_2244218 < baseStart_2244218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244229 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_2244229 : Nat := 118140960795 + 2244229 * 2 ^ 59
def prefixEnd_2244229 : Nat := 4983230072969 + 3 ^ 40 * 2244229 * 2
def baseEnd_2244229 : Nat := 1152368175759205177416485

theorem tailTrace_2244229 : CollatzResearch.WordTrace tailWord_2244229 prefixEnd_2244229 1152368175759205177416485 := by
  unfold tailWord_2244229
  simp only [CollatzResearch.WordTrace]
  refine ⟨81853756186549091643527741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54569170791032727762351827 81853756186549091643527741)
  ·
    refine ⟨30695158569955909366322903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81853756186549091643527741 30695158569955909366322903)
    ·
      refine ⟨46042737854933864049484355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30695158569955909366322903 46042737854933864049484355)
      ·
        refine ⟨69064106782400796074226533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46042737854933864049484355 69064106782400796074226533)
        ·
          refine ⟨12949520021700149263917475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69064106782400796074226533 12949520021700149263917475)
          ·
            refine ⟨19424280032550223895876213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12949520021700149263917475 19424280032550223895876213)
            ·
              refine ⟨1821026253051583490238395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19424280032550223895876213 1821026253051583490238395)
              ·
                refine ⟨2731539379577375235357593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821026253051583490238395 2731539379577375235357593)
                ·
                  refine ⟨2048654534683031426518195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731539379577375235357593 2048654534683031426518195)
                  ·
                    refine ⟨3072981802024547139777293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048654534683031426518195 3072981802024547139777293)
                    ·
                      refine ⟨1152368175759205177416485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3072981802024547139777293 1152368175759205177416485)
                      ·
                        rfl

theorem cell23_2244229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_2244229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244229 prefixEnd_2244229 := by exact prefixLift 2244229
  have htrace : WordTrace (prefixWord ++ tailWord_2244229) baseStart_2244229 baseEnd_2244229 := by
    simpa [prefixWord, tailWord_2244229, baseEnd_2244229] using wordTrace_append hprefix tailTrace_2244229
  have hstable : (prefixWord ++ tailWord_2244229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244229).length < 2 ^ (prefixWord ++ tailWord_2244229).sum := by decide
  have hdescent : baseEnd_2244229 < baseStart_2244229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244269 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2244269 : Nat := 118140960795 + 2244269 * 2 ^ 59
def prefixEnd_2244269 : Nat := 4983230072969 + 3 ^ 40 * 2244269 * 2
def baseEnd_2244269 : Nat := 1152388714985385020916301

theorem tailTrace_2244269 : CollatzResearch.WordTrace tailWord_2244269 prefixEnd_2244269 1152388714985385020916301 := by
  unfold tailWord_2244269
  simp only [CollatzResearch.WordTrace]
  refine ⟨81855215106404178474983861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54570143404269452316655907 81855215106404178474983861)
  ·
    refine ⟨7673926416225391732029737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81855215106404178474983861 7673926416225391732029737)
    ·
      refine ⟨5755444812169043799022303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7673926416225391732029737 5755444812169043799022303)
      ·
        refine ⟨8633167218253565698533455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5755444812169043799022303 8633167218253565698533455)
        ·
          refine ⟨12949750827380348547800183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633167218253565698533455 12949750827380348547800183)
          ·
            refine ⟨19424626241070522821700275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12949750827380348547800183 19424626241070522821700275)
            ·
              refine ⟨29136939361605784232550413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19424626241070522821700275 29136939361605784232550413)
              ·
                refine ⟨10926352260602169087206405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29136939361605784232550413 10926352260602169087206405)
                ·
                  refine ⟨2048691048862906703851201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10926352260602169087206405 2048691048862906703851201)
                  ·
                    refine ⟨1536518286647180027888401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048691048862906703851201 1536518286647180027888401)
                    ·
                      refine ⟨1152388714985385020916301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536518286647180027888401 1152388714985385020916301)
                      ·
                        rfl

theorem cell23_2244269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2244269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244269 prefixEnd_2244269 := by exact prefixLift 2244269
  have htrace : WordTrace (prefixWord ++ tailWord_2244269) baseStart_2244269 baseEnd_2244269 := by
    simpa [prefixWord, tailWord_2244269, baseEnd_2244269] using wordTrace_append hprefix tailTrace_2244269
  have hstable : (prefixWord ++ tailWord_2244269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244269).length < 2 ^ (prefixWord ++ tailWord_2244269).sum := by decide
  have hdescent : baseEnd_2244269 < baseStart_2244269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244285 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2244285 : Nat := 118140960795 + 2244285 * 2 ^ 59
def prefixEnd_2244285 : Nat := 4983230072969 + 3 ^ 40 * 2244285 * 2
def baseEnd_2244285 : Nat := 1152396930675856958316227

theorem tailTrace_2244285 : CollatzResearch.WordTrace tailWord_2244285 prefixEnd_2244285 1152396930675856958316227 := by
  unfold tailWord_2244285
  simp only [CollatzResearch.WordTrace]
  refine ⟨81855798674346213207566309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54570532449564142138377539 81855798674346213207566309)
  ·
    refine ⟨15347962251439914976418683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81855798674346213207566309 15347962251439914976418683)
    ·
      refine ⟨23021943377159872464628025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347962251439914976418683 23021943377159872464628025)
      ·
        refine ⟨17266457532869904348471019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23021943377159872464628025 17266457532869904348471019)
        ·
          refine ⟨25899686299304856522706529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17266457532869904348471019 25899686299304856522706529)
          ·
            refine ⟨19424764724478642392029897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25899686299304856522706529 19424764724478642392029897)
            ·
              refine ⟨14568573543358981794022423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19424764724478642392029897 14568573543358981794022423)
              ·
                refine ⟨21852860315038472691033635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14568573543358981794022423 21852860315038472691033635)
                ·
                  refine ⟨32779290472557709036550453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21852860315038472691033635 32779290472557709036550453)
                  ·
                    refine ⟨3073058481802285222176605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32779290472557709036550453 3073058481802285222176605)
                    ·
                      refine ⟨1152396930675856958316227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073058481802285222176605 1152396930675856958316227)
                      ·
                        rfl

theorem cell23_2244285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2244285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244285 prefixEnd_2244285 := by exact prefixLift 2244285
  have htrace : WordTrace (prefixWord ++ tailWord_2244285) baseStart_2244285 baseEnd_2244285 := by
    simpa [prefixWord, tailWord_2244285, baseEnd_2244285] using wordTrace_append hprefix tailTrace_2244285
  have hstable : (prefixWord ++ tailWord_2244285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244285).length < 2 ^ (prefixWord ++ tailWord_2244285).sum := by decide
  have hdescent : baseEnd_2244285 < baseStart_2244285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244286 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_2244286 : Nat := 118140960795 + 2244286 * 2 ^ 59
def prefixEnd_2244286 : Nat := 4983230072969 + 3 ^ 40 * 2244286 * 2
def baseEnd_2244286 : Nat := 1152397444156511454403723

theorem tailTrace_2244286 : CollatzResearch.WordTrace tailWord_2244286 prefixEnd_2244286 1152397444156511454403723 := by
  unfold tailWord_2244286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231979393417823797294089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54570556764895060252235141 10231979393417823797294089)
  ·
    refine ⟨7673984545063367847970567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10231979393417823797294089 7673984545063367847970567)
    ·
      refine ⟨11510976817595051771955851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673984545063367847970567 11510976817595051771955851)
      ·
        refine ⟨17266465226392577657933777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11510976817595051771955851 17266465226392577657933777)
        ·
          refine ⟨12949848919794433243450333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17266465226392577657933777 12949848919794433243450333)
          ·
            refine ⟨4856193344922912466293875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12949848919794433243450333 4856193344922912466293875)
            ·
              refine ⟨7284290017384368699440813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856193344922912466293875 7284290017384368699440813)
              ·
                refine ⟨2731608756519138262290305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7284290017384368699440813 2731608756519138262290305)
                ·
                  refine ⟨2048706567389353696717729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731608756519138262290305 2048706567389353696717729)
                  ·
                    refine ⟨1536529925542015272538297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048706567389353696717729 1536529925542015272538297)
                    ·
                      refine ⟨1152397444156511454403723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536529925542015272538297 1152397444156511454403723)
                      ·
                        rfl

theorem cell23_2244286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_2244286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244286 prefixEnd_2244286 := by exact prefixLift 2244286
  have htrace : WordTrace (prefixWord ++ tailWord_2244286) baseStart_2244286 baseEnd_2244286 := by
    simpa [prefixWord, tailWord_2244286, baseEnd_2244286] using wordTrace_append hprefix tailTrace_2244286
  have hstable : (prefixWord ++ tailWord_2244286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244286).length < 2 ^ (prefixWord ++ tailWord_2244286).sum := by decide
  have hdescent : baseEnd_2244286 < baseStart_2244286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244305 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_2244305 : Nat := 118140960795 + 2244305 * 2 ^ 59
def prefixEnd_2244305 : Nat := 4983230072969 + 3 ^ 40 * 2244305 * 2
def baseEnd_2244305 : Nat := 384135733429648960022045

theorem tailTrace_2244305 : CollatzResearch.WordTrace tailWord_2244305 prefixEnd_2244305 384135733429648960022045 := by
  unfold tailWord_2244305
  simp only [CollatzResearch.WordTrace]
  refine ⟨81856528134273756623294369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54571018756182504415529579 81856528134273756623294369)
  ·
    refine ⟨61392396100705317467470777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81856528134273756623294369 61392396100705317467470777)
    ·
      refine ⟨46044297075528988100603083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61392396100705317467470777 46044297075528988100603083)
      ·
        refine ⟨69066445613293482150904625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46044297075528988100603083 69066445613293482150904625)
        ·
          refine ⟨51799834209970111613178469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69066445613293482150904625 51799834209970111613178469)
          ·
            refine ⟨9712468914369395927470963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51799834209970111613178469 9712468914369395927470963)
            ·
              refine ⟨14568703371554093891206445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9712468914369395927470963 14568703371554093891206445)
              ·
                refine ⟨5463263764332785209202417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14568703371554093891206445 5463263764332785209202417)
                ·
                  refine ⟨4097447823249588906901813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5463263764332785209202417 4097447823249588906901813)
                  ·
                    refine ⟨384135733429648960022045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4097447823249588906901813 384135733429648960022045)
                    ·
                      rfl

theorem cell23_2244305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_2244305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244305 prefixEnd_2244305 := by exact prefixLift 2244305
  have htrace : WordTrace (prefixWord ++ tailWord_2244305) baseStart_2244305 baseEnd_2244305 := by
    simpa [prefixWord, tailWord_2244305, baseEnd_2244305] using wordTrace_append hprefix tailTrace_2244305
  have hstable : (prefixWord ++ tailWord_2244305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244305).length < 2 ^ (prefixWord ++ tailWord_2244305).sum := by decide
  have hdescent : baseEnd_2244305 < baseStart_2244305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244362 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2244362 : Nat := 118140960795 + 2244362 * 2 ^ 59
def prefixEnd_2244362 : Nat := 4983230072969 + 3 ^ 40 * 2244362 * 2
def baseEnd_2244362 : Nat := 1152436468686253157053373

theorem tailTrace_2244362 : CollatzResearch.WordTrace tailWord_2244362 prefixEnd_2244362 1152436468686253157053373 := by
  unfold tailWord_2244362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20464651773766813839529835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54572404730044836905412893 20464651773766813839529835)
  ·
    refine ⟨30696977660650220759294753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20464651773766813839529835 30696977660650220759294753)
    ·
      refine ⟨23022733245487665569471065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30696977660650220759294753 23022733245487665569471065)
      ·
        refine ⟨17267049934115749177103299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23022733245487665569471065 17267049934115749177103299)
        ·
          refine ⟨25900574901173623765654949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267049934115749177103299 25900574901173623765654949)
          ·
            refine ⟨4856357793970054456060303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25900574901173623765654949 4856357793970054456060303)
            ·
              refine ⟨7284536690955081684090455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856357793970054456060303 7284536690955081684090455)
              ·
                refine ⟨10926805036432622526135683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284536690955081684090455 10926805036432622526135683)
                ·
                  refine ⟨16390207554648933789203525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10926805036432622526135683 16390207554648933789203525)
                  ·
                    refine ⟨3073163916496675085475661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16390207554648933789203525 3073163916496675085475661)
                    ·
                      refine ⟨1152436468686253157053373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073163916496675085475661 1152436468686253157053373)
                      ·
                        rfl

theorem cell23_2244362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2244362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244362 prefixEnd_2244362 := by exact prefixLift 2244362
  have htrace : WordTrace (prefixWord ++ tailWord_2244362) baseStart_2244362 baseEnd_2244362 := by
    simpa [prefixWord, tailWord_2244362, baseEnd_2244362] using wordTrace_append hprefix tailTrace_2244362
  have hstable : (prefixWord ++ tailWord_2244362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244362).length < 2 ^ (prefixWord ++ tailWord_2244362).sum := by decide
  have hdescent : baseEnd_2244362 < baseStart_2244362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244385 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2244385 : Nat := 118140960795 + 2244385 * 2 ^ 59
def prefixEnd_2244385 : Nat := 4983230072969 + 3 ^ 40 * 2244385 * 2
def baseEnd_2244385 : Nat := 1152448278741306567065767

theorem tailTrace_2244385 : CollatzResearch.WordTrace tailWord_2244385 prefixEnd_2244385 1152448278741306567065767 := by
  unfold tailWord_2244385
  simp only [CollatzResearch.WordTrace]
  refine ⟨81859445973983930286206609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54572963982655953524137739 81859445973983930286206609)
  ·
    refine ⟨61394584480487947714654957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81859445973983930286206609 61394584480487947714654957)
    ·
      refine ⟨23022969180182980392995609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61394584480487947714654957 23022969180182980392995609)
      ·
        refine ⟨17267226885137235294746707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23022969180182980392995609 17267226885137235294746707)
        ·
          refine ⟨25900840327705852942120061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267226885137235294746707 25900840327705852942120061)
          ·
            refine ⟨9712815122889694853295023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25900840327705852942120061 9712815122889694853295023)
            ·
              refine ⟨14569222684334542279942535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9712815122889694853295023 14569222684334542279942535)
              ·
                refine ⟨21853834026501813419913803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14569222684334542279942535 21853834026501813419913803)
                ·
                  refine ⟨32780751039752720129870705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21853834026501813419913803 32780751039752720129870705)
                  ·
                    refine ⟨24585563279814540097403029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32780751039752720129870705 24585563279814540097403029)
                    ·
                      refine ⟨1152448278741306567065767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24585563279814540097403029 1152448278741306567065767)
                      ·
                        rfl

theorem cell23_2244385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2244385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244385 prefixEnd_2244385 := by exact prefixLift 2244385
  have htrace : WordTrace (prefixWord ++ tailWord_2244385) baseStart_2244385 baseEnd_2244385 := by
    simpa [prefixWord, tailWord_2244385, baseEnd_2244385] using wordTrace_append hprefix tailTrace_2244385
  have hstable : (prefixWord ++ tailWord_2244385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244385).length < 2 ^ (prefixWord ++ tailWord_2244385).sum := by decide
  have hdescent : baseEnd_2244385 < baseStart_2244385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244412 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_2244412 : Nat := 118140960795 + 2244412 * 2 ^ 59
def prefixEnd_2244412 : Nat := 4983230072969 + 3 ^ 40 * 2244412 * 2
def baseEnd_2244412 : Nat := 384154047572992653809381

theorem tailTrace_2244412 : CollatzResearch.WordTrace tailWord_2244412 prefixEnd_2244412 384154047572992653809381 := by
  unfold tailWord_2244412
  simp only [CollatzResearch.WordTrace]
  refine ⟨40930215372443056948719745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54573620496590742598292993 40930215372443056948719745)
  ·
    refine ⟨30697661529332292711539809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40930215372443056948719745 30697661529332292711539809)
    ·
      refine ⟨23023246146999219533654857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30697661529332292711539809 23023246146999219533654857)
      ·
        refine ⟨17267434610249414650241143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23023246146999219533654857 17267434610249414650241143)
        ·
          refine ⟨25901151915374121975361715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17267434610249414650241143 25901151915374121975361715)
          ·
            refine ⟨38851727873061182963042573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25901151915374121975361715 38851727873061182963042573)
            ·
              refine ⟨14569397952397943611140965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38851727873061182963042573 14569397952397943611140965)
              ·
                refine ⟨2731762116074614427088931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14569397952397943611140965 2731762116074614427088931)
                ·
                  refine ⟨4097643174111921640633397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731762116074614427088931 4097643174111921640633397)
                  ·
                    refine ⟨384154047572992653809381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4097643174111921640633397 384154047572992653809381)
                    ·
                      rfl

theorem cell23_2244412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_2244412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244412 prefixEnd_2244412 := by exact prefixLift 2244412
  have htrace : WordTrace (prefixWord ++ tailWord_2244412) baseStart_2244412 baseEnd_2244412 := by
    simpa [prefixWord, tailWord_2244412, baseEnd_2244412] using wordTrace_append hprefix tailTrace_2244412
  have hstable : (prefixWord ++ tailWord_2244412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244412).length < 2 ^ (prefixWord ++ tailWord_2244412).sum := by decide
  have hdescent : baseEnd_2244412 < baseStart_2244412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244425 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_2244425 : Nat := 118140960795 + 2244425 * 2 ^ 59
def prefixEnd_2244425 : Nat := 4983230072969 + 3 ^ 40 * 2244425 * 2
def baseEnd_2244425 : Nat := 384156272655828803521861

theorem tailTrace_2244425 : CollatzResearch.WordTrace tailWord_2244425 prefixEnd_2244425 384156272655828803521861 := by
  unfold tailWord_2244425
  simp only [CollatzResearch.WordTrace]
  refine ⟨81860904893839017117662729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54573936595892678078441819 81860904893839017117662729)
  ·
    refine ⟨61395678670379262838247047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81860904893839017117662729 61395678670379262838247047)
    ·
      refine ⟨92093518005568894257370571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61395678670379262838247047 92093518005568894257370571)
      ·
        refine ⟨138140277008353341386055857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92093518005568894257370571 138140277008353341386055857)
        ·
          refine ⟨103605207756265006039541893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138140277008353341386055857 103605207756265006039541893)
          ·
            refine ⟨19425976454299688632414105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103605207756265006039541893 19425976454299688632414105)
            ·
              refine ⟨14569482340724766474310579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19425976454299688632414105 14569482340724766474310579)
              ·
                refine ⟨21854223511087149711465869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14569482340724766474310579 21854223511087149711465869)
                ·
                  refine ⟨8195333816657681141799701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21854223511087149711465869 8195333816657681141799701)
                  ·
                    refine ⟨384156272655828803521861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8195333816657681141799701 384156272655828803521861)
                    ·
                      rfl

theorem cell23_2244425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_2244425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244425 prefixEnd_2244425 := by exact prefixLift 2244425
  have htrace : WordTrace (prefixWord ++ tailWord_2244425) baseStart_2244425 baseEnd_2244425 := by
    simpa [prefixWord, tailWord_2244425, baseEnd_2244425] using wordTrace_append hprefix tailTrace_2244425
  have hstable : (prefixWord ++ tailWord_2244425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244425).length < 2 ^ (prefixWord ++ tailWord_2244425).sum := by decide
  have hdescent : baseEnd_2244425 < baseStart_2244425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244436 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_2244436 : Nat := 118140960795 + 2244436 * 2 ^ 59
def prefixEnd_2244436 : Nat := 4983230072969 + 3 ^ 40 * 2244436 * 2
def baseEnd_2244436 : Nat := 1152474466254685867528033

theorem tailTrace_2244436 : CollatzResearch.WordTrace tailWord_2244436 prefixEnd_2244436 1152474466254685867528033 := by
  unfold tailWord_2244436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40930653048399582998156581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54574204064532777330875441 40930653048399582998156581)
  ·
    refine ⟨7674497446574921812154359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40930653048399582998156581 7674497446574921812154359)
    ·
      refine ⟨11511746169862382718231539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7674497446574921812154359 11511746169862382718231539)
      ·
        refine ⟨17267619254793574077347309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11511746169862382718231539 17267619254793574077347309)
        ·
          refine ⟨6475357220547590279005241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17267619254793574077347309 6475357220547590279005241)
          ·
            refine ⟨4856517915410692709253931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475357220547590279005241 4856517915410692709253931)
            ·
              refine ⟨7284776873116039063880897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856517915410692709253931 7284776873116039063880897)
              ·
                refine ⟨5463582654837029297910673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7284776873116039063880897 5463582654837029297910673)
                ·
                  refine ⟨4097686991127771973433005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5463582654837029297910673 4097686991127771973433005)
                  ·
                    refine ⟨1536632621672914490037377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4097686991127771973433005 1536632621672914490037377)
                    ·
                      refine ⟨1152474466254685867528033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536632621672914490037377 1152474466254685867528033)
                      ·
                        rfl

theorem cell23_2244436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_2244436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244436 prefixEnd_2244436 := by exact prefixLift 2244436
  have htrace : WordTrace (prefixWord ++ tailWord_2244436) baseStart_2244436 baseEnd_2244436 := by
    simpa [prefixWord, tailWord_2244436, baseEnd_2244436] using wordTrace_append hprefix tailTrace_2244436
  have hstable : (prefixWord ++ tailWord_2244436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244436).length < 2 ^ (prefixWord ++ tailWord_2244436).sum := by decide
  have hdescent : baseEnd_2244436 < baseStart_2244436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244442 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_2244442 : Nat := 118140960795 + 2244442 * 2 ^ 59
def prefixEnd_2244442 : Nat := 4983230072969 + 3 ^ 40 * 2244442 * 2
def baseEnd_2244442 : Nat := 384159182379537614684335

theorem tailTrace_2244442 : CollatzResearch.WordTrace tailWord_2244442 prefixEnd_2244442 384159182379537614684335 := by
  unfold tailWord_2244442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20465381233694357255257895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54574349956518286014021053 20465381233694357255257895)
  ·
    refine ⟨30698071850541535882886843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20465381233694357255257895 30698071850541535882886843)
    ·
      refine ⟨46047107775812303824330265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30698071850541535882886843 46047107775812303824330265)
      ·
        refine ⟨34535330831859227868247699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46047107775812303824330265 34535330831859227868247699)
        ·
          refine ⟨51802996247788841802371549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34535330831859227868247699 51802996247788841802371549)
          ·
            refine ⟨19426123592920815675889331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51802996247788841802371549 19426123592920815675889331)
            ·
              refine ⟨29139185389381223513833997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19426123592920815675889331 29139185389381223513833997)
              ·
                refine ⟨10927194521017958817687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29139185389381223513833997 10927194521017958817687749)
                ·
                  refine ⟨2048848972690867278316453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10927194521017958817687749 2048848972690867278316453)
                  ·
                    refine ⟨384159182379537614684335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048848972690867278316453 384159182379537614684335)
                    ·
                      rfl

theorem cell23_2244442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_2244442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244442 prefixEnd_2244442 := by exact prefixLift 2244442
  have htrace : WordTrace (prefixWord ++ tailWord_2244442) baseStart_2244442 baseEnd_2244442 := by
    simpa [prefixWord, tailWord_2244442, baseEnd_2244442] using wordTrace_append hprefix tailTrace_2244442
  have hstable : (prefixWord ++ tailWord_2244442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244442).length < 2 ^ (prefixWord ++ tailWord_2244442).sum := by decide
  have hdescent : baseEnd_2244442 < baseStart_2244442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244469 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2244469 : Nat := 118140960795 + 2244469 * 2 ^ 59
def prefixEnd_2244469 : Nat := 4983230072969 + 3 ^ 40 * 2244469 * 2
def baseEnd_2244469 : Nat := 1152491411116284238415381

theorem tailTrace_2244469 : CollatzResearch.WordTrace tailWord_2244469 prefixEnd_2244469 1152491411116284238415381 := by
  unfold tailWord_2244469
  simp only [CollatzResearch.WordTrace]
  refine ⟨81862509705679612632264461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54575006470453075088176307 81862509705679612632264461)
  ·
    refine ⟨30698441139629854737099173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81862509705679612632264461 30698441139629854737099173)
    ·
      refine ⟨5755957713680597763206095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30698441139629854737099173 5755957713680597763206095)
      ·
        refine ⟨8633936570520896644809143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5755957713680597763206095 8633936570520896644809143)
        ·
          refine ⟨12950904855781344967213715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8633936570520896644809143 12950904855781344967213715)
          ·
            refine ⟨19426357283672017450820573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12950904855781344967213715 19426357283672017450820573)
            ·
              refine ⟨7284883981377006544057715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19426357283672017450820573 7284883981377006544057715)
              ·
                refine ⟨10927325972065509816086573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7284883981377006544057715 10927325972065509816086573)
                ·
                  refine ⟨4097747239524566181032465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10927325972065509816086573 4097747239524566181032465)
                  ·
                    refine ⟨3073310429643424635774349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4097747239524566181032465 3073310429643424635774349)
                    ·
                      refine ⟨1152491411116284238415381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073310429643424635774349 1152491411116284238415381)
                      ·
                        rfl

theorem cell23_2244469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2244469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244469 prefixEnd_2244469 := by exact prefixLift 2244469
  have htrace : WordTrace (prefixWord ++ tailWord_2244469) baseStart_2244469 baseEnd_2244469 := by
    simpa [prefixWord, tailWord_2244469, baseEnd_2244469] using wordTrace_append hprefix tailTrace_2244469
  have hstable : (prefixWord ++ tailWord_2244469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244469).length < 2 ^ (prefixWord ++ tailWord_2244469).sum := by decide
  have hdescent : baseEnd_2244469 < baseStart_2244469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244494 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2244494 : Nat := 118140960795 + 2244494 * 2 ^ 59
def prefixEnd_2244494 : Nat := 4983230072969 + 3 ^ 40 * 2244494 * 2
def baseEnd_2244494 : Nat := 1152504248132646640602767

theorem tailTrace_2244494 : CollatzResearch.WordTrace tailWord_2244494 prefixEnd_2244494 1152504248132646640602767 := by
  unfold tailWord_2244494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232927691323630237740567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54575614353726027934616357 10232927691323630237740567)
  ·
    refine ⟨15349391536985445356610851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10232927691323630237740567 15349391536985445356610851)
    ·
      refine ⟨23024087305478168034916277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15349391536985445356610851 23024087305478168034916277)
      ·
        refine ⟨2158508184888578253273401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23024087305478168034916277 2158508184888578253273401)
        ·
          refine ⟨1618881138666433689955051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2158508184888578253273401 1618881138666433689955051)
          ·
            refine ⟨2428321707999650534932577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618881138666433689955051 2428321707999650534932577)
            ·
              refine ⟨1821241280999737901199433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2428321707999650534932577 1821241280999737901199433)
              ·
                refine ⟨1365930960749803425899575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1821241280999737901199433 1365930960749803425899575)
                ·
                  refine ⟨2048896441124705138849363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365930960749803425899575 2048896441124705138849363)
                  ·
                    refine ⟨3073344661687057708274045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048896441124705138849363 3073344661687057708274045)
                    ·
                      refine ⟨1152504248132646640602767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073344661687057708274045 1152504248132646640602767)
                      ·
                        rfl

theorem cell23_2244494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2244494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244494 prefixEnd_2244494 := by exact prefixLift 2244494
  have htrace : WordTrace (prefixWord ++ tailWord_2244494) baseStart_2244494 baseEnd_2244494 := by
    simpa [prefixWord, tailWord_2244494, baseEnd_2244494] using wordTrace_append hprefix tailTrace_2244494
  have hstable : (prefixWord ++ tailWord_2244494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244494).length < 2 ^ (prefixWord ++ tailWord_2244494).sum := by decide
  have hdescent : baseEnd_2244494 < baseStart_2244494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_2244495 : Nat := 118140960795 + 2244495 * 2 ^ 59
def prefixEnd_2244495 : Nat := 4983230072969 + 3 ^ 40 * 2244495 * 2
def baseEnd_2244495 : Nat := 1152504761613301136690261

theorem tailTrace_2244495 : CollatzResearch.WordTrace tailWord_2244495 prefixEnd_2244495 1152504761613301136690261 := by
  unfold tailWord_2244495
  simp only [CollatzResearch.WordTrace]
  refine ⟨81863458003585419072710939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54575638669056946048473959 81863458003585419072710939)
  ·
    refine ⟨122795187005378128609066409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81863458003585419072710939 122795187005378128609066409)
    ·
      refine ⟨92096390254033596456799807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122795187005378128609066409 92096390254033596456799807)
      ·
        refine ⟨138144585381050394685199711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92096390254033596456799807 138144585381050394685199711)
        ·
          refine ⟨207216878071575592027799567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138144585381050394685199711 207216878071575592027799567)
          ·
            refine ⟨310825317107363388041699351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207216878071575592027799567 310825317107363388041699351)
            ·
              refine ⟨466237975661045082062549027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310825317107363388041699351 466237975661045082062549027)
              ·
                refine ⟨699356963491567623093823541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466237975661045082062549027 699356963491567623093823541)
                ·
                  refine ⟨65564715327334464665045957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 699356963491567623093823541 65564715327334464665045957)
                  ·
                    refine ⟨12293384123875212124696117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65564715327334464665045957 12293384123875212124696117)
                    ·
                      refine ⟨1152504761613301136690261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12293384123875212124696117 1152504761613301136690261)
                      ·
                        rfl

theorem cell23_2244495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_2244495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244495 prefixEnd_2244495 := by exact prefixLift 2244495
  have htrace : WordTrace (prefixWord ++ tailWord_2244495) baseStart_2244495 baseEnd_2244495 := by
    simpa [prefixWord, tailWord_2244495, baseEnd_2244495] using wordTrace_append hprefix tailTrace_2244495
  have hstable : (prefixWord ++ tailWord_2244495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244495).length < 2 ^ (prefixWord ++ tailWord_2244495).sum := by decide
  have hdescent : baseEnd_2244495 < baseStart_2244495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244500 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2244500 : Nat := 118140960795 + 2244500 * 2 ^ 59
def prefixEnd_2244500 : Nat := 4983230072969 + 3 ^ 40 * 2244500 * 2
def baseEnd_2244500 : Nat := 1152507329016573617127739

theorem tailTrace_2244500 : CollatzResearch.WordTrace tailWord_2244500 prefixEnd_2244500 1152507329016573617127739 := by
  unfold tailWord_2244500
  simp only [CollatzResearch.WordTrace]
  refine ⟨40931820184283652463321477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54575760245711536617761969 40931820184283652463321477)
  ·
    refine ⟨7674716284553184836872777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40931820184283652463321477 7674716284553184836872777)
    ·
      refine ⟨5756037213414888627654583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7674716284553184836872777 5756037213414888627654583)
      ·
        refine ⟨8634055820122332941481875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756037213414888627654583 8634055820122332941481875)
        ·
          refine ⟨12951083730183499412222813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634055820122332941481875 12951083730183499412222813)
          ·
            refine ⟨4856656398818812279583555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12951083730183499412222813 4856656398818812279583555)
            ·
              refine ⟨7284984598228218419375333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856656398818812279583555 7284984598228218419375333)
              ·
                refine ⟨1365934612167790953632875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7284984598228218419375333 1365934612167790953632875)
                ·
                  refine ⟨2048901918251686430449313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365934612167790953632875 2048901918251686430449313)
                  ·
                    refine ⟨1536676438688764822836985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2048901918251686430449313 1536676438688764822836985)
                    ·
                      refine ⟨1152507329016573617127739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536676438688764822836985 1152507329016573617127739)
                      ·
                        rfl

theorem cell23_2244500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2244500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244500 prefixEnd_2244500 := by exact prefixLift 2244500
  have htrace : WordTrace (prefixWord ++ tailWord_2244500) baseStart_2244500 baseEnd_2244500 := by
    simpa [prefixWord, tailWord_2244500, baseEnd_2244500] using wordTrace_append hprefix tailTrace_2244500
  have hstable : (prefixWord ++ tailWord_2244500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244500).length < 2 ^ (prefixWord ++ tailWord_2244500).sum := by decide
  have hdescent : baseEnd_2244500 < baseStart_2244500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244516 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_2244516 : Nat := 118140960795 + 2244516 * 2 ^ 59
def prefixEnd_2244516 : Nat := 4983230072969 + 3 ^ 40 * 2244516 * 2
def baseEnd_2244516 : Nat := 1152515544707045554527665

theorem tailTrace_2244516 : CollatzResearch.WordTrace tailWord_2244516 prefixEnd_2244516 1152515544707045554527665 := by
  unfold tailWord_2244516
  simp only [CollatzResearch.WordTrace]
  refine ⟨40932111968254669829612701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54576149291006226439483601 40932111968254669829612701)
  ·
    refine ⟨15349541988095501186104763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40932111968254669829612701 15349541988095501186104763)
    ·
      refine ⟨23024312982143251779157145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15349541988095501186104763 23024312982143251779157145)
      ·
        refine ⟨17268234736607438834367859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23024312982143251779157145 17268234736607438834367859)
        ·
          refine ⟨25902352104911158251551789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17268234736607438834367859 25902352104911158251551789)
          ·
            refine ⟨9713382039341684344331921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25902352104911158251551789 9713382039341684344331921)
            ·
              refine ⟨7285036529506263258248941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9713382039341684344331921 7285036529506263258248941)
              ·
                refine ⟨2731888698564848721843353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7285036529506263258248941 2731888698564848721843353)
                ·
                  refine ⟨2048916523923636541382515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731888698564848721843353 2048916523923636541382515)
                  ·
                    refine ⟨3073374785885454812073773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048916523923636541382515 3073374785885454812073773)
                    ·
                      refine ⟨1152515544707045554527665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073374785885454812073773 1152515544707045554527665)
                      ·
                        rfl

theorem cell23_2244516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_2244516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244516 prefixEnd_2244516 := by exact prefixLift 2244516
  have htrace : WordTrace (prefixWord ++ tailWord_2244516) baseStart_2244516 baseEnd_2244516 := by
    simpa [prefixWord, tailWord_2244516, baseEnd_2244516] using wordTrace_append hprefix tailTrace_2244516
  have hstable : (prefixWord ++ tailWord_2244516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244516).length < 2 ^ (prefixWord ++ tailWord_2244516).sum := by decide
  have hdescent : baseEnd_2244516 < baseStart_2244516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244592 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_2244592 : Nat := 118140960795 + 2244592 * 2 ^ 59
def prefixEnd_2244592 : Nat := 4983230072969 + 3 ^ 40 * 2244592 * 2
def baseEnd_2244592 : Nat := 384184856412262419059105

theorem tailTrace_2244592 : CollatzResearch.WordTrace tailWord_2244592 prefixEnd_2244592 384184856412262419059105 := by
  unfold tailWord_2244592
  simp only [CollatzResearch.WordTrace]
  refine ⟨40933497942117002319496015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54577997256156003092661353 40933497942117002319496015)
  ·
    refine ⟨61400246913175503479244023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40933497942117002319496015 61400246913175503479244023)
    ·
      refine ⟨92100370369763255218866035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61400246913175503479244023 92100370369763255218866035)
      ·
        refine ⟨138150555554644882828299053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92100370369763255218866035 138150555554644882828299053)
        ·
          refine ⟨51806458332991831060612145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138150555554644882828299053 51806458332991831060612145)
          ·
            refine ⟨38854843749743873295459109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51806458332991831060612145 38854843749743873295459109)
            ·
              refine ⟨7285283203076976242898583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38854843749743873295459109 7285283203076976242898583)
              ·
                refine ⟨10927924804615464364347875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285283203076976242898583 10927924804615464364347875)
                ·
                  refine ⟨16391887206923196546521813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10927924804615464364347875 16391887206923196546521813)
                  ·
                    refine ⟨384184856412262419059105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16391887206923196546521813 384184856412262419059105)
                    ·
                      rfl

theorem cell23_2244592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_2244592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244592 prefixEnd_2244592 := by exact prefixLift 2244592
  have htrace : WordTrace (prefixWord ++ tailWord_2244592) baseStart_2244592 baseEnd_2244592 := by
    simpa [prefixWord, tailWord_2244592, baseEnd_2244592] using wordTrace_append hprefix tailTrace_2244592
  have hstable : (prefixWord ++ tailWord_2244592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244592).length < 2 ^ (prefixWord ++ tailWord_2244592).sum := by decide
  have hdescent : baseEnd_2244592 < baseStart_2244592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244609 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2244609 : Nat := 118140960795 + 2244609 * 2 ^ 59
def prefixEnd_2244609 : Nat := 4983230072969 + 3 ^ 40 * 2244609 * 2
def baseEnd_2244609 : Nat := 384187766135971230221579

theorem tailTrace_2244609 : CollatzResearch.WordTrace tailWord_2244609 prefixEnd_2244609 384187766135971230221579 := by
  unfold tailWord_2244609
  simp only [CollatzResearch.WordTrace]
  refine ⟨81867615925172416542360881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54578410616781611028240587 81867615925172416542360881)
  ·
    refine ⟨61400711943879312406770661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81867615925172416542360881 61400711943879312406770661)
    ·
      refine ⟨11512633489477371076269499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61400711943879312406770661 11512633489477371076269499)
      ·
        refine ⟨17268950234216056614404249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11512633489477371076269499 17268950234216056614404249)
        ·
          refine ⟨12951712675662042460803187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17268950234216056614404249 12951712675662042460803187)
          ·
            refine ⟨19427569013493063691204781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12951712675662042460803187 19427569013493063691204781)
            ·
              refine ⟨7285338380059898884201793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19427569013493063691204781 7285338380059898884201793)
              ·
                refine ⟨5464003785044924163151345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285338380059898884201793 5464003785044924163151345)
                ·
                  refine ⟨4098002838783693122363509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5464003785044924163151345 4098002838783693122363509)
                  ·
                    refine ⟨384187766135971230221579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4098002838783693122363509 384187766135971230221579)
                    ·
                      rfl

theorem cell23_2244609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2244609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244609 prefixEnd_2244609 := by exact prefixLift 2244609
  have htrace : WordTrace (prefixWord ++ tailWord_2244609) baseStart_2244609 baseEnd_2244609 := by
    simpa [prefixWord, tailWord_2244609, baseEnd_2244609] using wordTrace_append hprefix tailTrace_2244609
  have hstable : (prefixWord ++ tailWord_2244609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244609).length < 2 ^ (prefixWord ++ tailWord_2244609).sum := by decide
  have hdescent : baseEnd_2244609 < baseStart_2244609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244639 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 5, 4]
def baseStart_2244639 : Nat := 118140960795 + 2244639 * 2 ^ 59
def prefixEnd_2244639 : Nat := 4983230072969 + 3 ^ 40 * 2244639 * 2
def baseEnd_2244639 : Nat := 384192900942516191096533

theorem tailTrace_2244639 : CollatzResearch.WordTrace tailWord_2244639 prefixEnd_2244639 384192900942516191096533 := by
  unfold tailWord_2244639
  simp only [CollatzResearch.WordTrace]
  refine ⟨81868710115063731665952971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54579140076709154443968647 81868710115063731665952971)
  ·
    refine ⟨122803065172595597498929457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81868710115063731665952971 122803065172595597498929457)
    ·
      refine ⟨92102298879446698124197093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122803065172595597498929457 92102298879446698124197093)
      ·
        refine ⟨17269181039896255898286955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92102298879446698124197093 17269181039896255898286955)
        ·
          refine ⟨25903771559844383847430433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17269181039896255898286955 25903771559844383847430433)
          ·
            refine ⟨19427828669883287885572825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25903771559844383847430433 19427828669883287885572825)
            ·
              refine ⟨14570871502412465914179619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19427828669883287885572825 14570871502412465914179619)
              ·
                refine ⟨21856307253618698871269429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14570871502412465914179619 21856307253618698871269429)
                ·
                  refine ⟨2049028805026753019181509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21856307253618698871269429 2049028805026753019181509)
                  ·
                    refine ⟨384192900942516191096533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049028805026753019181509 384192900942516191096533)
                    ·
                      rfl

theorem cell23_2244639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_2244639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244639 prefixEnd_2244639 := by exact prefixLift 2244639
  have htrace : WordTrace (prefixWord ++ tailWord_2244639) baseStart_2244639 baseEnd_2244639 := by
    simpa [prefixWord, tailWord_2244639, baseEnd_2244639] using wordTrace_append hprefix tailTrace_2244639
  have hstable : (prefixWord ++ tailWord_2244639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244639).length < 2 ^ (prefixWord ++ tailWord_2244639).sum := by decide
  have hdescent : baseEnd_2244639 < baseStart_2244639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244652 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 8]
def baseStart_2244652 : Nat := 118140960795 + 2244652 * 2 ^ 59
def prefixEnd_2244652 : Nat := 4983230072969 + 3 ^ 40 * 2244652 * 2
def baseEnd_2244652 : Nat := 128065042008450780269671

theorem tailTrace_2244652 : CollatzResearch.WordTrace tailWord_2244652 prefixEnd_2244652 128065042008450780269671 := by
  unfold tailWord_2244652
  simp only [CollatzResearch.WordTrace]
  refine ⟨40934592132008317443088105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54579456176011089924117473 40934592132008317443088105)
  ·
    refine ⟨30700944099006238082316079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40934592132008317443088105 30700944099006238082316079)
    ·
      refine ⟨46051416148509357123474119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30700944099006238082316079 46051416148509357123474119)
      ·
        refine ⟨69077124222764035685211179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46051416148509357123474119 69077124222764035685211179)
        ·
          refine ⟨103615686334146053527816769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69077124222764035685211179 103615686334146053527816769)
          ·
            refine ⟨77711764750609540145862577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103615686334146053527816769 77711764750609540145862577)
            ·
              refine ⟨58283823562957155109396933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77711764750609540145862577 58283823562957155109396933)
              ·
                refine ⟨10928216918054466583011925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58283823562957155109396933 10928216918054466583011925)
                ·
                  refine ⟨128065042008450780269671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10928216918054466583011925 128065042008450780269671)
                  ·
                    rfl

theorem cell23_2244652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_2244652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244652 prefixEnd_2244652 := by exact prefixLift 2244652
  have htrace : WordTrace (prefixWord ++ tailWord_2244652) baseStart_2244652 baseEnd_2244652 := by
    simpa [prefixWord, tailWord_2244652, baseEnd_2244652] using wordTrace_append hprefix tailTrace_2244652
  have hstable : (prefixWord ++ tailWord_2244652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244652).length < 2 ^ (prefixWord ++ tailWord_2244652).sum := by decide
  have hdescent : baseEnd_2244652 < baseStart_2244652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244696 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2244696 : Nat := 118140960795 + 2244696 * 2 ^ 59
def prefixEnd_2244696 : Nat := 4983230072969 + 3 ^ 40 * 2244696 * 2
def baseEnd_2244696 : Nat := 1152607971224854850276837

theorem tailTrace_2244696 : CollatzResearch.WordTrace tailWord_2244696 prefixEnd_2244696 1152607971224854850276837 := by
  unfold tailWord_2244696
  simp only [CollatzResearch.WordTrace]
  refine ⟨40935394537928615200388971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54580526050571486933851961 40935394537928615200388971)
  ·
    refine ⟨61403091806892922800583457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40935394537928615200388971 61403091806892922800583457)
    ·
      refine ⟨46052318855169692100437593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61403091806892922800583457 46052318855169692100437593)
      ·
        refine ⟨34539239141377269075328195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46052318855169692100437593 34539239141377269075328195)
        ·
          refine ⟨51808858712065903612992293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34539239141377269075328195 51808858712065903612992293)
          ·
            refine ⟨9714161008512356927436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51808858712065903612992293 9714161008512356927436055)
            ·
              refine ⟨14571241512768535391154083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714161008512356927436055 14571241512768535391154083)
              ·
                refine ⟨21856862269152803086731125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14571241512768535391154083 21856862269152803086731125)
                ·
                  refine ⟨2049080837733075289381043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21856862269152803086731125 2049080837733075289381043)
                  ·
                    refine ⟨3073621256599612934071565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049080837733075289381043 3073621256599612934071565)
                    ·
                      refine ⟨1152607971224854850276837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073621256599612934071565 1152607971224854850276837)
                      ·
                        rfl

theorem cell23_2244696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2244696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244696 prefixEnd_2244696 := by exact prefixLift 2244696
  have htrace : WordTrace (prefixWord ++ tailWord_2244696) baseStart_2244696 baseEnd_2244696 := by
    simpa [prefixWord, tailWord_2244696, baseEnd_2244696] using wordTrace_append hprefix tailTrace_2244696
  have hstable : (prefixWord ++ tailWord_2244696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244696).length < 2 ^ (prefixWord ++ tailWord_2244696).sum := by decide
  have hdescent : baseEnd_2244696 < baseStart_2244696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244716 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_2244716 : Nat := 118140960795 + 2244716 * 2 ^ 59
def prefixEnd_2244716 : Nat := 4983230072969 + 3 ^ 40 * 2244716 * 2
def baseEnd_2244716 : Nat := 384206080279314924008915

theorem tailTrace_2244716 : CollatzResearch.WordTrace tailWord_2244716 prefixEnd_2244716 384206080279314924008915 := by
  unfold tailWord_2244716
  simp only [CollatzResearch.WordTrace]
  refine ⟨40935759267892386908253001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54581012357189849211004001 40935759267892386908253001)
  ·
    refine ⟨30701819450919290181189751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40935759267892386908253001 30701819450919290181189751)
    ·
      refine ⟨46052729176378935271784627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30701819450919290181189751 46052729176378935271784627)
      ·
        refine ⟨69079093764568402907676941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46052729176378935271784627 69079093764568402907676941)
        ·
          refine ⟨25904660161713151090378853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69079093764568402907676941 25904660161713151090378853)
          ·
            refine ⟨4857123780321215829446035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25904660161713151090378853 4857123780321215829446035)
            ·
              refine ⟨7285685670481823744169053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857123780321215829446035 7285685670481823744169053)
              ·
                refine ⟨2732132126430683904063395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7285685670481823744169053 2732132126430683904063395)
                ·
                  refine ⟨4098198189646025856095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732132126430683904063395 4098198189646025856095093)
                  ·
                    refine ⟨384206080279314924008915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4098198189646025856095093 384206080279314924008915)
                    ·
                      rfl

theorem cell23_2244716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_2244716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244716 prefixEnd_2244716 := by exact prefixLift 2244716
  have htrace : WordTrace (prefixWord ++ tailWord_2244716) baseStart_2244716 baseEnd_2244716 := by
    simpa [prefixWord, tailWord_2244716, baseEnd_2244716] using wordTrace_append hprefix tailTrace_2244716
  have hstable : (prefixWord ++ tailWord_2244716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244716).length < 2 ^ (prefixWord ++ tailWord_2244716).sum := by decide
  have hdescent : baseEnd_2244716 < baseStart_2244716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244739 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5]
def baseStart_2244739 : Nat := 118140960795 + 2244739 * 2 ^ 59
def prefixEnd_2244739 : Nat := 4983230072969 + 3 ^ 40 * 2244739 * 2
def baseEnd_2244739 : Nat := 1152630050892998182039139

theorem tailTrace_2244739 : CollatzResearch.WordTrace tailWord_2244739 prefixEnd_2244739 1152630050892998182039139 := by
  unfold tailWord_2244739
  simp only [CollatzResearch.WordTrace]
  refine ⟨81872357414701448744593271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54581571609800965829728847 81872357414701448744593271)
  ·
    refine ⟨122808536122052173116889907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81872357414701448744593271 122808536122052173116889907)
    ·
      refine ⟨184212804183078259675334861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122808536122052173116889907 184212804183078259675334861)
      ·
        refine ⟨69079801568654347378250573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184212804183078259675334861 69079801568654347378250573)
        ·
          refine ⟨25904925588245380266843965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69079801568654347378250573 25904925588245380266843965)
          ·
            refine ⟨9714347095592017600066487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25904925588245380266843965 9714347095592017600066487)
            ·
              refine ⟨14571520643388026400099731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9714347095592017600066487 14571520643388026400099731)
              ·
                refine ⟨21857280965082039600149597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14571520643388026400099731 21857280965082039600149597)
                ·
                  refine ⟨8196480361905764850056099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21857280965082039600149597 8196480361905764850056099)
                  ·
                    refine ⟨12294720542858647275084149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8196480361905764850056099 12294720542858647275084149)
                    ·
                      refine ⟨1152630050892998182039139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12294720542858647275084149 1152630050892998182039139)
                      ·
                        rfl

theorem cell23_2244739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_2244739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244739 prefixEnd_2244739 := by exact prefixLift 2244739
  have htrace : WordTrace (prefixWord ++ tailWord_2244739) baseStart_2244739 baseEnd_2244739 := by
    simpa [prefixWord, tailWord_2244739, baseEnd_2244739] using wordTrace_append hprefix tailTrace_2244739
  have hstable : (prefixWord ++ tailWord_2244739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244739).length < 2 ^ (prefixWord ++ tailWord_2244739).sum := by decide
  have hdescent : baseEnd_2244739 < baseStart_2244739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244746 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_2244746 : Nat := 118140960795 + 2244746 * 2 ^ 59
def prefixEnd_2244746 : Nat := 4983230072969 + 3 ^ 40 * 2244746 * 2
def baseEnd_2244746 : Nat := 384211215085859884883869

theorem tailTrace_2244746 : CollatzResearch.WordTrace tailWord_2244746 prefixEnd_2244746 384211215085859884883869 := by
  unfold tailWord_2244746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20468153181419022235024523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54581741817117392626732061 20468153181419022235024523)
  ·
    refine ⟨30702229772128533352536785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20468153181419022235024523 30702229772128533352536785)
    ·
      refine ⟨23026672329096400014402589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30702229772128533352536785 23026672329096400014402589)
      ·
        refine ⟨8635002123411150005400971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23026672329096400014402589 8635002123411150005400971)
        ·
          refine ⟨12952503185116725008101457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635002123411150005400971 12952503185116725008101457)
          ·
            refine ⟨9714377388837543756076093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12952503185116725008101457 9714377388837543756076093)
            ·
              refine ⟨3642891520814078908528535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9714377388837543756076093 3642891520814078908528535)
              ·
                refine ⟨5464337281221118362792803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3642891520814078908528535 5464337281221118362792803)
                ·
                  refine ⟨8196505921831677544189205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464337281221118362792803 8196505921831677544189205)
                  ·
                    refine ⟨384211215085859884883869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8196505921831677544189205 384211215085859884883869)
                    ·
                      rfl

theorem cell23_2244746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_2244746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244746 prefixEnd_2244746 := by exact prefixLift 2244746
  have htrace : WordTrace (prefixWord ++ tailWord_2244746) baseStart_2244746 baseEnd_2244746 := by
    simpa [prefixWord, tailWord_2244746, baseEnd_2244746] using wordTrace_append hprefix tailTrace_2244746
  have hstable : (prefixWord ++ tailWord_2244746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244746).length < 2 ^ (prefixWord ++ tailWord_2244746).sum := by decide
  have hdescent : baseEnd_2244746 < baseStart_2244746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244758 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2244758 : Nat := 118140960795 + 2244758 * 2 ^ 59
def prefixEnd_2244758 : Nat := 4983230072969 + 3 ^ 40 * 2244758 * 2
def baseEnd_2244758 : Nat := 384213269008477869233851

theorem tailTrace_2244758 : CollatzResearch.WordTrace tailWord_2244758 prefixEnd_2244758 384213269008477869233851 := by
  unfold tailWord_2244758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117065650102038436845933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54582033601088409993023285 5117065650102038436845933)
  ·
    refine ⟨1918899618788264413817225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5117065650102038436845933 1918899618788264413817225)
    ·
      refine ⟨1439174714091198310362919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1918899618788264413817225 1439174714091198310362919)
      ·
        refine ⟨2158762071136797465544379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439174714091198310362919 2158762071136797465544379)
        ·
          refine ⟨3238143106705196198316569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158762071136797465544379 3238143106705196198316569)
          ·
            refine ⟨2428607330028897148737427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3238143106705196198316569 2428607330028897148737427)
            ·
              refine ⟨3642910995043345723106141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428607330028897148737427 3642910995043345723106141)
              ·
                refine ⟨1366091623141254646164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3642910995043345723106141 1366091623141254646164803)
                ·
                  refine ⟨2049137434711881969247205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366091623141254646164803 2049137434711881969247205)
                  ·
                    refine ⟨384213269008477869233851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049137434711881969247205 384213269008477869233851)
                    ·
                      rfl

theorem cell23_2244758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2244758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244758 prefixEnd_2244758 := by exact prefixLift 2244758
  have htrace : WordTrace (prefixWord ++ tailWord_2244758) baseStart_2244758 baseEnd_2244758 := by
    simpa [prefixWord, tailWord_2244758, baseEnd_2244758] using wordTrace_append hprefix tailTrace_2244758
  have hstable : (prefixWord ++ tailWord_2244758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244758).length < 2 ^ (prefixWord ++ tailWord_2244758).sum := by decide
  have hdescent : baseEnd_2244758 < baseStart_2244758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244809 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_2244809 : Nat := 118140960795 + 2244809 * 2 ^ 59
def prefixEnd_2244809 : Nat := 4983230072969 + 3 ^ 40 * 2244809 * 2
def baseEnd_2244809 : Nat := 1152665994538812908163817

theorem tailTrace_2244809 : CollatzResearch.WordTrace tailWord_2244809 prefixEnd_2244809 1152665994538812908163817 := by
  unfold tailWord_2244809
  simp only [CollatzResearch.WordTrace]
  refine ⟨81874910524447850699641481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54583273682965233799760987 81874910524447850699641481)
  ·
    refine ⟨61406182893335888024731111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81874910524447850699641481 61406182893335888024731111)
    ·
      refine ⟨92109274340003832037096667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61406182893335888024731111 92109274340003832037096667)
      ·
        refine ⟨138163911510005748055645001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92109274340003832037096667 138163911510005748055645001)
        ·
          refine ⟨103622933632504311041733751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138163911510005748055645001 103622933632504311041733751)
          ·
            refine ⟨155434400448756466562600627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103622933632504311041733751 155434400448756466562600627)
            ·
              refine ⟨233151600673134699843900941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155434400448756466562600627 233151600673134699843900941)
              ·
                refine ⟨87431850252425512441462853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233151600673134699843900941 87431850252425512441462853)
                ·
                  refine ⟨16393471922329783582774285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87431850252425512441462853 16393471922329783582774285)
                  ·
                    refine ⟨6147551970873668843540357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16393471922329783582774285 6147551970873668843540357)
                    ·
                      refine ⟨1152665994538812908163817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6147551970873668843540357 1152665994538812908163817)
                      ·
                        rfl

theorem cell23_2244809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_2244809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244809 prefixEnd_2244809 := by exact prefixLift 2244809
  have htrace : WordTrace (prefixWord ++ tailWord_2244809) baseStart_2244809 baseEnd_2244809 := by
    simpa [prefixWord, tailWord_2244809, baseEnd_2244809] using wordTrace_append hprefix tailTrace_2244809
  have hstable : (prefixWord ++ tailWord_2244809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244809).length < 2 ^ (prefixWord ++ tailWord_2244809).sum := by decide
  have hdescent : baseEnd_2244809 < baseStart_2244809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244860 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_2244860 : Nat := 118140960795 + 2244860 * 2 ^ 59
def prefixEnd_2244860 : Nat := 4983230072969 + 3 ^ 40 * 2244860 * 2
def baseEnd_2244860 : Nat := 1152692182052192208626083

theorem tailTrace_2244860 : CollatzResearch.WordTrace tailWord_2244860 prefixEnd_2244860 1152692182052192208626083 := by
  unfold tailWord_2244860
  simp only [CollatzResearch.WordTrace]
  refine ⟨40938385323631543204874017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54584513764842057606498689 40938385323631543204874017)
  ·
    refine ⟨30703788992723657403655513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40938385323631543204874017 30703788992723657403655513)
    ·
      refine ⟨23027841744542743052741635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30703788992723657403655513 23027841744542743052741635)
      ·
        refine ⟨34541762616814114579112453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23027841744542743052741635 34541762616814114579112453)
        ·
          refine ⟨6476580490652646483583585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34541762616814114579112453 6476580490652646483583585)
          ·
            refine ⟨4857435367989484862687689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6476580490652646483583585 4857435367989484862687689)
            ·
              refine ⟨3643076525992113647015767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857435367989484862687689 3643076525992113647015767)
              ·
                refine ⟨5464614788988170470523651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643076525992113647015767 5464614788988170470523651)
                ·
                  refine ⟨8196922183482255705785477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464614788988170470523651 8196922183482255705785477)
                  ·
                    refine ⟨1536922909402922944834777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8196922183482255705785477 1536922909402922944834777)
                    ·
                      refine ⟨1152692182052192208626083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536922909402922944834777 1152692182052192208626083)
                      ·
                        rfl

theorem cell23_2244860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_2244860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244860 prefixEnd_2244860 := by exact prefixLift 2244860
  have htrace : WordTrace (prefixWord ++ tailWord_2244860) baseStart_2244860 baseEnd_2244860 := by
    simpa [prefixWord, tailWord_2244860, baseEnd_2244860] using wordTrace_append hprefix tailTrace_2244860
  have hstable : (prefixWord ++ tailWord_2244860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244860).length < 2 ^ (prefixWord ++ tailWord_2244860).sum := by decide
  have hdescent : baseEnd_2244860 < baseStart_2244860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244876 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2244876 : Nat := 118140960795 + 2244876 * 2 ^ 59
def prefixEnd_2244876 : Nat := 4983230072969 + 3 ^ 40 * 2244876 * 2
def baseEnd_2244876 : Nat := 1152700397742664146026009

theorem tailTrace_2244876 : CollatzResearch.WordTrace tailWord_2244876 prefixEnd_2244876 1152700397742664146026009 := by
  unfold tailWord_2244876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40938677107602560571165241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54584902810136747428220321 40938677107602560571165241)
  ·
    refine ⟨30704007830701920428373931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40938677107602560571165241 30704007830701920428373931)
    ·
      refine ⟨46056011746052880642560897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30704007830701920428373931 46056011746052880642560897)
      ·
        refine ⟨34542008809539660481920673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46056011746052880642560897 34542008809539660481920673)
        ·
          refine ⟨25906506607154745361440505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34542008809539660481920673 25906506607154745361440505)
          ·
            refine ⟨19429879955366059021080379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25906506607154745361440505 19429879955366059021080379)
            ·
              refine ⟨29144819933049088531620569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19429879955366059021080379 29144819933049088531620569)
              ·
                refine ⟨21858614949786816398715427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29144819933049088531620569 21858614949786816398715427)
                ·
                  refine ⟨32787922424680224598073141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21858614949786816398715427 32787922424680224598073141)
                  ·
                    refine ⟨3073867727313771056069357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32787922424680224598073141 3073867727313771056069357)
                    ·
                      refine ⟨1152700397742664146026009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3073867727313771056069357 1152700397742664146026009)
                      ·
                        rfl

theorem cell23_2244876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2244876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244876 prefixEnd_2244876 := by exact prefixLift 2244876
  have htrace : WordTrace (prefixWord ++ tailWord_2244876) baseStart_2244876 baseEnd_2244876 := by
    simpa [prefixWord, tailWord_2244876, baseEnd_2244876] using wordTrace_append hprefix tailTrace_2244876
  have hstable : (prefixWord ++ tailWord_2244876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244876).length < 2 ^ (prefixWord ++ tailWord_2244876).sum := by decide
  have hdescent : baseEnd_2244876 < baseStart_2244876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244894 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2244894 : Nat := 118140960795 + 2244894 * 2 ^ 59
def prefixEnd_2244894 : Nat := 4983230072969 + 3 ^ 40 * 2244894 * 2
def baseEnd_2244894 : Nat := 1152709640394445075600927

theorem tailTrace_2244894 : CollatzResearch.WordTrace tailWord_2244894 prefixEnd_2244894 1152709640394445075600927 := by
  unfold tailWord_2244894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234751341142488777060717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54585340486093273477657157 10234751341142488777060717)
  ·
    refine ⟨3838031752928433291397769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10234751341142488777060717 3838031752928433291397769)
    ·
      refine ⟨2878523814696324968548327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3838031752928433291397769 2878523814696324968548327)
      ·
        refine ⟨4317785722044487452822491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878523814696324968548327 4317785722044487452822491)
        ·
          refine ⟨6476678583066731179233737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317785722044487452822491 6476678583066731179233737)
          ·
            refine ⟨4857508937300048384425303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6476678583066731179233737 4857508937300048384425303)
            ·
              refine ⟨7286263405950072576637955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4857508937300048384425303 7286263405950072576637955)
              ·
                refine ⟨10929395108925108864956933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7286263405950072576637955 10929395108925108864956933)
                ·
                  refine ⟨2049261582923457912179425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10929395108925108864956933 2049261582923457912179425)
                  ·
                    refine ⟨1536946187192593434134569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049261582923457912179425 1536946187192593434134569)
                    ·
                      refine ⟨1152709640394445075600927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1536946187192593434134569 1152709640394445075600927)
                      ·
                        rfl

theorem cell23_2244894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2244894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244894 prefixEnd_2244894 := by exact prefixLift 2244894
  have htrace : WordTrace (prefixWord ++ tailWord_2244894) baseStart_2244894 baseEnd_2244894 := by
    simpa [prefixWord, tailWord_2244894, baseEnd_2244894] using wordTrace_append hprefix tailTrace_2244894
  have hstable : (prefixWord ++ tailWord_2244894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244894).length < 2 ^ (prefixWord ++ tailWord_2244894).sum := by decide
  have hdescent : baseEnd_2244894 < baseStart_2244894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244946 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2244946 : Nat := 118140960795 + 2244946 * 2 ^ 59
def prefixEnd_2244946 : Nat := 4983230072969 + 3 ^ 40 * 2244946 * 2
def baseEnd_2244946 : Nat := 1152736341388478872150687

theorem tailTrace_2244946 : CollatzResearch.WordTrace tailWord_2244946 prefixEnd_2244946 1152736341388478872150687 := by
  unfold tailWord_2244946
  simp only [CollatzResearch.WordTrace]
  refine ⟨20469976831237880774344673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54586604883301015398252461 20469976831237880774344673)
  ·
    refine ⟨15352482623428410580758505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20469976831237880774344673 15352482623428410580758505)
    ·
      refine ⟨11514361967571307935568879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15352482623428410580758505 11514361967571307935568879)
      ·
        refine ⟨17271542951356961903353319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514361967571307935568879 17271542951356961903353319)
        ·
          refine ⟨25907314427035442855029979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17271542951356961903353319 25907314427035442855029979)
          ·
            refine ⟨38860971640553164282544969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25907314427035442855029979 38860971640553164282544969)
            ·
              refine ⟨29145728730414873211908727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38860971640553164282544969 29145728730414873211908727)
              ·
                refine ⟨43718593095622309817863091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29145728730414873211908727 43718593095622309817863091)
                ·
                  refine ⟨65577889643433464726794637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43718593095622309817863091 65577889643433464726794637)
                  ·
                    refine ⟨24591708616287549272547989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65577889643433464726794637 24591708616287549272547989)
                    ·
                      refine ⟨1152736341388478872150687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24591708616287549272547989 1152736341388478872150687)
                      ·
                        rfl

theorem cell23_2244946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2244946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244946 prefixEnd_2244946 := by exact prefixLift 2244946
  have htrace : WordTrace (prefixWord ++ tailWord_2244946) baseStart_2244946 baseEnd_2244946 := by
    simpa [prefixWord, tailWord_2244946, baseEnd_2244946] using wordTrace_append hprefix tailTrace_2244946
  have hstable : (prefixWord ++ tailWord_2244946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244946).length < 2 ^ (prefixWord ++ tailWord_2244946).sum := by decide
  have hdescent : baseEnd_2244946 < baseStart_2244946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2244973 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2244973 : Nat := 118140960795 + 2244973 * 2 ^ 59
def prefixEnd_2244973 : Nat := 4983230072969 + 3 ^ 40 * 2244973 * 2
def baseEnd_2244973 : Nat := 128083356151794474057007

theorem tailTrace_2244973 : CollatzResearch.WordTrace tailWord_2244973 prefixEnd_2244973 128083356151794474057007 := by
  unfold tailWord_2244973
  simp only [CollatzResearch.WordTrace]
  refine ⟨81880892095853706708611573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54587261397235804472407715 81880892095853706708611573)
  ·
    refine ⟨7676333633986285003932335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81880892095853706708611573 7676333633986285003932335)
    ·
      refine ⟨11514500450979427505898503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7676333633986285003932335 11514500450979427505898503)
      ·
        refine ⟨17271750676469141258847755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11514500450979427505898503 17271750676469141258847755)
        ·
          refine ⟨25907626014703711888271633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17271750676469141258847755 25907626014703711888271633)
          ·
            refine ⟨19430719511027783916203725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25907626014703711888271633 19430719511027783916203725)
            ·
              refine ⟨7286519816635418968576397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19430719511027783916203725 7286519816635418968576397)
              ·
                refine ⟨2732444931238282113216149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7286519816635418968576397 2732444931238282113216149)
                ·
                  refine ⟨128083356151794474057007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2732444931238282113216149 128083356151794474057007)
                  ·
                    rfl

theorem cell23_2244973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2244973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2244973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2244973 prefixEnd_2244973 := by exact prefixLift 2244973
  have htrace : WordTrace (prefixWord ++ tailWord_2244973) baseStart_2244973 baseEnd_2244973 := by
    simpa [prefixWord, tailWord_2244973, baseEnd_2244973] using wordTrace_append hprefix tailTrace_2244973
  have hstable : (prefixWord ++ tailWord_2244973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2244973).length < 2 ^ (prefixWord ++ tailWord_2244973).sum := by decide
  have hdescent : baseEnd_2244973 < baseStart_2244973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2244973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245017 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 1, 1, 3]
def baseStart_2245017 : Nat := 118140960795 + 2245017 * 2 ^ 59
def prefixEnd_2245017 : Nat := 4983230072969 + 3 ^ 40 * 2245017 * 2
def baseEnd_2245017 : Nat := 1152772798514948094362861

theorem tailTrace_2245017 : CollatzResearch.WordTrace tailWord_2245017 prefixEnd_2245017 1152772798514948094362861 := by
  unfold tailWord_2245017
  simp only [CollatzResearch.WordTrace]
  refine ⟨81882496907694302223213305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54588331271796201482142203 81882496907694302223213305)
  ·
    refine ⟨61411872680770726667409979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81882496907694302223213305 61411872680770726667409979)
    ·
      refine ⟨92117809021156090001114969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61411872680770726667409979 92117809021156090001114969)
      ·
        refine ⟨69088356765867067500836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92117809021156090001114969 69088356765867067500836227)
        ·
          refine ⟨103632535148800601251254341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69088356765867067500836227 103632535148800601251254341)
          ·
            refine ⟨19431100340400112734610189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103632535148800601251254341 19431100340400112734610189)
            ·
              refine ⟨7286662627650042275478821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19431100340400112734610189 7286662627650042275478821)
              ·
                refine ⟨1366249242684382926652279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7286662627650042275478821 1366249242684382926652279)
                ·
                  refine ⟨2049373864026574389978419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366249242684382926652279 2049373864026574389978419)
                  ·
                    refine ⟨3074060796039861584967629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049373864026574389978419 3074060796039861584967629)
                    ·
                      refine ⟨1152772798514948094362861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074060796039861584967629 1152772798514948094362861)
                      ·
                        rfl

theorem cell23_2245017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_2245017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245017 prefixEnd_2245017 := by exact prefixLift 2245017
  have htrace : WordTrace (prefixWord ++ tailWord_2245017) baseStart_2245017 baseEnd_2245017 := by
    simpa [prefixWord, tailWord_2245017, baseEnd_2245017] using wordTrace_append hprefix tailTrace_2245017
  have hstable : (prefixWord ++ tailWord_2245017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245017).length < 2 ^ (prefixWord ++ tailWord_2245017).sum := by decide
  have hdescent : baseEnd_2245017 < baseStart_2245017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245023 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2245023 : Nat := 118140960795 + 2245023 * 2 ^ 59
def prefixEnd_2245023 : Nat := 4983230072969 + 3 ^ 40 * 2245023 * 2
def baseEnd_2245023 : Nat := 1152775879398875070887833

theorem tailTrace_2245023 : CollatzResearch.WordTrace tailWord_2245023 prefixEnd_2245023 1152775879398875070887833 := by
  unfold tailWord_2245023
  simp only [CollatzResearch.WordTrace]
  refine ⟨81882715745672565247931723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54588477163781710165287815 81882715745672565247931723)
  ·
    refine ⟨122824073618508847871897585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81882715745672565247931723 122824073618508847871897585)
    ·
      refine ⟨92118055213881635903923189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122824073618508847871897585 92118055213881635903923189)
      ·
        refine ⟨8636067676301403365992799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92118055213881635903923189 8636067676301403365992799)
        ·
          refine ⟨12954101514452105048989199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8636067676301403365992799 12954101514452105048989199)
          ·
            refine ⟨19431152271678157573483799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12954101514452105048989199 19431152271678157573483799)
            ·
              refine ⟨29146728407517236360225699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19431152271678157573483799 29146728407517236360225699)
              ·
                refine ⟨43720092611275854540338549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29146728407517236360225699 43720092611275854540338549)
                ·
                  refine ⟨4098758682307111363156739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43720092611275854540338549 4098758682307111363156739)
                  ·
                    refine ⟨6148138023460667044735109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4098758682307111363156739 6148138023460667044735109)
                    ·
                      refine ⟨1152775879398875070887833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6148138023460667044735109 1152775879398875070887833)
                      ·
                        rfl

theorem cell23_2245023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2245023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245023 prefixEnd_2245023 := by exact prefixLift 2245023
  have htrace : WordTrace (prefixWord ++ tailWord_2245023) baseStart_2245023 baseEnd_2245023 := by
    simpa [prefixWord, tailWord_2245023, baseEnd_2245023] using wordTrace_append hprefix tailTrace_2245023
  have hstable : (prefixWord ++ tailWord_2245023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245023).length < 2 ^ (prefixWord ++ tailWord_2245023).sum := by decide
  have hdescent : baseEnd_2245023 < baseStart_2245023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245073 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_2245073 : Nat := 118140960795 + 2245073 * 2 ^ 59
def prefixEnd_2245073 : Nat := 4983230072969 + 3 ^ 40 * 2245073 * 2
def baseEnd_2245073 : Nat := 1152801553431599875262603

theorem tailTrace_2245073 : CollatzResearch.WordTrace tailWord_2245073 prefixEnd_2245073 1152801553431599875262603 := by
  unfold tailWord_2245073
  simp only [CollatzResearch.WordTrace]
  refine ⟨81884539395491423787251873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54589692930327615858167915 81884539395491423787251873)
  ·
    refine ⟨61413404546618567840438905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81884539395491423787251873 61413404546618567840438905)
    ·
      refine ⟨46060053409963925880329179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61413404546618567840438905 46060053409963925880329179)
      ·
        refine ⟨69090080114945888820493769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46060053409963925880329179 69090080114945888820493769)
        ·
          refine ⟨51817560086209416615370327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69090080114945888820493769 51817560086209416615370327)
          ·
            refine ⟨77726340129314124923055491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51817560086209416615370327 77726340129314124923055491)
            ·
              refine ⟨116589510193971187384583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77726340129314124923055491 116589510193971187384583237)
              ·
                refine ⟨21860533161369597634609357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116589510193971187384583237 21860533161369597634609357)
                ·
                  refine ⟨8197699935513599112978509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21860533161369597634609357 8197699935513599112978509)
                  ·
                    refine ⟨3074137475817599667366941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8197699935513599112978509 3074137475817599667366941)
                    ·
                      refine ⟨1152801553431599875262603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074137475817599667366941 1152801553431599875262603)
                      ·
                        rfl

theorem cell23_2245073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_2245073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245073 prefixEnd_2245073 := by exact prefixLift 2245073
  have htrace : WordTrace (prefixWord ++ tailWord_2245073) baseStart_2245073 baseEnd_2245073 := by
    simpa [prefixWord, tailWord_2245073, baseEnd_2245073] using wordTrace_append hprefix tailTrace_2245073
  have hstable : (prefixWord ++ tailWord_2245073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245073).length < 2 ^ (prefixWord ++ tailWord_2245073).sum := by decide
  have hdescent : baseEnd_2245073 < baseStart_2245073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245117 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_2245117 : Nat := 118140960795 + 2245117 * 2 ^ 59
def prefixEnd_2245117 : Nat := 4983230072969 + 3 ^ 40 * 2245117 * 2
def baseEnd_2245117 : Nat := 1152824146580397703112401

theorem tailTrace_2245117 : CollatzResearch.WordTrace tailWord_2245117 prefixEnd_2245117 1152824146580397703112401 := by
  unfold tailWord_2245117
  simp only [CollatzResearch.WordTrace]
  refine ⟨81886144207332019301853605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54590762804888012867902403 81886144207332019301853605)
  ·
    refine ⟨15353652038874753619097551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81886144207332019301853605 15353652038874753619097551)
    ·
      refine ⟨23030478058312130428646327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15353652038874753619097551 23030478058312130428646327)
      ·
        refine ⟨34545717087468195642969491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23030478058312130428646327 34545717087468195642969491)
        ·
          refine ⟨51818575631202293464454237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34545717087468195642969491 51818575631202293464454237)
          ·
            refine ⟨19431965861700860049170339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51818575631202293464454237 19431965861700860049170339)
            ·
              refine ⟨29147948792551290073755509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19431965861700860049170339 29147948792551290073755509)
              ·
                refine ⟨2732620199301683444414579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29147948792551290073755509 2732620199301683444414579)
                ·
                  refine ⟨4098930298952525166621869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732620199301683444414579 4098930298952525166621869)
                  ·
                    refine ⟨1537098862107196937483201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4098930298952525166621869 1537098862107196937483201)
                    ·
                      refine ⟨1152824146580397703112401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537098862107196937483201 1152824146580397703112401)
                      ·
                        rfl

theorem cell23_2245117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_2245117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245117 prefixEnd_2245117 := by exact prefixLift 2245117
  have htrace : WordTrace (prefixWord ++ tailWord_2245117) baseStart_2245117 baseEnd_2245117 := by
    simpa [prefixWord, tailWord_2245117, baseEnd_2245117] using wordTrace_append hprefix tailTrace_2245117
  have hstable : (prefixWord ++ tailWord_2245117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245117).length < 2 ^ (prefixWord ++ tailWord_2245117).sum := by decide
  have hdescent : baseEnd_2245117 < baseStart_2245117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245153 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 9]
def baseStart_2245153 : Nat := 118140960795 + 2245153 * 2 ^ 59
def prefixEnd_2245153 : Nat := 4983230072969 + 3 ^ 40 * 2245153 * 2
def baseEnd_2245153 : Nat := 128093625764884395806915

theorem tailTrace_2245153 : CollatzResearch.WordTrace tailWord_2245153 prefixEnd_2245153 128093625764884395806915 := by
  unfold tailWord_2245153
  simp only [CollatzResearch.WordTrace]
  refine ⟨81887457235201597450164113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54591638156801064966776075 81887457235201597450164113)
  ·
    refine ⟨61415592926401198087623085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81887457235201597450164113 61415592926401198087623085)
    ·
      refine ⟨23030847347400449282858657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61415592926401198087623085 23030847347400449282858657)
      ·
        refine ⟨17273135510550336962143993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23030847347400449282858657 17273135510550336962143993)
        ·
          refine ⟨12954851632912752721607995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17273135510550336962143993 12954851632912752721607995)
          ·
            refine ⟨19432277449369129082411993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12954851632912752721607995 19432277449369129082411993)
            ·
              refine ⟨14574208087026846811808995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19432277449369129082411993 14574208087026846811808995)
              ·
                refine ⟨21861312130540270217713493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14574208087026846811808995 21861312130540270217713493)
                ·
                  refine ⟨128093625764884395806915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21861312130540270217713493 128093625764884395806915)
                  ·
                    rfl

theorem cell23_2245153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_2245153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245153 prefixEnd_2245153 := by exact prefixLift 2245153
  have htrace : WordTrace (prefixWord ++ tailWord_2245153) baseStart_2245153 baseEnd_2245153 := by
    simpa [prefixWord, tailWord_2245153, baseEnd_2245153] using wordTrace_append hprefix tailTrace_2245153
  have hstable : (prefixWord ++ tailWord_2245153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245153).length < 2 ^ (prefixWord ++ tailWord_2245153).sum := by decide
  have hdescent : baseEnd_2245153 < baseStart_2245153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245181 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_2245181 : Nat := 118140960795 + 2245181 * 2 ^ 59
def prefixEnd_2245181 : Nat := 4983230072969 + 3 ^ 40 * 2245181 * 2
def baseEnd_2245181 : Nat := 1152857009342285452712107

theorem tailTrace_2245181 : CollatzResearch.WordTrace tailWord_2245181 prefixEnd_2245181 1152857009342285452712107 := by
  unfold tailWord_2245181
  simp only [CollatzResearch.WordTrace]
  refine ⟨81888478479100158232183397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54592318986066772154788931 81888478479100158232183397)
  ·
    refine ⟨15354089714831279668534387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81888478479100158232183397 15354089714831279668534387)
    ·
      refine ⟨23031134572246919502801581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15354089714831279668534387 23031134572246919502801581)
      ·
        refine ⟨8636675464592594813550593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23031134572246919502801581 8636675464592594813550593)
        ·
          refine ⟨6477506598444446110162945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636675464592594813550593 6477506598444446110162945)
          ·
            refine ⟨4858129948833334582622209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6477506598444446110162945 4858129948833334582622209)
            ·
              refine ⟨3643597461625000936966657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4858129948833334582622209 3643597461625000936966657)
              ·
                refine ⟨2732698096218750702724993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643597461625000936966657 2732698096218750702724993)
                ·
                  refine ⟨2049523572164063027043745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2732698096218750702724993 2049523572164063027043745)
                  ·
                    refine ⟨1537142679123047270282809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049523572164063027043745 1537142679123047270282809)
                    ·
                      refine ⟨1152857009342285452712107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537142679123047270282809 1152857009342285452712107)
                      ·
                        rfl

theorem cell23_2245181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_2245181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245181 prefixEnd_2245181 := by exact prefixLift 2245181
  have htrace : WordTrace (prefixWord ++ tailWord_2245181) baseStart_2245181 baseEnd_2245181 := by
    simpa [prefixWord, tailWord_2245181, baseEnd_2245181] using wordTrace_append hprefix tailTrace_2245181
  have hstable : (prefixWord ++ tailWord_2245181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245181).length < 2 ^ (prefixWord ++ tailWord_2245181).sum := by decide
  have hdescent : baseEnd_2245181 < baseStart_2245181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245197 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2245197 : Nat := 118140960795 + 2245197 * 2 ^ 59
def prefixEnd_2245197 : Nat := 4983230072969 + 3 ^ 40 * 2245197 * 2
def baseEnd_2245197 : Nat := 1152865225032757390112033

theorem tailTrace_2245197 : CollatzResearch.WordTrace tailWord_2245197 prefixEnd_2245197 1152865225032757390112033 := by
  unfold tailWord_2245197
  simp only [CollatzResearch.WordTrace]
  refine ⟨81889062047042192964765845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54592708031361461976510563 81889062047042192964765845)
  ·
    refine ⟨3838549783455102795223399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81889062047042192964765845 3838549783455102795223399)
    ·
      refine ⟨5757824675182654192835099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838549783455102795223399 5757824675182654192835099)
      ·
        refine ⟨8636737012773981289252649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757824675182654192835099 8636737012773981289252649)
        ·
          refine ⟨6477552759580485966939487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636737012773981289252649 6477552759580485966939487)
          ·
            refine ⟨9716329139370728950409231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477552759580485966939487 9716329139370728950409231)
            ·
              refine ⟨14574493709056093425613847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9716329139370728950409231 14574493709056093425613847)
              ·
                refine ⟨21861740563584140138420771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14574493709056093425613847 21861740563584140138420771)
                ·
                  refine ⟨32792610845376210207631157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21861740563584140138420771 32792610845376210207631157)
                  ·
                    refine ⟨3074307266754019706965421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32792610845376210207631157 3074307266754019706965421)
                    ·
                      refine ⟨1152865225032757390112033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074307266754019706965421 1152865225032757390112033)
                      ·
                        rfl

theorem cell23_2245197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2245197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245197 prefixEnd_2245197 := by exact prefixLift 2245197
  have htrace : WordTrace (prefixWord ++ tailWord_2245197) baseStart_2245197 baseEnd_2245197 := by
    simpa [prefixWord, tailWord_2245197, baseEnd_2245197] using wordTrace_append hprefix tailTrace_2245197
  have hstable : (prefixWord ++ tailWord_2245197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245197).length < 2 ^ (prefixWord ++ tailWord_2245197).sum := by decide
  have hdescent : baseEnd_2245197 < baseStart_2245197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245217 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2245217 : Nat := 118140960795 + 2245217 * 2 ^ 59
def prefixEnd_2245217 : Nat := 4983230072969 + 3 ^ 40 * 2245217 * 2
def baseEnd_2245217 : Nat := 384291831548615770620647

theorem tailTrace_2245217 : CollatzResearch.WordTrace tailWord_2245217 prefixEnd_2245217 384291831548615770620647 := by
  unfold tailWord_2245217
  simp only [CollatzResearch.WordTrace]
  refine ⟨81889791506969736380493905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54593194337979824253662603 81889791506969736380493905)
  ·
    refine ⟨61417343630227302285370429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81889791506969736380493905 61417343630227302285370429)
    ·
      refine ⟨23031503861335238357013911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61417343630227302285370429 23031503861335238357013911)
      ·
        refine ⟨34547255792002857535520867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031503861335238357013911 34547255792002857535520867)
        ·
          refine ⟨51820883688004286303281301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34547255792002857535520867 51820883688004286303281301)
          ·
            refine ⟨2429103922875200920466311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51820883688004286303281301 2429103922875200920466311)
            ·
              refine ⟨3643655884312801380699467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429103922875200920466311 3643655884312801380699467)
              ·
                refine ⟨5465483826469202071049201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643655884312801380699467 5465483826469202071049201)
                ·
                  refine ⟨4099112869851901553286901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5465483826469202071049201 4099112869851901553286901)
                  ·
                    refine ⟨384291831548615770620647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4099112869851901553286901 384291831548615770620647)
                    ·
                      rfl

theorem cell23_2245217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2245217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245217 prefixEnd_2245217 := by exact prefixLift 2245217
  have htrace : WordTrace (prefixWord ++ tailWord_2245217) baseStart_2245217 baseEnd_2245217 := by
    simpa [prefixWord, tailWord_2245217, baseEnd_2245217] using wordTrace_append hprefix tailTrace_2245217
  have hstable : (prefixWord ++ tailWord_2245217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245217).length < 2 ^ (prefixWord ++ tailWord_2245217).sum := by decide
  have hdescent : baseEnd_2245217 < baseStart_2245217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245220 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_2245220 : Nat := 118140960795 + 2245220 * 2 ^ 59
def prefixEnd_2245220 : Nat := 4983230072969 + 3 ^ 40 * 2245220 * 2
def baseEnd_2245220 : Nat := 1152877035087810800124427

theorem tailTrace_2245220 : CollatzResearch.WordTrace tailWord_2245220 prefixEnd_2245220 1152877035087810800124427 := by
  unfold tailWord_2245220
  simp only [CollatzResearch.WordTrace]
  refine ⟨40944950462979433946426557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54593267283972578595235409 40944950462979433946426557)
  ·
    refine ⟨15354356423617287729909959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40944950462979433946426557 15354356423617287729909959)
    ·
      refine ⟨23031534635425931594864939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15354356423617287729909959 23031534635425931594864939)
      ·
        refine ⟨34547301953138897392297409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031534635425931594864939 34547301953138897392297409)
        ·
          refine ⟨25910476464854173044223057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34547301953138897392297409 25910476464854173044223057)
          ·
            refine ⟨19432857348640629783167293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25910476464854173044223057 19432857348640629783167293)
            ·
              refine ⟨7287321505740236168687735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19432857348640629783167293 7287321505740236168687735)
              ·
                refine ⟨10930982258610354253031603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287321505740236168687735 10930982258610354253031603)
                ·
                  refine ⟨16396473387915531379547405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10930982258610354253031603 16396473387915531379547405)
                  ·
                    refine ⟨6148677520468324267330277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16396473387915531379547405 6148677520468324267330277)
                    ·
                      refine ⟨1152877035087810800124427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6148677520468324267330277 1152877035087810800124427)
                      ·
                        rfl

theorem cell23_2245220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_2245220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245220 prefixEnd_2245220 := by exact prefixLift 2245220
  have htrace : WordTrace (prefixWord ++ tailWord_2245220) baseStart_2245220 baseEnd_2245220 := by
    simpa [prefixWord, tailWord_2245220, baseEnd_2245220] using wordTrace_append hprefix tailTrace_2245220
  have hstable : (prefixWord ++ tailWord_2245220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245220).length < 2 ^ (prefixWord ++ tailWord_2245220).sum := by decide
  have hdescent : baseEnd_2245220 < baseStart_2245220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245324 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_2245324 : Nat := 118140960795 + 2245324 * 2 ^ 59
def prefixEnd_2245324 : Nat := 4983230072969 + 3 ^ 40 * 2245324 * 2
def baseEnd_2245324 : Nat := 384310145691959464407983

theorem tailTrace_2245324 : CollatzResearch.WordTrace tailWord_2245324 prefixEnd_2245324 384310145691959464407983 := by
  unfold tailWord_2245324
  simp only [CollatzResearch.WordTrace]
  refine ⟨40946847058791046827319513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54595796078388062436426017 40946847058791046827319513)
  ·
    refine ⟨30710135294093285120489635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40946847058791046827319513 30710135294093285120489635)
    ·
      refine ⟨46065202941139927680734453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30710135294093285120489635 46065202941139927680734453)
      ·
        refine ⟨4318612775731868220068855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46065202941139927680734453 4318612775731868220068855)
        ·
          refine ⟨6477919163597802330103283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318612775731868220068855 6477919163597802330103283)
          ·
            refine ⟨9716878745396703495154925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477919163597802330103283 9716878745396703495154925)
            ·
              refine ⟨3643829529523763810683097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9716878745396703495154925 3643829529523763810683097)
              ·
                refine ⟨2732872147142822858012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643829529523763810683097 2732872147142822858012323)
                ·
                  refine ⟨4099308220714234287018485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732872147142822858012323 4099308220714234287018485)
                  ·
                    refine ⟨384310145691959464407983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4099308220714234287018485 384310145691959464407983)
                    ·
                      rfl

theorem cell23_2245324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_2245324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245324 prefixEnd_2245324 := by exact prefixLift 2245324
  have htrace : WordTrace (prefixWord ++ tailWord_2245324) baseStart_2245324 baseEnd_2245324 := by
    simpa [prefixWord, tailWord_2245324, baseEnd_2245324] using wordTrace_append hprefix tailTrace_2245324
  have hstable : (prefixWord ++ tailWord_2245324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245324).length < 2 ^ (prefixWord ++ tailWord_2245324).sum := by decide
  have hdescent : baseEnd_2245324 < baseStart_2245324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245357 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2245357 : Nat := 118140960795 + 2245357 * 2 ^ 59
def prefixEnd_2245357 : Nat := 4983230072969 + 3 ^ 40 * 2245357 * 2
def baseEnd_2245357 : Nat := 1152947381937476764111297

theorem tailTrace_2245357 : CollatzResearch.WordTrace tailWord_2245357 prefixEnd_2245357 1152947381937476764111297 := by
  unfold tailWord_2245357
  simp only [CollatzResearch.WordTrace]
  refine ⟨81894897726462540290590325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54596598484308360193726883 81894897726462540290590325)
  ·
    refine ⟨7677646661855863152242843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81894897726462540290590325 7677646661855863152242843)
    ·
      refine ⟨11516469992783794728364265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7677646661855863152242843 11516469992783794728364265)
      ·
        refine ⟨8637352494587846046273199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11516469992783794728364265 8637352494587846046273199)
        ·
          refine ⟨12956028741881769069409799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8637352494587846046273199 12956028741881769069409799)
          ·
            refine ⟨19434043112822653604114699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12956028741881769069409799 19434043112822653604114699)
            ·
              refine ⟨29151064669233980406172049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19434043112822653604114699 29151064669233980406172049)
              ·
                refine ⟨21863298501925485304629037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29151064669233980406172049 21863298501925485304629037)
                ·
                  refine ⟨8198736938222056989235889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21863298501925485304629037 8198736938222056989235889)
                  ·
                    refine ⟨6149052703666542741926917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8198736938222056989235889 6149052703666542741926917)
                    ·
                      refine ⟨1152947381937476764111297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6149052703666542741926917 1152947381937476764111297)
                      ·
                        rfl

theorem cell23_2245357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2245357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245357 prefixEnd_2245357 := by exact prefixLift 2245357
  have htrace : WordTrace (prefixWord ++ tailWord_2245357) baseStart_2245357 baseEnd_2245357 := by
    simpa [prefixWord, tailWord_2245357, baseEnd_2245357] using wordTrace_append hprefix tailTrace_2245357
  have hstable : (prefixWord ++ tailWord_2245357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245357).length < 2 ^ (prefixWord ++ tailWord_2245357).sum := by decide
  have hdescent : baseEnd_2245357 < baseStart_2245357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245370 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_2245370 : Nat := 118140960795 + 2245370 * 2 ^ 59
def prefixEnd_2245370 : Nat := 4983230072969 + 3 ^ 40 * 2245370 * 2
def baseEnd_2245370 : Nat := 1152954057185985213248737

theorem tailTrace_2245370 : CollatzResearch.WordTrace tailWord_2245370 prefixEnd_2245370 1152954057185985213248737 := by
  unfold tailWord_2245370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20473842968853860877703391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54596914583610295673875709 20473842968853860877703391)
  ·
    refine ⟨30710764453280791316555087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20473842968853860877703391 30710764453280791316555087)
    ·
      refine ⟨46066146679921186974832631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30710764453280791316555087 46066146679921186974832631)
      ·
        refine ⟨69099220019881780462248947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46066146679921186974832631 69099220019881780462248947)
        ·
          refine ⟨103648830029822670693373421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69099220019881780462248947 103648830029822670693373421)
          ·
            refine ⟨38868311261183501510015033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103648830029822670693373421 38868311261183501510015033)
            ·
              refine ⟨29151233445887626132511275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38868311261183501510015033 29151233445887626132511275)
              ·
                refine ⟨43726850168831439198766913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29151233445887626132511275 43726850168831439198766913)
                ·
                  refine ⟨32795137626623579399075185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43726850168831439198766913 32795137626623579399075185)
                  ·
                    refine ⟨24596353219967684549306389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32795137626623579399075185 24596353219967684549306389)
                    ·
                      refine ⟨1152954057185985213248737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24596353219967684549306389 1152954057185985213248737)
                      ·
                        rfl

theorem cell23_2245370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_2245370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245370 prefixEnd_2245370 := by exact prefixLift 2245370
  have htrace : WordTrace (prefixWord ++ tailWord_2245370) baseStart_2245370 baseEnd_2245370 := by
    simpa [prefixWord, tailWord_2245370, baseEnd_2245370] using wordTrace_append hprefix tailTrace_2245370
  have hstable : (prefixWord ++ tailWord_2245370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245370).length < 2 ^ (prefixWord ++ tailWord_2245370).sum := by decide
  have hdescent : baseEnd_2245370 < baseStart_2245370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245374 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2245374 : Nat := 118140960795 + 2245374 * 2 ^ 59
def prefixEnd_2245374 : Nat := 4983230072969 + 3 ^ 40 * 2245374 * 2
def baseEnd_2245374 : Nat := 1152956111108603197598719

theorem tailTrace_2245374 : CollatzResearch.WordTrace tailWord_2245374 prefixEnd_2245374 1152956111108603197598719 := by
  unfold tailWord_2245374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236939720925119024244897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54597011844933968129306117 10236939720925119024244897)
  ·
    refine ⟨7677704790693839268183673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10236939720925119024244897 7677704790693839268183673)
    ·
      refine ⟨5758278593020379451137755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7677704790693839268183673 5758278593020379451137755)
      ·
        refine ⟨8637417889530569176706633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758278593020379451137755 8637417889530569176706633)
        ·
          refine ⟨6478063417147926882529975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8637417889530569176706633 6478063417147926882529975)
          ·
            refine ⟨9717095125721890323794963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478063417147926882529975 9717095125721890323794963)
            ·
              refine ⟨14575642688582835485692445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9717095125721890323794963 14575642688582835485692445)
              ·
                refine ⟨5465866008218563307134667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14575642688582835485692445 5465866008218563307134667)
                ·
                  refine ⟨8198799012327844960702001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465866008218563307134667 8198799012327844960702001)
                  ·
                    refine ⟨6149099259245883720526501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8198799012327844960702001 6149099259245883720526501)
                    ·
                      refine ⟨1152956111108603197598719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6149099259245883720526501 1152956111108603197598719)
                      ·
                        rfl

theorem cell23_2245374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2245374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245374 prefixEnd_2245374 := by exact prefixLift 2245374
  have htrace : WordTrace (prefixWord ++ tailWord_2245374) baseStart_2245374 baseEnd_2245374 := by
    simpa [prefixWord, tailWord_2245374, baseEnd_2245374] using wordTrace_append hprefix tailTrace_2245374
  have hstable : (prefixWord ++ tailWord_2245374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245374).length < 2 ^ (prefixWord ++ tailWord_2245374).sum := by decide
  have hdescent : baseEnd_2245374 < baseStart_2245374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245378 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2245378 : Nat := 118140960795 + 2245378 * 2 ^ 59
def prefixEnd_2245378 : Nat := 4983230072969 + 3 ^ 40 * 2245378 * 2
def baseEnd_2245378 : Nat := 1152958165031221181948701

theorem tailTrace_2245378 : CollatzResearch.WordTrace tailWord_2245378 prefixEnd_2245378 1152958165031221181948701 := by
  unfold tailWord_2245378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20473915914846615219276197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54597109106257640584736525 20473915914846615219276197)
  ·
    refine ⟨3838859234033740353614287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20473915914846615219276197 3838859234033740353614287)
    ·
      refine ⟨5758288851050610530421431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838859234033740353614287 5758288851050610530421431)
      ·
        refine ⟨8637433276575915795632147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758288851050610530421431 8637433276575915795632147)
        ·
          refine ⟨12956149914863873693448221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8637433276575915795632147 12956149914863873693448221)
          ·
            refine ⟨4858556218073952635043083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12956149914863873693448221 4858556218073952635043083)
            ·
              refine ⟨7287834327110928952564625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858556218073952635043083 7287834327110928952564625)
              ·
                refine ⟨5465875745333196714423469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7287834327110928952564625 5465875745333196714423469)
                ·
                  refine ⟨2049703404499948767908801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5465875745333196714423469 2049703404499948767908801)
                  ·
                    refine ⟨1537277553374961575931601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049703404499948767908801 1537277553374961575931601)
                    ·
                      refine ⟨1152958165031221181948701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537277553374961575931601 1152958165031221181948701)
                      ·
                        rfl

theorem cell23_2245378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2245378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245378 prefixEnd_2245378 := by exact prefixLift 2245378
  have htrace : WordTrace (prefixWord ++ tailWord_2245378) baseStart_2245378 baseEnd_2245378 := by
    simpa [prefixWord, tailWord_2245378, baseEnd_2245378] using wordTrace_append hprefix tailTrace_2245378
  have hstable : (prefixWord ++ tailWord_2245378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245378).length < 2 ^ (prefixWord ++ tailWord_2245378).sum := by decide
  have hdescent : baseEnd_2245378 < baseStart_2245378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245405 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2245405 : Nat := 118140960795 + 2245405 * 2 ^ 59
def prefixEnd_2245405 : Nat := 4983230072969 + 3 ^ 40 * 2245405 * 2
def baseEnd_2245405 : Nat := 384324009669630858770359

theorem tailTrace_2245405 : CollatzResearch.WordTrace tailWord_2245405 prefixEnd_2245405 384324009669630858770359 := by
  unfold tailWord_2245405
  simp only [CollatzResearch.WordTrace]
  refine ⟨81896648430288644488337669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54597765620192429658891779 81896648430288644488337669)
  ·
    refine ⟨15355621580679120841563313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81896648430288644488337669 15355621580679120841563313)
    ·
      refine ⟨11516716185509340631172485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15355621580679120841563313 11516716185509340631172485)
      ·
        refine ⟨2159384284783001368344841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11516716185509340631172485 2159384284783001368344841)
        ·
          refine ⟨1619538213587251026258631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159384284783001368344841 1619538213587251026258631)
          ·
            refine ⟨2429307320380876539387947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619538213587251026258631 2429307320380876539387947)
            ·
              refine ⟨3643960980571314809081921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429307320380876539387947 3643960980571314809081921)
              ·
                refine ⟨2732970735428486106811441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3643960980571314809081921 2732970735428486106811441)
                ·
                  refine ⟨2049728051571364580108581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2732970735428486106811441 2049728051571364580108581)
                  ·
                    refine ⟨384324009669630858770359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049728051571364580108581 384324009669630858770359)
                    ·
                      rfl

theorem cell23_2245405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2245405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245405 prefixEnd_2245405 := by exact prefixLift 2245405
  have htrace : WordTrace (prefixWord ++ tailWord_2245405) baseStart_2245405 baseEnd_2245405 := by
    simpa [prefixWord, tailWord_2245405, baseEnd_2245405] using wordTrace_append hprefix tailTrace_2245405
  have hstable : (prefixWord ++ tailWord_2245405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245405).length < 2 ^ (prefixWord ++ tailWord_2245405).sum := by decide
  have hdescent : baseEnd_2245405 < baseStart_2245405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245427 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 6]
def baseStart_2245427 : Nat := 118140960795 + 2245427 * 2 ^ 59
def prefixEnd_2245427 : Nat := 4983230072969 + 3 ^ 40 * 2245427 * 2
def baseEnd_2245427 : Nat := 384327775194430496745325

theorem tailTrace_2245427 : CollatzResearch.WordTrace tailWord_2245427 prefixEnd_2245427 384327775194430496745325 := by
  unfold tailWord_2245427
  simp only [CollatzResearch.WordTrace]
  refine ⟨81897450836208942245638535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54598300557472628163759023 81897450836208942245638535)
  ·
    refine ⟨122846176254313413368457803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81897450836208942245638535 122846176254313413368457803)
    ·
      refine ⟨184269264381470120052686705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122846176254313413368457803 184269264381470120052686705)
      ·
        refine ⟨138201948286102590039515029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184269264381470120052686705 138201948286102590039515029)
        ·
          refine ⟨6478216325911058908102267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138201948286102590039515029 6478216325911058908102267)
          ·
            refine ⟨9717324488866588362153401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478216325911058908102267 9717324488866588362153401)
            ·
              refine ⟨7287993366649941271615051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9717324488866588362153401 7287993366649941271615051)
              ·
                refine ⟨10931990049974911907422577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287993366649941271615051 10931990049974911907422577)
                ·
                  refine ⟨8198992537481183930566933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10931990049974911907422577 8198992537481183930566933)
                  ·
                    refine ⟨384327775194430496745325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8198992537481183930566933 384327775194430496745325)
                    ·
                      rfl

theorem cell23_2245427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 6].length) (baseStart_2245427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245427 prefixEnd_2245427 := by exact prefixLift 2245427
  have htrace : WordTrace (prefixWord ++ tailWord_2245427) baseStart_2245427 baseEnd_2245427 := by
    simpa [prefixWord, tailWord_2245427, baseEnd_2245427] using wordTrace_append hprefix tailTrace_2245427
  have hstable : (prefixWord ++ tailWord_2245427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245427).length < 2 ^ (prefixWord ++ tailWord_2245427).sum := by decide
  have hdescent : baseEnd_2245427 < baseStart_2245427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245428 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2245428 : Nat := 118140960795 + 2245428 * 2 ^ 59
def prefixEnd_2245428 : Nat := 4983230072969 + 3 ^ 40 * 2245428 * 2
def baseEnd_2245428 : Nat := 1152983839063945986323471

theorem tailTrace_2245428 : CollatzResearch.WordTrace tailWord_2245428 prefixEnd_2245428 1152983839063945986323471 := by
  unfold tailWord_2245428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40948743654602659708212469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54598324872803546277616625 40948743654602659708212469)
  ·
    refine ⟨3838944717618999347644919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40948743654602659708212469 3838944717618999347644919)
    ·
      refine ⟨5758417076428499021467379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838944717618999347644919 5758417076428499021467379)
      ·
        refine ⟨8637625614642748532201069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758417076428499021467379 8637625614642748532201069)
        ·
          refine ⟨3239109605491030699575401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8637625614642748532201069 3239109605491030699575401)
          ·
            refine ⟨2429332204118273024681551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239109605491030699575401 2429332204118273024681551)
            ·
              refine ⟨3643998306177409537022327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429332204118273024681551 3643998306177409537022327)
              ·
                refine ⟨5465997459266114305533491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643998306177409537022327 5465997459266114305533491)
                ·
                  refine ⟨8198996188899171458300237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5465997459266114305533491 8198996188899171458300237)
                  ·
                    refine ⟨3074623570837189296862589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8198996188899171458300237 3074623570837189296862589)
                    ·
                      refine ⟨1152983839063945986323471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074623570837189296862589 1152983839063945986323471)
                      ·
                        rfl

theorem cell23_2245428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2245428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245428 prefixEnd_2245428 := by exact prefixLift 2245428
  have htrace : WordTrace (prefixWord ++ tailWord_2245428) baseStart_2245428 baseEnd_2245428 := by
    simpa [prefixWord, tailWord_2245428, baseEnd_2245428] using wordTrace_append hprefix tailTrace_2245428
  have hstable : (prefixWord ++ tailWord_2245428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245428).length < 2 ^ (prefixWord ++ tailWord_2245428).sum := by decide
  have hdescent : baseEnd_2245428 < baseStart_2245428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245446 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2245446 : Nat := 118140960795 + 2245446 * 2 ^ 59
def prefixEnd_2245446 : Nat := 4983230072969 + 3 ^ 40 * 2245446 * 2
def baseEnd_2245446 : Nat := 1152993081715726915898389

theorem tailTrace_2245446 : CollatzResearch.WordTrace tailWord_2245446 prefixEnd_2245446 1152993081715726915898389 := by
  unfold tailWord_2245446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559316994473128390330631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54598762548760072327053461 2559316994473128390330631)
  ·
    refine ⟨3838975491709692585495947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559316994473128390330631 3838975491709692585495947)
    ·
      refine ⟨5758463237564538878243921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838975491709692585495947 5758463237564538878243921)
      ·
        refine ⟨4318847428173404158682941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5758463237564538878243921 4318847428173404158682941)
        ·
          refine ⟨1619567785565026559506103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4318847428173404158682941 1619567785565026559506103)
          ·
            refine ⟨2429351678347539839259155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619567785565026559506103 2429351678347539839259155)
            ·
              refine ⟨3644027517521309758888733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429351678347539839259155 3644027517521309758888733)
              ·
                refine ⟨1366510319070491159583275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644027517521309758888733 1366510319070491159583275)
                ·
                  refine ⟨2049765478605736739374913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366510319070491159583275 2049765478605736739374913)
                  ·
                    refine ⟨1537324108954302554531185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049765478605736739374913 1537324108954302554531185)
                    ·
                      refine ⟨1152993081715726915898389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537324108954302554531185 1152993081715726915898389)
                      ·
                        rfl

theorem cell23_2245446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2245446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245446 prefixEnd_2245446 := by exact prefixLift 2245446
  have htrace : WordTrace (prefixWord ++ tailWord_2245446) baseStart_2245446 baseEnd_2245446 := by
    simpa [prefixWord, tailWord_2245446, baseEnd_2245446] using wordTrace_append hprefix tailTrace_2245446
  have hstable : (prefixWord ++ tailWord_2245446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245446).length < 2 ^ (prefixWord ++ tailWord_2245446).sum := by decide
  have hdescent : baseEnd_2245446 < baseStart_2245446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245468 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2245468 : Nat := 118140960795 + 2245468 * 2 ^ 59
def prefixEnd_2245468 : Nat := 4983230072969 + 3 ^ 40 * 2245468 * 2
def baseEnd_2245468 : Nat := 1153004378290125829823287

theorem tailTrace_2245468 : CollatzResearch.WordTrace tailWord_2245468 prefixEnd_2245468 1153004378290125829823287 := by
  unfold tailWord_2245468
  simp only [CollatzResearch.WordTrace]
  refine ⟨40949473114530203123940529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54599297486040270831920705 40949473114530203123940529)
  ·
    refine ⟨30712104835897652342955397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40949473114530203123940529 30712104835897652342955397)
    ·
      refine ⟨5758519656730809814304137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30712104835897652342955397 5758519656730809814304137)
      ·
        refine ⟨4318889742548107360728103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5758519656730809814304137 4318889742548107360728103)
        ·
          refine ⟨6478334613822161041092155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318889742548107360728103 6478334613822161041092155)
          ·
            refine ⟨9717501920733241561638233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478334613822161041092155 9717501920733241561638233)
            ·
              refine ⟨7288126440549931171228675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9717501920733241561638233 7288126440549931171228675)
              ·
                refine ⟨10932189660824896756843013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288126440549931171228675 10932189660824896756843013)
                ·
                  refine ⟨2049785561404668141908065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10932189660824896756843013 2049785561404668141908065)
                  ·
                    refine ⟨1537339171053501106431049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2049785561404668141908065 1537339171053501106431049)
                    ·
                      refine ⟨1153004378290125829823287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537339171053501106431049 1153004378290125829823287)
                      ·
                        rfl

theorem cell23_2245468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2245468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245468 prefixEnd_2245468 := by exact prefixLift 2245468
  have htrace : WordTrace (prefixWord ++ tailWord_2245468) baseStart_2245468 baseEnd_2245468 := by
    simpa [prefixWord, tailWord_2245468, baseEnd_2245468] using wordTrace_append hprefix tailTrace_2245468
  have hstable : (prefixWord ++ tailWord_2245468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245468).length < 2 ^ (prefixWord ++ tailWord_2245468).sum := by decide
  have hdescent : baseEnd_2245468 < baseStart_2245468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245514 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2245514 : Nat := 118140960795 + 2245514 * 2 ^ 59
def prefixEnd_2245514 : Nat := 4983230072969 + 3 ^ 40 * 2245514 * 2
def baseEnd_2245514 : Nat := 1153027998400232649848075

theorem tailTrace_2245514 : CollatzResearch.WordTrace tailWord_2245514 prefixEnd_2245514 1153027998400232649848075 := by
  unfold tailWord_2245514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475155996723439026013899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54600415991262504069370397 20475155996723439026013899)
  ·
    refine ⟨30712733995085158539020849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20475155996723439026013899 30712733995085158539020849)
    ·
      refine ⟨23034550496313868904265637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30712733995085158539020849 23034550496313868904265637)
      ·
        refine ⟨4318978218058850419549807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23034550496313868904265637 4318978218058850419549807)
        ·
          refine ⟨6478467327088275629324711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4318978218058850419549807 6478467327088275629324711)
          ·
            refine ⟨9717700990632413443987067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478467327088275629324711 9717700990632413443987067)
            ·
              refine ⟨14576551485948620165980601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9717700990632413443987067 14576551485948620165980601)
              ·
                refine ⟨10932413614461465124485451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14576551485948620165980601 10932413614461465124485451)
                ·
                  refine ⟨16398620421692197686728177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10932413614461465124485451 16398620421692197686728177)
                  ·
                    refine ⟨12298965316269148265046133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16398620421692197686728177 12298965316269148265046133)
                    ·
                      refine ⟨1153027998400232649848075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12298965316269148265046133 1153027998400232649848075)
                      ·
                        rfl

theorem cell23_2245514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2245514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245514 prefixEnd_2245514 := by exact prefixLift 2245514
  have htrace : WordTrace (prefixWord ++ tailWord_2245514) baseStart_2245514 baseEnd_2245514 := by
    simpa [prefixWord, tailWord_2245514, baseEnd_2245514] using wordTrace_append hprefix tailTrace_2245514
  have hstable : (prefixWord ++ tailWord_2245514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245514).length < 2 ^ (prefixWord ++ tailWord_2245514).sum := by decide
  have hdescent : baseEnd_2245514 < baseStart_2245514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245527 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2245527 : Nat := 118140960795 + 2245527 * 2 ^ 59
def prefixEnd_2245527 : Nat := 4983230072969 + 3 ^ 40 * 2245527 * 2
def baseEnd_2245527 : Nat := 1153034673648741098985515

theorem tailTrace_2245527 : CollatzResearch.WordTrace tailWord_2245527 prefixEnd_2245527 1153034673648741098985515 := by
  unfold tailWord_2245527
  simp only [CollatzResearch.WordTrace]
  refine ⟨81901098135846659324278835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54600732090564439549519223 81901098135846659324278835)
  ·
    refine ⟨122851647203769988986418253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81901098135846659324278835 122851647203769988986418253)
    ·
      refine ⟨46069367701413745869906845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122851647203769988986418253 46069367701413745869906845)
      ·
        refine ⟨17276012888030154701215067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46069367701413745869906845 17276012888030154701215067)
        ·
          refine ⟨25914019332045232051822601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17276012888030154701215067 25914019332045232051822601)
          ·
            refine ⟨19435514499033924038866951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25914019332045232051822601 19435514499033924038866951)
            ·
              refine ⟨29153271748550886058300427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19435514499033924038866951 29153271748550886058300427)
              ·
                refine ⟨43729907622826329087450641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29153271748550886058300427 43729907622826329087450641)
                ·
                  refine ⟨32797430717119746815587981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43729907622826329087450641 32797430717119746815587981)
                  ·
                    refine ⟨12299036518919905055845493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32797430717119746815587981 12299036518919905055845493)
                    ·
                      refine ⟨1153034673648741098985515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12299036518919905055845493 1153034673648741098985515)
                      ·
                        rfl

theorem cell23_2245527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2245527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245527 prefixEnd_2245527 := by exact prefixLift 2245527
  have htrace : WordTrace (prefixWord ++ tailWord_2245527) baseStart_2245527 baseEnd_2245527 := by
    simpa [prefixWord, tailWord_2245527, baseEnd_2245527] using wordTrace_append hprefix tailTrace_2245527
  have hstable : (prefixWord ++ tailWord_2245527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245527).length < 2 ^ (prefixWord ++ tailWord_2245527).sum := by decide
  have hdescent : baseEnd_2245527 < baseStart_2245527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245561 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2245561 : Nat := 118140960795 + 2245561 * 2 ^ 59
def prefixEnd_2245561 : Nat := 4983230072969 + 3 ^ 40 * 2245561 * 2
def baseEnd_2245561 : Nat := 1153052131990993965960359

theorem tailTrace_2245561 : CollatzResearch.WordTrace tailWord_2245561 prefixEnd_2245561 1153052131990993965960359 := by
  unfold tailWord_2245561
  simp only [CollatzResearch.WordTrace]
  refine ⟨81902338217723483131016537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54601558811815655420677691 81902338217723483131016537)
  ·
    refine ⟨61426753663292612348262403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81902338217723483131016537 61426753663292612348262403)
    ·
      refine ⟨92140130494938918522393605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61426753663292612348262403 92140130494938918522393605)
      ·
        refine ⟨17276274467801047222948801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92140130494938918522393605 17276274467801047222948801)
        ·
          refine ⟨12957205850850785417211601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17276274467801047222948801 12957205850850785417211601)
          ·
            refine ⟨9717904388138089062908701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12957205850850785417211601 9717904388138089062908701)
            ·
              refine ⟨3644214145551783398590763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9717904388138089062908701 3644214145551783398590763)
              ·
                refine ⟨5466321218327675097886145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644214145551783398590763 5466321218327675097886145)
                ·
                  refine ⟨4099740913745756323414609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5466321218327675097886145 4099740913745756323414609)
                  ·
                    refine ⟨3074805685309317242560957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099740913745756323414609 3074805685309317242560957)
                    ·
                      refine ⟨1153052131990993965960359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074805685309317242560957 1153052131990993965960359)
                      ·
                        rfl

theorem cell23_2245561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2245561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245561 prefixEnd_2245561 := by exact prefixLift 2245561
  have htrace : WordTrace (prefixWord ++ tailWord_2245561) baseStart_2245561 baseEnd_2245561 := by
    simpa [prefixWord, tailWord_2245561, baseEnd_2245561] using wordTrace_append hprefix tailTrace_2245561
  have hstable : (prefixWord ++ tailWord_2245561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245561).length < 2 ^ (prefixWord ++ tailWord_2245561).sum := by decide
  have hdescent : baseEnd_2245561 < baseStart_2245561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245568 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 1, 4]
def baseStart_2245568 : Nat := 118140960795 + 2245568 * 2 ^ 59
def prefixEnd_2245568 : Nat := 4983230072969 + 3 ^ 40 * 2245568 * 2
def baseEnd_2245568 : Nat := 384351908785191812857609

theorem tailTrace_2245568 : CollatzResearch.WordTrace tailWord_2245568 prefixEnd_2245568 384351908785191812857609 := by
  unfold tailWord_2245568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40951296764349061663260679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54601729019132082217680905 40951296764349061663260679)
  ·
    refine ⟨61426945146523592494891019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40951296764349061663260679 61426945146523592494891019)
    ·
      refine ⟨92140417719785388742336529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61426945146523592494891019 92140417719785388742336529)
      ·
        refine ⟨69105313289839041556752397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92140417719785388742336529 69105313289839041556752397)
        ·
          refine ⟨25914492483689640583782149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69105313289839041556752397 25914492483689640583782149)
          ·
            refine ⟨4858967340691807609459153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25914492483689640583782149 4858967340691807609459153)
            ·
              refine ⟨3644225505518855707094365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4858967340691807609459153 3644225505518855707094365)
              ·
                refine ⟨1366584564569570890160387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644225505518855707094365 1366584564569570890160387)
                ·
                  refine ⟨2049876846854356335240581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366584564569570890160387 2049876846854356335240581)
                  ·
                    refine ⟨384351908785191812857609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049876846854356335240581 384351908785191812857609)
                    ·
                      rfl

theorem cell23_2245568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_2245568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245568 prefixEnd_2245568 := by exact prefixLift 2245568
  have htrace : WordTrace (prefixWord ++ tailWord_2245568) baseStart_2245568 baseEnd_2245568 := by
    simpa [prefixWord, tailWord_2245568, baseEnd_2245568] using wordTrace_append hprefix tailTrace_2245568
  have hstable : (prefixWord ++ tailWord_2245568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245568).length < 2 ^ (prefixWord ++ tailWord_2245568).sum := by decide
  have hdescent : baseEnd_2245568 < baseStart_2245568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245642 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_2245642 : Nat := 118140960795 + 2245642 * 2 ^ 59
def prefixEnd_2245642 : Nat := 4983230072969 + 3 ^ 40 * 2245642 * 2
def baseEnd_2245642 : Nat := 1153093723924008149047487

theorem tailTrace_2245642 : CollatzResearch.WordTrace tailWord_2245642 prefixEnd_2245642 1153093723924008149047487 := by
  unfold tailWord_2245642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476323132607508491178795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54603528353620022643143453 20476323132607508491178795)
  ·
    refine ⟨30714484698911262736768193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20476323132607508491178795 30714484698911262736768193)
    ·
      refine ⟨23035863524183447052576145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30714484698911262736768193 23035863524183447052576145)
      ·
        refine ⟨17276897643137585289432109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23035863524183447052576145 17276897643137585289432109)
        ·
          refine ⟨6478836616176594483537041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17276897643137585289432109 6478836616176594483537041)
          ·
            refine ⟨4859127462132445862652781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478836616176594483537041 4859127462132445862652781)
            ·
              refine ⟨1822172798299667198494793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4859127462132445862652781 1822172798299667198494793)
              ·
                refine ⟨1366629598724750398871095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822172798299667198494793 1366629598724750398871095)
                ·
                  refine ⟨2049944398087125598306643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366629598724750398871095 2049944398087125598306643)
                  ·
                    refine ⟨3074916597130688397459965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049944398087125598306643 3074916597130688397459965)
                    ·
                      refine ⟨1153093723924008149047487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074916597130688397459965 1153093723924008149047487)
                      ·
                        rfl

theorem cell23_2245642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_2245642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245642 prefixEnd_2245642 := by exact prefixLift 2245642
  have htrace : WordTrace (prefixWord ++ tailWord_2245642) baseStart_2245642 baseEnd_2245642 := by
    simpa [prefixWord, tailWord_2245642, baseEnd_2245642] using wordTrace_append hprefix tailTrace_2245642
  have hstable : (prefixWord ++ tailWord_2245642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245642).length < 2 ^ (prefixWord ++ tailWord_2245642).sum := by decide
  have hdescent : baseEnd_2245642 < baseStart_2245642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245644 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2245644 : Nat := 118140960795 + 2245644 * 2 ^ 59
def prefixEnd_2245644 : Nat := 4983230072969 + 3 ^ 40 * 2245644 * 2
def baseEnd_2245644 : Nat := 1153094750885317141222477

theorem tailTrace_2245644 : CollatzResearch.WordTrace tailWord_2245644 prefixEnd_2245644 1153094750885317141222477 := by
  unfold tailWord_2245644
  simp only [CollatzResearch.WordTrace]
  refine ⟨40952682738211394153143993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54603576984281858870858657 40952682738211394153143993)
  ·
    refine ⟨30714512053658545614857995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40952682738211394153143993 30714512053658545614857995)
    ·
      refine ⟨46071768080487818422286993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30714512053658545614857995 46071768080487818422286993)
      ·
        refine ⟨34553826060365863816715245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46071768080487818422286993 34553826060365863816715245)
        ·
          refine ⟨12957684772637198931268217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34553826060365863816715245 12957684772637198931268217)
          ·
            refine ⟨9718263579477899198451163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12957684772637198931268217 9718263579477899198451163)
            ·
              refine ⟨14577395369216848797676745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9718263579477899198451163 14577395369216848797676745)
              ·
                refine ⟨10933046526912636598257559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14577395369216848797676745 10933046526912636598257559)
                ·
                  refine ⟨16399569790368954897386339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10933046526912636598257559 16399569790368954897386339)
                  ·
                    refine ⟨24599354685553432346079509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16399569790368954897386339 24599354685553432346079509)
                    ·
                      refine ⟨1153094750885317141222477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24599354685553432346079509 1153094750885317141222477)
                      ·
                        rfl

theorem cell23_2245644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2245644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245644 prefixEnd_2245644 := by exact prefixLift 2245644
  have htrace : WordTrace (prefixWord ++ tailWord_2245644) baseStart_2245644 baseEnd_2245644 := by
    simpa [prefixWord, tailWord_2245644, baseEnd_2245644] using wordTrace_append hprefix tailTrace_2245644
  have hstable : (prefixWord ++ tailWord_2245644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245644).length < 2 ^ (prefixWord ++ tailWord_2245644).sum := by decide
  have hdescent : baseEnd_2245644 < baseStart_2245644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245668 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2245668 : Nat := 118140960795 + 2245668 * 2 ^ 59
def prefixEnd_2245668 : Nat := 4983230072969 + 3 ^ 40 * 2245668 * 2
def baseEnd_2245668 : Nat := 1153107074421025047322367

theorem tailTrace_2245668 : CollatzResearch.WordTrace tailWord_2245668 prefixEnd_2245668 1153107074421025047322367 := by
  unfold tailWord_2245668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40953120414167920202580829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54604160552223893603441105 40953120414167920202580829)
  ·
    refine ⟨15357420155312970075967811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40953120414167920202580829 15357420155312970075967811)
    ·
      refine ⟨23036130232969455113951717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15357420155312970075967811 23036130232969455113951717)
      ·
        refine ⟨4319274418681772833865947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23036130232969455113951717 4319274418681772833865947)
        ·
          refine ⟨6478911628022659250798921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319274418681772833865947 6478911628022659250798921)
          ·
            refine ⟨4859183721016994438099191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478911628022659250798921 4859183721016994438099191)
            ·
              refine ⟨7288775581525491657148787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859183721016994438099191 7288775581525491657148787)
              ·
                refine ⟨10933163372288237485723181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7288775581525491657148787 10933163372288237485723181)
                ·
                  refine ⟨4099936264608089057146193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10933163372288237485723181 4099936264608089057146193)
                  ·
                    refine ⟨3074952198456066792859645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4099936264608089057146193 3074952198456066792859645)
                    ·
                      refine ⟨1153107074421025047322367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074952198456066792859645 1153107074421025047322367)
                      ·
                        rfl

theorem cell23_2245668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2245668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245668 prefixEnd_2245668 := by exact prefixLift 2245668
  have htrace : WordTrace (prefixWord ++ tailWord_2245668) baseStart_2245668 baseEnd_2245668 := by
    simpa [prefixWord, tailWord_2245668, baseEnd_2245668] using wordTrace_append hprefix tailTrace_2245668
  have hstable : (prefixWord ++ tailWord_2245668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245668).length < 2 ^ (prefixWord ++ tailWord_2245668).sum := by decide
  have hdescent : baseEnd_2245668 < baseStart_2245668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245671 : List Nat := [1, 1, 7, 1, 1, 1, 2, 9]
def baseStart_2245671 : Nat := 118140960795 + 2245671 * 2 ^ 59
def prefixEnd_2245671 : Nat := 4983230072969 + 3 ^ 40 * 2245671 * 2
def baseEnd_2245671 : Nat := 42707726476406982799439

theorem tailTrace_2245671 : CollatzResearch.WordTrace tailWord_2245671 prefixEnd_2245671 42707726476406982799439 := by
  unfold tailWord_2245671
  simp only [CollatzResearch.WordTrace]
  refine ⟨81906350247324971917520867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54604233498216647945013911 81906350247324971917520867)
  ·
    refine ⟨122859525370987457876281301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81906350247324971917520867 122859525370987457876281301)
    ·
      refine ⟨2879520125882518543975343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 122859525370987457876281301 2879520125882518543975343)
      ·
        refine ⟨4319280188823777815963015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2879520125882518543975343 4319280188823777815963015)
        ·
          refine ⟨6478920283235666723944523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319280188823777815963015 6478920283235666723944523)
          ·
            refine ⟨9718380424853500085916785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478920283235666723944523 9718380424853500085916785)
            ·
              refine ⟨7288785318640125064437589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9718380424853500085916785 7288785318640125064437589)
              ·
                refine ⟨42707726476406982799439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7288785318640125064437589 42707726476406982799439)
                ·
                  rfl

theorem cell23_2245671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 9].length) (baseStart_2245671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245671 prefixEnd_2245671 := by exact prefixLift 2245671
  have htrace : WordTrace (prefixWord ++ tailWord_2245671) baseStart_2245671 baseEnd_2245671 := by
    simpa [prefixWord, tailWord_2245671, baseEnd_2245671] using wordTrace_append hprefix tailTrace_2245671
  have hstable : (prefixWord ++ tailWord_2245671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245671).length < 2 ^ (prefixWord ++ tailWord_2245671).sum := by decide
  have hdescent : baseEnd_2245671 < baseStart_2245671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245681 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2245681 : Nat := 118140960795 + 2245681 * 2 ^ 59
def prefixEnd_2245681 : Nat := 4983230072969 + 3 ^ 40 * 2245681 * 2
def baseEnd_2245681 : Nat := 1153113749669533496459807

theorem tailTrace_2245681 : CollatzResearch.WordTrace tailWord_2245681 prefixEnd_2245681 1153113749669533496459807 := by
  unfold tailWord_2245681
  simp only [CollatzResearch.WordTrace]
  refine ⟨81906714977288743625384897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54604476651525829083589931 81906714977288743625384897)
  ·
    refine ⟨61430036232966557719038673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81906714977288743625384897 61430036232966557719038673)
    ·
      refine ⟨46072527174724918289279005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61430036232966557719038673 46072527174724918289279005)
      ·
        refine ⟨17277197690521844358479627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46072527174724918289279005 17277197690521844358479627)
        ·
          refine ⟨25915796535782766537719441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17277197690521844358479627 25915796535782766537719441)
          ·
            refine ⟨19436847401837074903289581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25915796535782766537719441 19436847401837074903289581)
            ·
              refine ⟨7288817775688903088733593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19436847401837074903289581 7288817775688903088733593)
              ·
                refine ⟨5466613331766677316550195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7288817775688903088733593 5466613331766677316550195)
                ·
                  refine ⟨8199919997650015974825293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5466613331766677316550195 8199919997650015974825293)
                  ·
                    refine ⟨3074969999118755990559485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8199919997650015974825293 3074969999118755990559485)
                    ·
                      refine ⟨1153113749669533496459807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3074969999118755990559485 1153113749669533496459807)
                      ·
                        rfl

theorem cell23_2245681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2245681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245681 prefixEnd_2245681 := by exact prefixLift 2245681
  have htrace : WordTrace (prefixWord ++ tailWord_2245681) baseStart_2245681 baseEnd_2245681 := by
    simpa [prefixWord, tailWord_2245681, baseEnd_2245681] using wordTrace_append hprefix tailTrace_2245681
  have hstable : (prefixWord ++ tailWord_2245681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245681).length < 2 ^ (prefixWord ++ tailWord_2245681).sum := by decide
  have hdescent : baseEnd_2245681 < baseStart_2245681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245691 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 7, 3, 2]
def baseStart_2245691 : Nat := 118140960795 + 2245691 * 2 ^ 59
def prefixEnd_2245691 : Nat := 4983230072969 + 3 ^ 40 * 2245691 * 2
def baseEnd_2245691 : Nat := 1153118884476078457334761

theorem tailTrace_2245691 : CollatzResearch.WordTrace tailWord_2245691 prefixEnd_2245691 1153118884476078457334761 := by
  unfold tailWord_2245691
  simp only [CollatzResearch.WordTrace]
  refine ⟨81907079707252515333248927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54604719804835010222165951 81907079707252515333248927)
  ·
    refine ⟨122860619560878772999873391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81907079707252515333248927 122860619560878772999873391)
    ·
      refine ⟨184290929341318159499810087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122860619560878772999873391 184290929341318159499810087)
      ·
        refine ⟨276436394011977239249715131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184290929341318159499810087 276436394011977239249715131)
        ·
          refine ⟨414654591017965858874572697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276436394011977239249715131 414654591017965858874572697)
          ·
            refine ⟨310990943263474394155929523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414654591017965858874572697 310990943263474394155929523)
            ·
              refine ⟨466486414895211591233894285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310990943263474394155929523 466486414895211591233894285)
              ·
                refine ⟨174932405585704346712710357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466486414895211591233894285 174932405585704346712710357)
                ·
                  refine ⟨4099978255914945626079149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174932405585704346712710357 4099978255914945626079149)
                  ·
                    refine ⟨1537491845968104609779681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4099978255914945626079149 1537491845968104609779681)
                    ·
                      refine ⟨1153118884476078457334761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537491845968104609779681 1153118884476078457334761)
                      ·
                        rfl

theorem cell23_2245691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 3, 2].length) (baseStart_2245691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245691 prefixEnd_2245691 := by exact prefixLift 2245691
  have htrace : WordTrace (prefixWord ++ tailWord_2245691) baseStart_2245691 baseEnd_2245691 := by
    simpa [prefixWord, tailWord_2245691, baseEnd_2245691] using wordTrace_append hprefix tailTrace_2245691
  have hstable : (prefixWord ++ tailWord_2245691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245691).length < 2 ^ (prefixWord ++ tailWord_2245691).sum := by decide
  have hdescent : baseEnd_2245691 < baseStart_2245691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245704 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2245704 : Nat := 118140960795 + 2245704 * 2 ^ 59
def prefixEnd_2245704 : Nat := 4983230072969 + 3 ^ 40 * 2245704 * 2
def baseEnd_2245704 : Nat := 1153125559724586906472201

theorem tailTrace_2245704 : CollatzResearch.WordTrace tailWord_2245704 prefixEnd_2245704 1153125559724586906472201 := by
  unfold tailWord_2245704
  simp only [CollatzResearch.WordTrace]
  refine ⟨40953776928102709276736083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54605035904136945702314777 40953776928102709276736083)
  ·
    refine ⟨61430665392154063915104125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40953776928102709276736083 61430665392154063915104125)
    ·
      refine ⟨23036499522057773968164047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61430665392154063915104125 23036499522057773968164047)
      ·
        refine ⟨34554749283086660952246071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23036499522057773968164047 34554749283086660952246071)
        ·
          refine ⟨51832123924629991428369107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34554749283086660952246071 51832123924629991428369107)
          ·
            refine ⟨77748185886944987142553661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51832123924629991428369107 77748185886944987142553661)
            ·
              refine ⟨29155569707604370178457623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77748185886944987142553661 29155569707604370178457623)
              ·
                refine ⟨43733354561406555267686435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29155569707604370178457623 43733354561406555267686435)
                ·
                  refine ⟨65600031842109832901529653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43733354561406555267686435 65600031842109832901529653)
                  ·
                    refine ⟨6150002985197796834518405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65600031842109832901529653 6150002985197796834518405)
                    ·
                      refine ⟨1153125559724586906472201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6150002985197796834518405 1153125559724586906472201)
                      ·
                        rfl

theorem cell23_2245704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2245704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245704 prefixEnd_2245704 := by exact prefixLift 2245704
  have htrace : WordTrace (prefixWord ++ tailWord_2245704) baseStart_2245704 baseEnd_2245704 := by
    simpa [prefixWord, tailWord_2245704, baseEnd_2245704] using wordTrace_append hprefix tailTrace_2245704
  have hstable : (prefixWord ++ tailWord_2245704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245704).length < 2 ^ (prefixWord ++ tailWord_2245704).sum := by decide
  have hdescent : baseEnd_2245704 < baseStart_2245704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245742 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_2245742 : Nat := 118140960795 + 2245742 * 2 ^ 59
def prefixEnd_2245742 : Nat := 4983230072969 + 3 ^ 40 * 2245742 * 2
def baseEnd_2245742 : Nat := 1153145071989457757797027

theorem tailTrace_2245742 : CollatzResearch.WordTrace tailWord_2245742 prefixEnd_2245742 1153145071989457757797027 := by
  unfold tailWord_2245742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10238617478758468880419435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54605959886711834028903653 10238617478758468880419435)
  ·
    refine ⟨15357926218137703320629153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10238617478758468880419435 15357926218137703320629153)
    ·
      refine ⟨11518444663603277490471865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15357926218137703320629153 11518444663603277490471865)
      ·
        refine ⟨8638833497702458117853899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11518444663603277490471865 8638833497702458117853899)
        ·
          refine ⟨12958250246553687176780849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8638833497702458117853899 12958250246553687176780849)
          ·
            refine ⟨9718687684915265382585637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12958250246553687176780849 9718687684915265382585637)
            ·
              refine ⟨1822253940921612259234807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9718687684915265382585637 1822253940921612259234807)
              ·
                refine ⟨2733380911382418388852211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822253940921612259234807 2733380911382418388852211)
                ·
                  refine ⟨4100071367073627583278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2733380911382418388852211 4100071367073627583278317)
                  ·
                    refine ⟨1537526762652610343729369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4100071367073627583278317 1537526762652610343729369)
                    ·
                      refine ⟨1153145071989457757797027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537526762652610343729369 1153145071989457757797027)
                      ·
                        rfl

theorem cell23_2245742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_2245742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245742 prefixEnd_2245742 := by exact prefixLift 2245742
  have htrace : WordTrace (prefixWord ++ tailWord_2245742) baseStart_2245742 baseEnd_2245742 := by
    simpa [prefixWord, tailWord_2245742, baseEnd_2245742] using wordTrace_append hprefix tailTrace_2245742
  have hstable : (prefixWord ++ tailWord_2245742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245742).length < 2 ^ (prefixWord ++ tailWord_2245742).sum := by decide
  have hdescent : baseEnd_2245742 < baseStart_2245742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245744 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 9]
def baseStart_2245744 : Nat := 118140960795 + 2245744 * 2 ^ 59
def prefixEnd_2245744 : Nat := 4983230072969 + 3 ^ 40 * 2245744 * 2
def baseEnd_2245744 : Nat := 128127344327862972219113

theorem tailTrace_2245744 : CollatzResearch.WordTrace tailWord_2245744 prefixEnd_2245744 128127344327862972219113 := by
  unfold tailWord_2245744
  simp only [CollatzResearch.WordTrace]
  refine ⟨40954506388030252692464143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54606008517373670256618857 40954506388030252692464143)
  ·
    refine ⟨61431759582045379038696215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40954506388030252692464143 61431759582045379038696215)
    ·
      refine ⟨92147639373068068558044323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61431759582045379038696215 92147639373068068558044323)
      ·
        refine ⟨138221459059602102837066485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92147639373068068558044323 138221459059602102837066485)
        ·
          refine ⟨12958261786837697140974983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138221459059602102837066485 12958261786837697140974983)
          ·
            refine ⟨19437392680256545711462475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12958261786837697140974983 19437392680256545711462475)
            ·
              refine ⟨29156089020384818567193713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19437392680256545711462475 29156089020384818567193713)
              ·
                refine ⟨21867066765288613925395285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29156089020384818567193713 21867066765288613925395285)
                ·
                  refine ⟨128127344327862972219113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21867066765288613925395285 128127344327862972219113)
                  ·
                    rfl

theorem cell23_2245744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_2245744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245744 prefixEnd_2245744 := by exact prefixLift 2245744
  have htrace : WordTrace (prefixWord ++ tailWord_2245744) baseStart_2245744 baseEnd_2245744 := by
    simpa [prefixWord, tailWord_2245744, baseEnd_2245744] using wordTrace_append hprefix tailTrace_2245744
  have hstable : (prefixWord ++ tailWord_2245744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245744).length < 2 ^ (prefixWord ++ tailWord_2245744).sum := by decide
  have hdescent : baseEnd_2245744 < baseStart_2245744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245749 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2245749 : Nat := 118140960795 + 2245749 * 2 ^ 59
def prefixEnd_2245749 : Nat := 4983230072969 + 3 ^ 40 * 2245749 * 2
def baseEnd_2245749 : Nat := 1153148666354039230409495

theorem tailTrace_2245749 : CollatzResearch.WordTrace tailWord_2245749 prefixEnd_2245749 1153148666354039230409495 := by
  unfold tailWord_2245749
  simp only [CollatzResearch.WordTrace]
  refine ⟨81909195141042391238860301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54606130094028260825906867 81909195141042391238860301)
  ·
    refine ⟨30715948177890896714572613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81909195141042391238860301 30715948177890896714572613)
    ·
      refine ⟨5759240283354543133982365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30715948177890896714572613 5759240283354543133982365)
      ·
        refine ⟨2159715106257953675243387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5759240283354543133982365 2159715106257953675243387)
        ·
          refine ⟨3239572659386930512865081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159715106257953675243387 3239572659386930512865081)
          ·
            refine ⟨2429679494540197884648811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239572659386930512865081 2429679494540197884648811)
            ·
              refine ⟨3644519241810296826973217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429679494540197884648811 3644519241810296826973217)
              ·
                refine ⟨2733389431357722620229913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644519241810296826973217 2733389431357722620229913)
                ·
                  refine ⟨2050042073518291965172435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733389431357722620229913 2050042073518291965172435)
                  ·
                    refine ⟨3075063110277437947758653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050042073518291965172435 3075063110277437947758653)
                    ·
                      refine ⟨1153148666354039230409495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075063110277437947758653 1153148666354039230409495)
                      ·
                        rfl

theorem cell23_2245749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2245749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245749 prefixEnd_2245749 := by exact prefixLift 2245749
  have htrace : WordTrace (prefixWord ++ tailWord_2245749) baseStart_2245749 baseEnd_2245749 := by
    simpa [prefixWord, tailWord_2245749, baseEnd_2245749] using wordTrace_append hprefix tailTrace_2245749
  have hstable : (prefixWord ++ tailWord_2245749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245749).length < 2 ^ (prefixWord ++ tailWord_2245749).sum := by decide
  have hdescent : baseEnd_2245749 < baseStart_2245749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245761 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 7]
def baseStart_2245761 : Nat := 118140960795 + 2245761 * 2 ^ 59
def prefixEnd_2245761 : Nat := 4983230072969 + 3 ^ 40 * 2245761 * 2
def baseEnd_2245761 : Nat := 128128314235765909273271

theorem tailTrace_2245761 : CollatzResearch.WordTrace tailWord_2245761 prefixEnd_2245761 128128314235765909273271 := by
  unfold tailWord_2245761
  simp only [CollatzResearch.WordTrace]
  refine ⟨81909632816998917288297137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54606421877999278192198091 81909632816998917288297137)
  ·
    refine ⟨61432224612749187966222853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81909632816998917288297137 61432224612749187966222853)
    ·
      refine ⟨11518542114890472743666785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61432224612749187966222853 11518542114890472743666785)
      ·
        refine ⟨8638906586167854557750089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11518542114890472743666785 8638906586167854557750089)
        ·
          refine ⟨6479179939625890918312567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8638906586167854557750089 6479179939625890918312567)
          ·
            refine ⟨9718769909438836377468851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479179939625890918312567 9718769909438836377468851)
            ·
              refine ⟨14578154864158254566203277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9718769909438836377468851 14578154864158254566203277)
              ·
                refine ⟨5466808074059345462326229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14578154864158254566203277 5466808074059345462326229)
                ·
                  refine ⟨128128314235765909273271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5466808074059345462326229 128128314235765909273271)
                  ·
                    rfl

theorem cell23_2245761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_2245761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245761 prefixEnd_2245761 := by exact prefixLift 2245761
  have htrace : WordTrace (prefixWord ++ tailWord_2245761) baseStart_2245761 baseEnd_2245761 := by
    simpa [prefixWord, tailWord_2245761, baseEnd_2245761] using wordTrace_append hprefix tailTrace_2245761
  have hstable : (prefixWord ++ tailWord_2245761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245761).length < 2 ^ (prefixWord ++ tailWord_2245761).sum := by decide
  have hdescent : baseEnd_2245761 < baseStart_2245761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245811 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4]
def baseStart_2245811 : Nat := 118140960795 + 2245811 * 2 ^ 59
def prefixEnd_2245811 : Nat := 4983230072969 + 3 ^ 40 * 2245811 * 2
def baseEnd_2245811 : Nat := 1153180502154617987834209

theorem tailTrace_2245811 : CollatzResearch.WordTrace tailWord_2245811 prefixEnd_2245811 1153180502154617987834209 := by
  unfold tailWord_2245811
  simp only [CollatzResearch.WordTrace]
  refine ⟨81911456466817775827617287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54607637644545183885078191 81911456466817775827617287)
  ·
    refine ⟨122867184700226663741425931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81911456466817775827617287 122867184700226663741425931)
    ·
      refine ⟨184300777050339995612138897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122867184700226663741425931 184300777050339995612138897)
      ·
        refine ⟨138225582787754996709104173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184300777050339995612138897 138225582787754996709104173)
        ·
          refine ⟨51834593545408123765914065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138225582787754996709104173 51834593545408123765914065)
          ·
            refine ⟨38875945159056092824435549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51834593545408123765914065 38875945159056092824435549)
            ·
              refine ⟨14578479434646034809163331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38875945159056092824435549 14578479434646034809163331)
              ·
                refine ⟨21867719151969052213744997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14578479434646034809163331 21867719151969052213744997)
                ·
                  refine ⟨4100197340994197290077187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21867719151969052213744997 4100197340994197290077187)
                  ·
                    refine ⟨6150296011491295935115781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100197340994197290077187 6150296011491295935115781)
                    ·
                      refine ⟨1153180502154617987834209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6150296011491295935115781 1153180502154617987834209)
                      ·
                        rfl

theorem cell23_2245811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_2245811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245811 prefixEnd_2245811 := by exact prefixLift 2245811
  have htrace : WordTrace (prefixWord ++ tailWord_2245811) baseStart_2245811 baseEnd_2245811 := by
    simpa [prefixWord, tailWord_2245811, baseEnd_2245811] using wordTrace_append hprefix tailTrace_2245811
  have hstable : (prefixWord ++ tailWord_2245811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245811).length < 2 ^ (prefixWord ++ tailWord_2245811).sum := by decide
  have hdescent : baseEnd_2245811 < baseStart_2245811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_2245831 : Nat := 118140960795 + 2245831 * 2 ^ 59
def prefixEnd_2245831 : Nat := 4983230072969 + 3 ^ 40 * 2245831 * 2
def baseEnd_2245831 : Nat := 1153190771767707909584117

theorem tailTrace_2245831 : CollatzResearch.WordTrace tailWord_2245831 prefixEnd_2245831 1153190771767707909584117 := by
  unfold tailWord_2245831
  simp only [CollatzResearch.WordTrace]
  refine ⟨81912185926745319243345347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54608123951163546162230231 81912185926745319243345347)
  ·
    refine ⟨122868278890117978865018021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81912185926745319243345347 122868278890117978865018021)
    ·
      refine ⟨23037802291897121037190879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122868278890117978865018021 23037802291897121037190879)
      ·
        refine ⟨34556703437845681555786319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23037802291897121037190879 34556703437845681555786319)
        ·
          refine ⟨51835055156768522333679479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34556703437845681555786319 51835055156768522333679479)
          ·
            refine ⟨77752582735152783500519219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51835055156768522333679479 77752582735152783500519219)
            ·
              refine ⟨116628874102729175250778829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77752582735152783500519219 116628874102729175250778829)
              ·
                refine ⟨43735827788523440719042061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116628874102729175250778829 43735827788523440719042061)
                ·
                  refine ⟨16400935420696290269640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43735827788523440719042061 16400935420696290269640773)
                  ·
                    refine ⟨3075175391380554425557645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16400935420696290269640773 3075175391380554425557645)
                    ·
                      refine ⟨1153190771767707909584117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075175391380554425557645 1153190771767707909584117)
                      ·
                        rfl

theorem cell23_2245831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_2245831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245831 prefixEnd_2245831 := by exact prefixLift 2245831
  have htrace : WordTrace (prefixWord ++ tailWord_2245831) baseStart_2245831 baseEnd_2245831 := by
    simpa [prefixWord, tailWord_2245831, baseEnd_2245831] using wordTrace_append hprefix tailTrace_2245831
  have hstable : (prefixWord ++ tailWord_2245831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245831).length < 2 ^ (prefixWord ++ tailWord_2245831).sum := by decide
  have hdescent : baseEnd_2245831 < baseStart_2245831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245845 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2245845 : Nat := 118140960795 + 2245845 * 2 ^ 59
def prefixEnd_2245845 : Nat := 4983230072969 + 3 ^ 40 * 2245845 * 2
def baseEnd_2245845 : Nat := 1153197960496870854809053

theorem tailTrace_2245845 : CollatzResearch.WordTrace tailWord_2245845 prefixEnd_2245845 1153197960496870854809053 := by
  unfold tailWord_2245845
  simp only [CollatzResearch.WordTrace]
  refine ⟨81912696548694599634354989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54608464365796399756236659 81912696548694599634354989)
  ·
    refine ⟨30717261205760474862883121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81912696548694599634354989 30717261205760474862883121)
    ·
      refine ⟨23037945904320356147162341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30717261205760474862883121 23037945904320356147162341)
      ·
        refine ⟨4319614857060066777592939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23037945904320356147162341 4319614857060066777592939)
        ·
          refine ⟨6479422285590100166389409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4319614857060066777592939 6479422285590100166389409)
          ·
            refine ⟨4859566714192575124792057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6479422285590100166389409 4859566714192575124792057)
            ·
              refine ⟨3644675035644431343594043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859566714192575124792057 3644675035644431343594043)
              ·
                refine ⟨5467012553466647015391065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3644675035644431343594043 5467012553466647015391065)
                ·
                  refine ⟨4100259415099985261543299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467012553466647015391065 4100259415099985261543299)
                  ·
                    refine ⟨6150389122649977892314949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4100259415099985261543299 6150389122649977892314949)
                    ·
                      refine ⟨1153197960496870854809053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6150389122649977892314949 1153197960496870854809053)
                      ·
                        rfl

theorem cell23_2245845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2245845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245845 prefixEnd_2245845 := by exact prefixLift 2245845
  have htrace : WordTrace (prefixWord ++ tailWord_2245845) baseStart_2245845 baseEnd_2245845 := by
    simpa [prefixWord, tailWord_2245845, baseEnd_2245845] using wordTrace_append hprefix tailTrace_2245845
  have hstable : (prefixWord ++ tailWord_2245845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245845).length < 2 ^ (prefixWord ++ tailWord_2245845).sum := by decide
  have hdescent : baseEnd_2245845 < baseStart_2245845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245868 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 6]
def baseStart_2245868 : Nat := 118140960795 + 2245868 * 2 ^ 59
def prefixEnd_2245868 : Nat := 4983230072969 + 3 ^ 40 * 2245868 * 2
def baseEnd_2245868 : Nat := 128134418950213807202383

theorem tailTrace_2245868 : CollatzResearch.WordTrace tailWord_2245868 prefixEnd_2245868 128134418950213807202383 := by
  unfold tailWord_2245868
  simp only [CollatzResearch.WordTrace]
  refine ⟨40956767713805637281221129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54609023618407516374961505 40956767713805637281221129)
  ·
    refine ⟨30717575785354227960915847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40956767713805637281221129 30717575785354227960915847)
    ·
      refine ⟨46076363678031341941373771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30717575785354227960915847 46076363678031341941373771)
      ·
        refine ⟨69114545517047012912060657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46076363678031341941373771 69114545517047012912060657)
        ·
          refine ⟨51835909137785259684045493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69114545517047012912060657 51835909137785259684045493)
          ·
            refine ⟨4859616481667368095379265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51835909137785259684045493 4859616481667368095379265)
            ·
              refine ⟨3644712361250526071534449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859616481667368095379265 3644712361250526071534449)
              ·
                refine ⟨2733534270937894553650837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3644712361250526071534449 2733534270937894553650837)
                ·
                  refine ⟨128134418950213807202383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2733534270937894553650837 128134418950213807202383)
                  ·
                    rfl

theorem cell23_2245868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_2245868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245868 prefixEnd_2245868 := by exact prefixLift 2245868
  have htrace : WordTrace (prefixWord ++ tailWord_2245868) baseStart_2245868 baseEnd_2245868 := by
    simpa [prefixWord, tailWord_2245868, baseEnd_2245868] using wordTrace_append hprefix tailTrace_2245868
  have hstable : (prefixWord ++ tailWord_2245868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245868).length < 2 ^ (prefixWord ++ tailWord_2245868).sum := by decide
  have hdescent : baseEnd_2245868 < baseStart_2245868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245878 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2245878 : Nat := 118140960795 + 2245878 * 2 ^ 59
def prefixEnd_2245878 : Nat := 4983230072969 + 3 ^ 40 * 2245878 * 2
def baseEnd_2245878 : Nat := 1153214905358469225696401

theorem tailTrace_2245878 : CollatzResearch.WordTrace tailWord_2245878 prefixEnd_2245878 1153214905358469225696401 := by
  unfold tailWord_2245878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119618759848440391894143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54609266771716697513537525 5119618759848440391894143)
  ·
    refine ⟨7679428139772660587841215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119618759848440391894143 7679428139772660587841215)
    ·
      refine ⟨11519142209658990881761823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7679428139772660587841215 11519142209658990881761823)
      ·
        refine ⟨17278713314488486322642735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519142209658990881761823 17278713314488486322642735)
        ·
          refine ⟨25918069971732729483964103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278713314488486322642735 25918069971732729483964103)
          ·
            refine ⟨38877104957599094225946155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25918069971732729483964103 38877104957599094225946155)
            ·
              refine ⟨58315657436398641338919233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38877104957599094225946155 58315657436398641338919233)
              ·
                refine ⟨43736743077298981004189425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58315657436398641338919233 43736743077298981004189425)
                ·
                  refine ⟨32802557307974235753142069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43736743077298981004189425 32802557307974235753142069)
                  ·
                    refine ⟨3075239747622584601857069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32802557307974235753142069 3075239747622584601857069)
                    ·
                      refine ⟨1153214905358469225696401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075239747622584601857069 1153214905358469225696401)
                      ·
                        rfl

theorem cell23_2245878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2245878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245878 prefixEnd_2245878 := by exact prefixLift 2245878
  have htrace : WordTrace (prefixWord ++ tailWord_2245878) baseStart_2245878 baseEnd_2245878 := by
    simpa [prefixWord, tailWord_2245878, baseEnd_2245878] using wordTrace_append hprefix tailTrace_2245878
  have hstable : (prefixWord ++ tailWord_2245878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245878).length < 2 ^ (prefixWord ++ tailWord_2245878).sum := by decide
  have hdescent : baseEnd_2245878 < baseStart_2245878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245881 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_2245881 : Nat := 118140960795 + 2245881 * 2 ^ 59
def prefixEnd_2245881 : Nat := 4983230072969 + 3 ^ 40 * 2245881 * 2
def baseEnd_2245881 : Nat := 384405481933477571319629

theorem tailTrace_2245881 : CollatzResearch.WordTrace tailWord_2245881 prefixEnd_2245881 384405481933477571319629 := by
  unfold tailWord_2245881
  simp only [CollatzResearch.WordTrace]
  refine ⟨81914009576564177782665497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54609339717709451855110331 81914009576564177782665497)
  ·
    refine ⟨61435507182423133336999123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81914009576564177782665497 61435507182423133336999123)
    ·
      refine ⟨92153260773634700005498685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61435507182423133336999123 92153260773634700005498685)
      ·
        refine ⟨34557472790113012502062007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92153260773634700005498685 34557472790113012502062007)
        ·
          refine ⟨51836209185169518753093011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34557472790113012502062007 51836209185169518753093011)
          ·
            refine ⟨77754313777754278129639517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51836209185169518753093011 77754313777754278129639517)
            ·
              refine ⟨29157867666657854298614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77754313777754278129639517 29157867666657854298614819)
              ·
                refine ⟨43736801499986781447922229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29157867666657854298614819 43736801499986781447922229)
                ·
                  refine ⟨4100325140623760760742709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43736801499986781447922229 4100325140623760760742709)
                  ·
                    refine ⟨384405481933477571319629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4100325140623760760742709 384405481933477571319629)
                    ·
                      rfl

theorem cell23_2245881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_2245881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245881 prefixEnd_2245881 := by exact prefixLift 2245881
  have htrace : WordTrace (prefixWord ++ tailWord_2245881) baseStart_2245881 baseEnd_2245881 := by
    simpa [prefixWord, tailWord_2245881, baseEnd_2245881] using wordTrace_append hprefix tailTrace_2245881
  have hstable : (prefixWord ++ tailWord_2245881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245881).length < 2 ^ (prefixWord ++ tailWord_2245881).sum := by decide
  have hdescent : baseEnd_2245881 < baseStart_2245881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245888 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2]
def baseStart_2245888 : Nat := 118140960795 + 2245888 * 2 ^ 59
def prefixEnd_2245888 : Nat := 4983230072969 + 3 ^ 40 * 2245888 * 2
def baseEnd_2245888 : Nat := 1153220040165014186571355

theorem tailTrace_2245888 : CollatzResearch.WordTrace tailWord_2245888 prefixEnd_2245888 1153220040165014186571355 := by
  unfold tailWord_2245888
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957132443769408989085159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54609509925025878652113545 40957132443769408989085159)
  ·
    refine ⟨61435698665654113483627739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40957132443769408989085159 61435698665654113483627739)
    ·
      refine ⟨92153547998481170225441609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61435698665654113483627739 92153547998481170225441609)
      ·
        refine ⟨69115160998860877669081207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92153547998481170225441609 69115160998860877669081207)
        ·
          refine ⟨103672741498291316503621811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69115160998860877669081207 103672741498291316503621811)
          ·
            refine ⟨155509112247436974755432717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103672741498291316503621811 155509112247436974755432717)
            ·
              refine ⟨58315917092788865533287269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155509112247436974755432717 58315917092788865533287269)
              ·
                refine ⟨10934234454897912287491363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58315917092788865533287269 10934234454897912287491363)
                ·
                  refine ⟨16401351682346868431237045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10934234454897912287491363 16401351682346868431237045)
                  ·
                    refine ⟨1537626720220018915428473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16401351682346868431237045 1537626720220018915428473)
                    ·
                      refine ⟨1153220040165014186571355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537626720220018915428473 1153220040165014186571355)
                      ·
                        rfl

theorem cell23_2245888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_2245888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245888 prefixEnd_2245888 := by exact prefixLift 2245888
  have htrace : WordTrace (prefixWord ++ tailWord_2245888) baseStart_2245888 baseEnd_2245888 := by
    simpa [prefixWord, tailWord_2245888, baseEnd_2245888] using wordTrace_append hprefix tailTrace_2245888
  have hstable : (prefixWord ++ tailWord_2245888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245888).length < 2 ^ (prefixWord ++ tailWord_2245888).sum := by decide
  have hdescent : baseEnd_2245888 < baseStart_2245888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245898 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_2245898 : Nat := 118140960795 + 2245898 * 2 ^ 59
def prefixEnd_2245898 : Nat := 4983230072969 + 3 ^ 40 * 2245898 * 2
def baseEnd_2245898 : Nat := 384408391657186382482103

theorem tailTrace_2245898 : CollatzResearch.WordTrace tailWord_2245898 prefixEnd_2245898 384408391657186382482103 := by
  unfold tailWord_2245898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478657404375647421508587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54609753078335059790689565 20478657404375647421508587)
  ·
    refine ⟨30717986106563471132262881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20478657404375647421508587 30717986106563471132262881)
    ·
      refine ⟨23038489579922603349197161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30717986106563471132262881 23038489579922603349197161)
      ·
        refine ⟨17278867184941952511897871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23038489579922603349197161 17278867184941952511897871)
        ·
          refine ⟨25918300777412928767846807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278867184941952511897871 25918300777412928767846807)
          ·
            refine ⟨38877451166119393151770211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25918300777412928767846807 38877451166119393151770211)
            ·
              refine ⟨58316176749179089727655317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38877451166119393151770211 58316176749179089727655317)
              ·
                refine ⟨2733570785117769830983843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58316176749179089727655317 2733570785117769830983843)
                ·
                  refine ⟨4100356177676654746475765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2733570785117769830983843 4100356177676654746475765)
                  ·
                    refine ⟨384408391657186382482103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4100356177676654746475765 384408391657186382482103)
                    ·
                      rfl

theorem cell23_2245898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_2245898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245898 prefixEnd_2245898 := by exact prefixLift 2245898
  have htrace : WordTrace (prefixWord ++ tailWord_2245898) baseStart_2245898 baseEnd_2245898 := by
    simpa [prefixWord, tailWord_2245898, baseEnd_2245898] using wordTrace_append hprefix tailTrace_2245898
  have hstable : (prefixWord ++ tailWord_2245898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245898).length < 2 ^ (prefixWord ++ tailWord_2245898).sum := by decide
  have hdescent : baseEnd_2245898 < baseStart_2245898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245906 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2245906 : Nat := 118140960795 + 2245906 * 2 ^ 59
def prefixEnd_2245906 : Nat := 4983230072969 + 3 ^ 40 * 2245906 * 2
def baseEnd_2245906 : Nat := 384409760938931705382091

theorem tailTrace_2245906 : CollatzResearch.WordTrace tailWord_2245906 prefixEnd_2245906 384409760938931705382091 := by
  unfold tailWord_2245906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478730350368401763081393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54609947600982404701550381 20478730350368401763081393)
  ·
    refine ⟨15359047762776301322311045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20478730350368401763081393 15359047762776301322311045)
    ·
      refine ⟨2879821455520556497933321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15359047762776301322311045 2879821455520556497933321)
      ·
        refine ⟨2159866091640417373449991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2879821455520556497933321 2159866091640417373449991)
        ·
          refine ⟨3239799137460626060174987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159866091640417373449991 3239799137460626060174987)
          ·
            refine ⟨4859698706190939090262481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239799137460626060174987 4859698706190939090262481)
            ·
              refine ⟨3644774029643204317696861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859698706190939090262481 3644774029643204317696861)
              ·
                refine ⟨1366790261116201619136323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644774029643204317696861 1366790261116201619136323)
                ·
                  refine ⟨2050185391674302428704485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366790261116201619136323 2050185391674302428704485)
                  ·
                    refine ⟨384409760938931705382091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050185391674302428704485 384409760938931705382091)
                    ·
                      rfl

theorem cell23_2245906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2245906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245906 prefixEnd_2245906 := by exact prefixLift 2245906
  have htrace : WordTrace (prefixWord ++ tailWord_2245906) baseStart_2245906 baseEnd_2245906 := by
    simpa [prefixWord, tailWord_2245906, baseEnd_2245906] using wordTrace_append hprefix tailTrace_2245906
  have hstable : (prefixWord ++ tailWord_2245906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245906).length < 2 ^ (prefixWord ++ tailWord_2245906).sum := by decide
  have hdescent : baseEnd_2245906 < baseStart_2245906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245912 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2245912 : Nat := 118140960795 + 2245912 * 2 ^ 59
def prefixEnd_2245912 : Nat := 4983230072969 + 3 ^ 40 * 2245912 * 2
def baseEnd_2245912 : Nat := 1153232363700722092671245

theorem tailTrace_2245912 : CollatzResearch.WordTrace tailWord_2245912 prefixEnd_2245912 1153232363700722092671245 := by
  unfold tailWord_2245912
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957570119725935038521995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54610093492967913384695993 40957570119725935038521995)
  ·
    refine ⟨61436355179588902557782993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40957570119725935038521995 61436355179588902557782993)
    ·
      refine ⟨46077266384691676918337245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61436355179588902557782993 46077266384691676918337245)
      ·
        refine ⟨17278974894259378844376467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46077266384691676918337245 17278974894259378844376467)
        ·
          refine ⟨25918462341389068266564701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278974894259378844376467 25918462341389068266564701)
          ·
            refine ⟨9719423378020900599961763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25918462341389068266564701 9719423378020900599961763)
            ·
              refine ⟨14579135067031350899942645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719423378020900599961763 14579135067031350899942645)
              ·
                refine ⟨1366793912534189146869623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14579135067031350899942645 1366793912534189146869623)
                ·
                  refine ⟨2050190868801283720304435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366793912534189146869623 2050190868801283720304435)
                  ·
                    refine ⟨3075286303201925580456653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050190868801283720304435 3075286303201925580456653)
                    ·
                      refine ⟨1153232363700722092671245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075286303201925580456653 1153232363700722092671245)
                      ·
                        rfl

theorem cell23_2245912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2245912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245912 prefixEnd_2245912 := by exact prefixLift 2245912
  have htrace : WordTrace (prefixWord ++ tailWord_2245912) baseStart_2245912 baseEnd_2245912 := by
    simpa [prefixWord, tailWord_2245912, baseEnd_2245912] using wordTrace_append hprefix tailTrace_2245912
  have hstable : (prefixWord ++ tailWord_2245912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245912).length < 2 ^ (prefixWord ++ tailWord_2245912).sum := by decide
  have hdescent : baseEnd_2245912 < baseStart_2245912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245938 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2245938 : Nat := 118140960795 + 2245938 * 2 ^ 59
def prefixEnd_2245938 : Nat := 4983230072969 + 3 ^ 40 * 2245938 * 2
def baseEnd_2245938 : Nat := 1153245714197738990946125

theorem tailTrace_2245938 : CollatzResearch.WordTrace tailWord_2245938 prefixEnd_2245938 1153245714197738990946125 := by
  unfold tailWord_2245938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479022134339419129372617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54610725691571784344993645 20479022134339419129372617)
  ·
    refine ⟨15359266600754564347029463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20479022134339419129372617 15359266600754564347029463)
    ·
      refine ⟨23038899901131846520544195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15359266600754564347029463 23038899901131846520544195)
      ·
        refine ⟨34558349851697769780816293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23038899901131846520544195 34558349851697769780816293)
        ·
          refine ⟨6479690597193331833903055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34558349851697769780816293 6479690597193331833903055)
          ·
            refine ⟨9719535895789997750854583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479690597193331833903055 9719535895789997750854583)
            ·
              refine ⟨14579303843684996626281875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719535895789997750854583 14579303843684996626281875)
              ·
                refine ⟨21868955765527494939422813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14579303843684996626281875 21868955765527494939422813)
                ·
                  refine ⟨8200858412072810602283555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21868955765527494939422813 8200858412072810602283555)
                  ·
                    refine ⟨12301287618109215903425333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8200858412072810602283555 12301287618109215903425333)
                    ·
                      refine ⟨1153245714197738990946125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12301287618109215903425333 1153245714197738990946125)
                      ·
                        rfl

theorem cell23_2245938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2245938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245938 prefixEnd_2245938 := by exact prefixLift 2245938
  have htrace : WordTrace (prefixWord ++ tailWord_2245938) baseStart_2245938 baseEnd_2245938 := by
    simpa [prefixWord, tailWord_2245938, baseEnd_2245938] using wordTrace_append hprefix tailTrace_2245938
  have hstable : (prefixWord ++ tailWord_2245938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245938).length < 2 ^ (prefixWord ++ tailWord_2245938).sum := by decide
  have hdescent : baseEnd_2245938 < baseStart_2245938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245948 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2245948 : Nat := 118140960795 + 2245948 * 2 ^ 59
def prefixEnd_2245948 : Nat := 4983230072969 + 3 ^ 40 * 2245948 * 2
def baseEnd_2245948 : Nat := 1153250849004283951821079

theorem tailTrace_2245948 : CollatzResearch.WordTrace tailWord_2245948 prefixEnd_2245948 1153250849004283951821079 := by
  unfold tailWord_2245948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40958226633660724112677249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54610968844880965483569665 40958226633660724112677249)
  ·
    refine ⟨30718669975245543084507937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40958226633660724112677249 30718669975245543084507937)
    ·
      refine ⟨23039002481434157313380953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30718669975245543084507937 23039002481434157313380953)
      ·
        refine ⟨17279251861075617985035715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23039002481434157313380953 17279251861075617985035715)
        ·
          refine ⟨25918877791613426977553573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17279251861075617985035715 25918877791613426977553573)
          ·
            refine ⟨4859789585927517558291295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25918877791613426977553573 4859789585927517558291295)
            ·
              refine ⟨7289684378891276337436943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859789585927517558291295 7289684378891276337436943)
              ·
                refine ⟨10934526568336914506155415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7289684378891276337436943 10934526568336914506155415)
                ·
                  refine ⟨16401789852505371759233123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10934526568336914506155415 16401789852505371759233123)
                  ·
                    refine ⟨24602684778758057638849685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16401789852505371759233123 24602684778758057638849685)
                    ·
                      refine ⟨1153250849004283951821079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24602684778758057638849685 1153250849004283951821079)
                      ·
                        rfl

theorem cell23_2245948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2245948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245948 prefixEnd_2245948 := by exact prefixLift 2245948
  have htrace : WordTrace (prefixWord ++ tailWord_2245948) baseStart_2245948 baseEnd_2245948 := by
    simpa [prefixWord, tailWord_2245948, baseEnd_2245948] using wordTrace_append hprefix tailTrace_2245948
  have hstable : (prefixWord ++ tailWord_2245948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245948).length < 2 ^ (prefixWord ++ tailWord_2245948).sum := by decide
  have hdescent : baseEnd_2245948 < baseStart_2245948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2245968 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_2245968 : Nat := 118140960795 + 2245968 * 2 ^ 59
def prefixEnd_2245968 : Nat := 4983230072969 + 3 ^ 40 * 2245968 * 2
def baseEnd_2245968 : Nat := 1153261118617373873570987

theorem tailTrace_2245968 : CollatzResearch.WordTrace tailWord_2245968 prefixEnd_2245968 1153261118617373873570987 := by
  unfold tailWord_2245968
  simp only [CollatzResearch.WordTrace]
  refine ⟨40958591363624495820541279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54611455151499327760721705 40958591363624495820541279)
  ·
    refine ⟨61437887045436743730811919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40958591363624495820541279 61437887045436743730811919)
    ·
      refine ⟨92156830568155115596217879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61437887045436743730811919 92156830568155115596217879)
      ·
        refine ⟨138235245852232673394326819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92156830568155115596217879 138235245852232673394326819)
        ·
          refine ⟨207352868778349010091490229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138235245852232673394326819 207352868778349010091490229)
          ·
            refine ⟨19439331447970219696077209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207352868778349010091490229 19439331447970219696077209)
            ·
              refine ⟨14579498585977664772057907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19439331447970219696077209 14579498585977664772057907)
              ·
                refine ⟨21869247878966497158086861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14579498585977664772057907 21869247878966497158086861)
                ·
                  refine ⟨8200967954612436434282573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21869247878966497158086861 8200967954612436434282573)
                  ·
                    refine ⟨3075362982979663662855965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8200967954612436434282573 3075362982979663662855965)
                    ·
                      refine ⟨1153261118617373873570987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075362982979663662855965 1153261118617373873570987)
                      ·
                        rfl

theorem cell23_2245968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_2245968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2245968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2245968 prefixEnd_2245968 := by exact prefixLift 2245968
  have htrace : WordTrace (prefixWord ++ tailWord_2245968) baseStart_2245968 baseEnd_2245968 := by
    simpa [prefixWord, tailWord_2245968, baseEnd_2245968] using wordTrace_append hprefix tailTrace_2245968
  have hstable : (prefixWord ++ tailWord_2245968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2245968).length < 2 ^ (prefixWord ++ tailWord_2245968).sum := by decide
  have hdescent : baseEnd_2245968 < baseStart_2245968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2245968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246002 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2246002 : Nat := 118140960795 + 2246002 * 2 ^ 59
def prefixEnd_2246002 : Nat := 4983230072969 + 3 ^ 40 * 2246002 * 2
def baseEnd_2246002 : Nat := 1153278576959626740545831

theorem tailTrace_2246002 : CollatzResearch.WordTrace tailWord_2246002 prefixEnd_2246002 1153278576959626740545831 := by
  unfold tailWord_2246002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479605702281453861955065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54612281872750543631880173 20479605702281453861955065)
  ·
    refine ⟨15359704276711090396466299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20479605702281453861955065 15359704276711090396466299)
    ·
      refine ⟨23039556415066635594699449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15359704276711090396466299 23039556415066635594699449)
      ·
        refine ⟨17279667311299976696024587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23039556415066635594699449 17279667311299976696024587)
        ·
          refine ⟨25919500966949965044036881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17279667311299976696024587 25919500966949965044036881)
          ·
            refine ⟨19439625725212473783027661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25919500966949965044036881 19439625725212473783027661)
            ·
              refine ⟨7289859646954677668635373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19439625725212473783027661 7289859646954677668635373)
              ·
                refine ⟨2733697367608004125738265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7289859646954677668635373 2733697367608004125738265)
                ·
                  refine ⟨2050273025706003094303699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2733697367608004125738265 2050273025706003094303699)
                  ·
                    refine ⟨3075409538559004641455549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2050273025706003094303699 3075409538559004641455549)
                    ·
                      refine ⟨1153278576959626740545831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075409538559004641455549 1153278576959626740545831)
                      ·
                        rfl

theorem cell23_2246002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2246002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246002 prefixEnd_2246002 := by exact prefixLift 2246002
  have htrace : WordTrace (prefixWord ++ tailWord_2246002) baseStart_2246002 baseEnd_2246002 := by
    simpa [prefixWord, tailWord_2246002, baseEnd_2246002] using wordTrace_append hprefix tailTrace_2246002
  have hstable : (prefixWord ++ tailWord_2246002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246002).length < 2 ^ (prefixWord ++ tailWord_2246002).sum := by decide
  have hdescent : baseEnd_2246002 < baseStart_2246002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246028 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2246028 : Nat := 118140960795 + 2246028 * 2 ^ 59
def prefixEnd_2246028 : Nat := 4983230072969 + 3 ^ 40 * 2246028 * 2
def baseEnd_2246028 : Nat := 1153291927456643638820711

theorem tailTrace_2246028 : CollatzResearch.WordTrace tailWord_2246028 prefixEnd_2246028 1153291927456643638820711 := by
  unfold tailWord_2246028
  simp only [CollatzResearch.WordTrace]
  refine ⟨40959685553515810944133369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54612914071354414592177825 40959685553515810944133369)
  ·
    refine ⟨30719764165136858208100027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40959685553515810944133369 30719764165136858208100027)
    ·
      refine ⟨46079646247705287312150041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30719764165136858208100027 46079646247705287312150041)
      ·
        refine ⟨34559734685778965484112531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46079646247705287312150041 34559734685778965484112531)
        ·
          refine ⟨51839602028668448226168797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34559734685778965484112531 51839602028668448226168797)
          ·
            refine ⟨19439850760750668084813299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51839602028668448226168797 19439850760750668084813299)
            ·
              refine ⟨29159776141126002127219949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19439850760750668084813299 29159776141126002127219949)
              ·
                refine ⟨10934916052922250797707481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29159776141126002127219949 10934916052922250797707481)
                ·
                  refine ⟨8201187039691688098280611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10934916052922250797707481 8201187039691688098280611)
                  ·
                    refine ⟨12301780559537532147420917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8201187039691688098280611 12301780559537532147420917)
                    ·
                      refine ⟨1153291927456643638820711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12301780559537532147420917 1153291927456643638820711)
                      ·
                        rfl

theorem cell23_2246028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2246028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246028 prefixEnd_2246028 := by exact prefixLift 2246028
  have htrace : WordTrace (prefixWord ++ tailWord_2246028) baseStart_2246028 baseEnd_2246028 := by
    simpa [prefixWord, tailWord_2246028, baseEnd_2246028] using wordTrace_append hprefix tailTrace_2246028
  have hstable : (prefixWord ++ tailWord_2246028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246028).length < 2 ^ (prefixWord ++ tailWord_2246028).sum := by decide
  have hdescent : baseEnd_2246028 < baseStart_2246028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246045 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2246045 : Nat := 118140960795 + 2246045 * 2 ^ 59
def prefixEnd_2246045 : Nat := 4983230072969 + 3 ^ 40 * 2246045 * 2
def baseEnd_2246045 : Nat := 1153300656627770072308133

theorem tailTrace_2246045 : CollatzResearch.WordTrace tailWord_2246045 prefixEnd_2246045 1153300656627770072308133 := by
  unfold tailWord_2246045
  simp only [CollatzResearch.WordTrace]
  refine ⟨81919991147970033791635589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54613327431980022527757059 81919991147970033791635589)
  ·
    refine ⟨15359998340244381335931673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81919991147970033791635589 15359998340244381335931673)
    ·
      refine ⟨11519998755183286001948755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15359998340244381335931673 11519998755183286001948755)
      ·
        refine ⟨17279998132774929002923133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11519998755183286001948755 17279998132774929002923133)
        ·
          refine ⟨6479999299790598376096175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17279998132774929002923133 6479999299790598376096175)
          ·
            refine ⟨9719998949685897564144263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6479999299790598376096175 9719998949685897564144263)
            ·
              refine ⟨14579998424528846346216395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9719998949685897564144263 14579998424528846346216395)
              ·
                refine ⟨21869997636793269519324593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14579998424528846346216395 21869997636793269519324593)
                ·
                  refine ⟨16402498227594952139493445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21869997636793269519324593 16402498227594952139493445)
                  ·
                    refine ⟨3075468417674053526155021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16402498227594952139493445 3075468417674053526155021)
                    ·
                      refine ⟨1153300656627770072308133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3075468417674053526155021 1153300656627770072308133)
                      ·
                        rfl

theorem cell23_2246045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2246045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246045 prefixEnd_2246045 := by exact prefixLift 2246045
  have htrace : WordTrace (prefixWord ++ tailWord_2246045) baseStart_2246045 baseEnd_2246045 := by
    simpa [prefixWord, tailWord_2246045, baseEnd_2246045] using wordTrace_append hprefix tailTrace_2246045
  have hstable : (prefixWord ++ tailWord_2246045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246045).length < 2 ^ (prefixWord ++ tailWord_2246045).sum := by decide
  have hdescent : baseEnd_2246045 < baseStart_2246045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246048 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 7]
def baseStart_2246048 : Nat := 118140960795 + 2246048 * 2 ^ 59
def prefixEnd_2246048 : Nat := 4983230072969 + 3 ^ 40 * 2246048 * 2
def baseEnd_2246048 : Nat := 128144688563303728952291

theorem tailTrace_2246048 : CollatzResearch.WordTrace tailWord_2246048 prefixEnd_2246048 128144688563303728952291 := by
  unfold tailWord_2246048
  simp only [CollatzResearch.WordTrace]
  refine ⟨40960050283479582651997399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54613400377972776869329865 40960050283479582651997399)
  ·
    refine ⟨61440075425219373977996099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40960050283479582651997399 61440075425219373977996099)
    ·
      refine ⟨92160113137829060966994149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61440075425219373977996099 92160113137829060966994149)
      ·
        refine ⟨17280021213342948931311403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92160113137829060966994149 17280021213342948931311403)
        ·
          refine ⟨25920031820014423396967105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17280021213342948931311403 25920031820014423396967105)
          ·
            refine ⟨19440023865010817547725329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25920031820014423396967105 19440023865010817547725329)
            ·
              refine ⟨14580017898758113160793997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19440023865010817547725329 14580017898758113160793997)
              ·
                refine ⟨5467506712034292435297749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14580017898758113160793997 5467506712034292435297749)
                ·
                  refine ⟨128144688563303728952291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5467506712034292435297749 128144688563303728952291)
                  ·
                    rfl

theorem cell23_2246048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_2246048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246048 prefixEnd_2246048 := by exact prefixLift 2246048
  have htrace : WordTrace (prefixWord ++ tailWord_2246048) baseStart_2246048 baseEnd_2246048 := by
    simpa [prefixWord, tailWord_2246048, baseEnd_2246048] using wordTrace_append hprefix tailTrace_2246048
  have hstable : (prefixWord ++ tailWord_2246048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246048).length < 2 ^ (prefixWord ++ tailWord_2246048).sum := by decide
  have hdescent : baseEnd_2246048 < baseStart_2246048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246055 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2246055 : Nat := 118140960795 + 2246055 * 2 ^ 59
def prefixEnd_2246055 : Nat := 4983230072969 + 3 ^ 40 * 2246055 * 2
def baseEnd_2246055 : Nat := 1153305791434315033183087

theorem tailTrace_2246055 : CollatzResearch.WordTrace tailWord_2246055 prefixEnd_2246055 1153305791434315033183087 := by
  unfold tailWord_2246055
  simp only [CollatzResearch.WordTrace]
  refine ⟨81920355877933805499499619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54613570585289203666333079 81920355877933805499499619)
  ·
    refine ⟨122880533816900708249249429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81920355877933805499499619 122880533816900708249249429)
    ·
      refine ⟨5760025022667220699183567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122880533816900708249249429 5760025022667220699183567)
      ·
        refine ⟨8640037534000831048775351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760025022667220699183567 8640037534000831048775351)
        ·
          refine ⟨12960056301001246573163027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640037534000831048775351 12960056301001246573163027)
          ·
            refine ⟨19440084451501869859744541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12960056301001246573163027 19440084451501869859744541)
            ·
              refine ⟨7290031669313201197404203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19440084451501869859744541 7290031669313201197404203)
              ·
                refine ⟨10935047503969801796106305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7290031669313201197404203 10935047503969801796106305)
                ·
                  refine ⟨8201285627977351347079729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10935047503969801796106305 8201285627977351347079729)
                  ·
                    refine ⟨6150964220983013510309797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8201285627977351347079729 6150964220983013510309797)
                    ·
                      refine ⟨1153305791434315033183087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6150964220983013510309797 1153305791434315033183087)
                      ·
                        rfl

theorem cell23_2246055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2246055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246055 prefixEnd_2246055 := by exact prefixLift 2246055
  have htrace : WordTrace (prefixWord ++ tailWord_2246055) baseStart_2246055 baseEnd_2246055 := by
    simpa [prefixWord, tailWord_2246055, baseEnd_2246055] using wordTrace_append hprefix tailTrace_2246055
  have hstable : (prefixWord ++ tailWord_2246055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246055).length < 2 ^ (prefixWord ++ tailWord_2246055).sum := by decide
  have hdescent : baseEnd_2246055 < baseStart_2246055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246115 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2246115 : Nat := 118140960795 + 2246115 * 2 ^ 59
def prefixEnd_2246115 : Nat := 4983230072969 + 3 ^ 40 * 2246115 * 2
def baseEnd_2246115 : Nat := 1153336600273584798432811

theorem tailTrace_2246115 : CollatzResearch.WordTrace tailWord_2246115 prefixEnd_2246115 1153336600273584798432811 := by
  unfold tailWord_2246115
  simp only [CollatzResearch.WordTrace]
  refine ⟨81922544257716435746683799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54615029505144290497789199 81922544257716435746683799)
  ·
    refine ⟨122883816386574653620025699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81922544257716435746683799 122883816386574653620025699)
    ·
      refine ⟨184325724579861980430038549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122883816386574653620025699 184325724579861980430038549)
      ·
        refine ⟨8640268339681030332658057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184325724579861980430038549 8640268339681030332658057)
        ·
          refine ⟨6480201254760772749493543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8640268339681030332658057 6480201254760772749493543)
          ·
            refine ⟨9720301882141159124240315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6480201254760772749493543 9720301882141159124240315)
            ·
              refine ⟨14580452823211738686360473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9720301882141159124240315 14580452823211738686360473)
              ·
                refine ⟨10935339617408804014770355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14580452823211738686360473 10935339617408804014770355)
                ·
                  refine ⟨16403009426113206022155533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10935339617408804014770355 16403009426113206022155533)
                  ·
                    refine ⟨6151128534792452258308325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16403009426113206022155533 6151128534792452258308325)
                    ·
                      refine ⟨1153336600273584798432811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6151128534792452258308325 1153336600273584798432811)
                      ·
                        rfl

theorem cell23_2246115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2246115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246115 prefixEnd_2246115 := by exact prefixLift 2246115
  have htrace : WordTrace (prefixWord ++ tailWord_2246115) baseStart_2246115 baseEnd_2246115 := by
    simpa [prefixWord, tailWord_2246115, baseEnd_2246115] using wordTrace_append hprefix tailTrace_2246115
  have hstable : (prefixWord ++ tailWord_2246115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246115).length < 2 ^ (prefixWord ++ tailWord_2246115).sum := by decide
  have hdescent : baseEnd_2246115 < baseStart_2246115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246138 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_2246138 : Nat := 118140960795 + 2246138 * 2 ^ 59
def prefixEnd_2246138 : Nat := 4983230072969 + 3 ^ 40 * 2246138 * 2
def baseEnd_2246138 : Nat := 128149823369848689827245

theorem tailTrace_2246138 : CollatzResearch.WordTrace tailWord_2246138 prefixEnd_2246138 128149823369848689827245 := by
  unfold tailWord_2246138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20480845784158277668692767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54615588757755407116514045 20480845784158277668692767)
  ·
    refine ⟨30721268676237416503039151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20480845784158277668692767 30721268676237416503039151)
    ·
      refine ⟨46081903014356124754558727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30721268676237416503039151 46081903014356124754558727)
      ·
        refine ⟨69122854521534187131838091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46081903014356124754558727 69122854521534187131838091)
        ·
          refine ⟨103684281782301280697757137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69122854521534187131838091 103684281782301280697757137)
          ·
            refine ⟨77763211336725960523317853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103684281782301280697757137 77763211336725960523317853)
            ·
              refine ⟨29161204251272235196244195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77763211336725960523317853 29161204251272235196244195)
              ·
                refine ⟨43741806376908352794366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29161204251272235196244195 43741806376908352794366293)
                ·
                  refine ⟨128149823369848689827245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43741806376908352794366293 128149823369848689827245)
                  ·
                    rfl

theorem cell23_2246138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_2246138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246138 prefixEnd_2246138 := by exact prefixLift 2246138
  have htrace : WordTrace (prefixWord ++ tailWord_2246138) baseStart_2246138 baseEnd_2246138 := by
    simpa [prefixWord, tailWord_2246138, baseEnd_2246138] using wordTrace_append hprefix tailTrace_2246138
  have hstable : (prefixWord ++ tailWord_2246138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246138).length < 2 ^ (prefixWord ++ tailWord_2246138).sum := by decide
  have hdescent : baseEnd_2246138 < baseStart_2246138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246150 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2246150 : Nat := 118140960795 + 2246150 * 2 ^ 59
def prefixEnd_2246150 : Nat := 4983230072969 + 3 ^ 40 * 2246150 * 2
def baseEnd_2246150 : Nat := 128150508010721351277239

theorem tailTrace_2246150 : CollatzResearch.WordTrace tailWord_2246150 prefixEnd_2246150 128150508010721351277239 := by
  unfold tailWord_2246150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560119400393426147631497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54615880541726424482805269 2560119400393426147631497)
  ·
    refine ⟨1920089550295069610723623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560119400393426147631497 1920089550295069610723623)
    ·
      refine ⟨2880134325442604416085435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920089550295069610723623 2880134325442604416085435)
      ·
        refine ⟨4320201488163906624128153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880134325442604416085435 4320201488163906624128153)
        ·
          refine ⟨3240151116122929968096115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320201488163906624128153 3240151116122929968096115)
          ·
            refine ⟨4860226674184394952144173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240151116122929968096115 4860226674184394952144173)
            ·
              refine ⟨1822585002819148107054065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4860226674184394952144173 1822585002819148107054065)
              ·
                refine ⟨1366938752114361080290549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822585002819148107054065 1366938752114361080290549)
                ·
                  refine ⟨128150508010721351277239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366938752114361080290549 128150508010721351277239)
                  ·
                    rfl

theorem cell23_2246150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2246150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246150 prefixEnd_2246150 := by exact prefixLift 2246150
  have htrace : WordTrace (prefixWord ++ tailWord_2246150) baseStart_2246150 baseEnd_2246150 := by
    simpa [prefixWord, tailWord_2246150, baseEnd_2246150] using wordTrace_append hprefix tailTrace_2246150
  have hstable : (prefixWord ++ tailWord_2246150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246150).length < 2 ^ (prefixWord ++ tailWord_2246150).sum := by decide
  have hdescent : baseEnd_2246150 < baseStart_2246150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246209 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2246209 : Nat := 118140960795 + 2246209 * 2 ^ 59
def prefixEnd_2246209 : Nat := 4983230072969 + 3 ^ 40 * 2246209 * 2
def baseEnd_2246209 : Nat := 1153384867455107430657379

theorem tailTrace_2246209 : CollatzResearch.WordTrace tailWord_2246209 prefixEnd_2246209 1153384867455107430657379 := by
  unfold tailWord_2246209
  simp only [CollatzResearch.WordTrace]
  refine ⟨81925972719375889800605681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54617315146250593200403787 81925972719375889800605681)
  ·
    refine ⟨61444479539531917350454261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81925972719375889800605681 61444479539531917350454261)
    ·
      refine ⟨5760419956831117251605087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61444479539531917350454261 5760419956831117251605087)
      ·
        refine ⟨8640629935246675877407631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760419956831117251605087 8640629935246675877407631)
        ·
          refine ⟨12960944902870013816111447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8640629935246675877407631 12960944902870013816111447)
          ·
            refine ⟨19441417354305020724167171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12960944902870013816111447 19441417354305020724167171)
            ·
              refine ⟨29162126031457531086250757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19441417354305020724167171 29162126031457531086250757)
              ·
                refine ⟨5467898630898287078672017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29162126031457531086250757 5467898630898287078672017)
                ·
                  refine ⟨4100923973173715309004013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5467898630898287078672017 4100923973173715309004013)
                  ·
                    refine ⟨1537846489940143240876505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4100923973173715309004013 1537846489940143240876505)
                    ·
                      refine ⟨1153384867455107430657379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537846489940143240876505 1153384867455107430657379)
                      ·
                        rfl

theorem cell23_2246209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2246209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246209 prefixEnd_2246209 := by exact prefixLift 2246209
  have htrace : WordTrace (prefixWord ++ tailWord_2246209) baseStart_2246209 baseEnd_2246209 := by
    simpa [prefixWord, tailWord_2246209, baseEnd_2246209] using wordTrace_append hprefix tailTrace_2246209
  have hstable : (prefixWord ++ tailWord_2246209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246209).length < 2 ^ (prefixWord ++ tailWord_2246209).sum := by decide
  have hdescent : baseEnd_2246209 < baseStart_2246209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246222 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_2246222 : Nat := 118140960795 + 2246222 * 2 ^ 59
def prefixEnd_2246222 : Nat := 4983230072969 + 3 ^ 40 * 2246222 * 2
def baseEnd_2246222 : Nat := 1153391542703615879794819

theorem tailTrace_2246222 : CollatzResearch.WordTrace tailWord_2246222 prefixEnd_2246222 1153391542703615879794819 := by
  unfold tailWord_2246222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240805858541099127603615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54617631245552528680552613 10240805858541099127603615)
  ·
    refine ⟨15361208787811648691405423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240805858541099127603615 15361208787811648691405423)
    ·
      refine ⟨23041813181717473037108135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15361208787811648691405423 23041813181717473037108135)
      ·
        refine ⟨34562719772576209555662203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23041813181717473037108135 34562719772576209555662203)
        ·
          refine ⟨51844079658864314333493305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34562719772576209555662203 51844079658864314333493305)
          ·
            refine ⟨38883059744148235750119979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51844079658864314333493305 38883059744148235750119979)
            ·
              refine ⟨58324589616222353625179969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38883059744148235750119979 58324589616222353625179969)
              ·
                refine ⟨43743442212166765218884977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58324589616222353625179969 43743442212166765218884977)
                ·
                  refine ⟨32807581659125073914163733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43743442212166765218884977 32807581659125073914163733)
                  ·
                    refine ⟨1537855390271487839726425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32807581659125073914163733 1537855390271487839726425)
                    ·
                      refine ⟨1153391542703615879794819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1537855390271487839726425 1153391542703615879794819)
                      ·
                        rfl

theorem cell23_2246222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_2246222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246222 prefixEnd_2246222 := by exact prefixLift 2246222
  have htrace : WordTrace (prefixWord ++ tailWord_2246222) baseStart_2246222 baseEnd_2246222 := by
    simpa [prefixWord, tailWord_2246222, baseEnd_2246222] using wordTrace_append hprefix tailTrace_2246222
  have hstable : (prefixWord ++ tailWord_2246222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246222).length < 2 ^ (prefixWord ++ tailWord_2246222).sum := by decide
  have hdescent : baseEnd_2246222 < baseStart_2246222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246225 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_2246225 : Nat := 118140960795 + 2246225 * 2 ^ 59
def prefixEnd_2246225 : Nat := 4983230072969 + 3 ^ 40 * 2246225 * 2
def baseEnd_2246225 : Nat := 1153393083145579368057305

theorem tailTrace_2246225 : CollatzResearch.WordTrace tailWord_2246225 prefixEnd_2246225 1153393083145579368057305 := by
  unfold tailWord_2246225
  simp only [CollatzResearch.WordTrace]
  refine ⟨81926556287317924533188129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54617704191545283022125419 81926556287317924533188129)
  ·
    refine ⟨61444917215488443399891097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81926556287317924533188129 61444917215488443399891097)
    ·
      refine ⟨46083687911616332549918323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61444917215488443399891097 46083687911616332549918323)
      ·
        refine ⟨69125531867424498824877485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46083687911616332549918323 69125531867424498824877485)
        ·
          refine ⟨25922074450284187059329057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69125531867424498824877485 25922074450284187059329057)
          ·
            refine ⟨19441555837713140294496793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25922074450284187059329057 19441555837713140294496793)
            ·
              refine ⟨14581166878284855220872595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19441555837713140294496793 14581166878284855220872595)
              ·
                refine ⟨21871750317427282831308893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14581166878284855220872595 21871750317427282831308893)
                ·
                  refine ⟨8201906369035231061740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21871750317427282831308893 8201906369035231061740835)
                  ·
                    refine ⟨12302859553552846592611253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8201906369035231061740835 12302859553552846592611253)
                    ·
                      refine ⟨1153393083145579368057305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12302859553552846592611253 1153393083145579368057305)
                      ·
                        rfl

theorem cell23_2246225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_2246225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246225 prefixEnd_2246225 := by exact prefixLift 2246225
  have htrace : WordTrace (prefixWord ++ tailWord_2246225) baseStart_2246225 baseEnd_2246225 := by
    simpa [prefixWord, tailWord_2246225, baseEnd_2246225] using wordTrace_append hprefix tailTrace_2246225
  have hstable : (prefixWord ++ tailWord_2246225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246225).length < 2 ^ (prefixWord ++ tailWord_2246225).sum := by decide
  have hdescent : baseEnd_2246225 < baseStart_2246225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2246253 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2246253 : Nat := 118140960795 + 2246253 * 2 ^ 59
def prefixEnd_2246253 : Nat := 4983230072969 + 3 ^ 40 * 2246253 * 2
def baseEnd_2246253 : Nat := 384469153534635086169059

theorem tailTrace_2246253 : CollatzResearch.WordTrace tailWord_2246253 prefixEnd_2246253 384469153534635086169059 := by
  unfold tailWord_2246253
  simp only [CollatzResearch.WordTrace]
  refine ⟨81927577531216485315207413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54618385020810990210138275 81927577531216485315207413)
  ·
    refine ⟨7680710393551545498300695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81927577531216485315207413 7680710393551545498300695)
    ·
      refine ⟨11521065590327318247451043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680710393551545498300695 11521065590327318247451043)
      ·
        refine ⟨17281598385490977371176565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11521065590327318247451043 17281598385490977371176565)
        ·
          refine ⟨1620149848639779128547803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17281598385490977371176565 1620149848639779128547803)
          ·
            refine ⟨2430224772959668692821705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620149848639779128547803 2430224772959668692821705)
            ·
              refine ⟨1822668579719751519616279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430224772959668692821705 1822668579719751519616279)
              ·
                refine ⟨2734002869579627279424419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822668579719751519616279 2734002869579627279424419)
                ·
                  refine ⟨4101004304369440919136629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2734002869579627279424419 4101004304369440919136629)
                  ·
                    refine ⟨384469153534635086169059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4101004304369440919136629 384469153534635086169059)
                    ·
                      rfl

theorem cell23_2246253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2246253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2246253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2246253 prefixEnd_2246253 := by exact prefixLift 2246253
  have htrace : WordTrace (prefixWord ++ tailWord_2246253) baseStart_2246253 baseEnd_2246253 := by
    simpa [prefixWord, tailWord_2246253, baseEnd_2246253] using wordTrace_append hprefix tailTrace_2246253
  have hstable : (prefixWord ++ tailWord_2246253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2246253).length < 2 ^ (prefixWord ++ tailWord_2246253).sum := by decide
  have hdescent : baseEnd_2246253 < baseStart_2246253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2246253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
