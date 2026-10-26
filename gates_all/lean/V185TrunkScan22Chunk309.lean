import V185TrunkScan22Chunk308

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2757506 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2757506 : Nat := 118140960795 + 2757506 * 2 ^ 59
def prefixEnd_2757506 : Nat := 4983230072969 + 3 ^ 40 * 2757506 * 2
def baseEnd_2757506 : Nat := 943950657104662319195645

theorem tailTrace_2757506 : CollatzResearch.WordTrace tailWord_2757506 prefixEnd_2757506 943950657104662319195645 := by
  unfold tailWord_2757506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143626587008545344025093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67049670898689454250733581 25143626587008545344025093)
  ·
    refine ⟨4714429985064102252004705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25143626587008545344025093 4714429985064102252004705)
    ·
      refine ⟨3535822488798076689003529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4714429985064102252004705 3535822488798076689003529)
      ·
        refine ⟨2651866866598557516752647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3535822488798076689003529 2651866866598557516752647)
        ·
          refine ⟨3977800299897836275128971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651866866598557516752647 3977800299897836275128971)
          ·
            refine ⟨5966700449846754412693457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977800299897836275128971 5966700449846754412693457)
            ·
              refine ⟨4475025337385065809520093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966700449846754412693457 4475025337385065809520093)
              ·
                refine ⟨1678134501519399678570035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4475025337385065809520093 1678134501519399678570035)
                ·
                  refine ⟨2517201752279099517855053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678134501519399678570035 2517201752279099517855053)
                  ·
                    refine ⟨943950657104662319195645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517201752279099517855053 943950657104662319195645)
                    ·
                      rfl

theorem cell22_2757506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2757506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757506 prefixEnd_2757506 := by exact prefixLift 2757506
  have htrace : WordTrace (prefixWord ++ tailWord_2757506) baseStart_2757506 baseEnd_2757506 := by
    simpa [prefixWord, tailWord_2757506, baseEnd_2757506] using wordTrace_append hprefix tailTrace_2757506
  have hstable : (prefixWord ++ tailWord_2757506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757506).length < 2 ^ (prefixWord ++ tailWord_2757506).sum := by decide
  have hdescent : baseEnd_2757506 < baseStart_2757506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757513 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 4]
def baseStart_2757513 : Nat := 118140960795 + 2757513 * 2 ^ 59
def prefixEnd_2757513 : Nat := 4983230072969 + 3 ^ 40 * 2757513 * 2
def baseEnd_2757513 : Nat := 314651017782572211423541

theorem tailTrace_2757513 : CollatzResearch.WordTrace tailWord_2757513 prefixEnd_2757513 314651017782572211423541 := by
  unfold tailWord_2757513
  simp only [CollatzResearch.WordTrace]
  refine ⟨100574761659008821571605193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67049841106005881047736795 100574761659008821571605193)
  ·
    refine ⟨75431071244256616178703895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100574761659008821571605193 75431071244256616178703895)
    ·
      refine ⟨113146606866384924268055843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75431071244256616178703895 113146606866384924268055843)
      ·
        refine ⟨169719910299577386402083765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113146606866384924268055843 169719910299577386402083765)
        ·
          refine ⟨15911241590585379975195353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169719910299577386402083765 15911241590585379975195353)
          ·
            refine ⟨11933431192939034981396515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15911241590585379975195353 11933431192939034981396515)
            ·
              refine ⟨17900146789408552472094773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11933431192939034981396515 17900146789408552472094773)
              ·
                refine ⟨1678138761507051794258885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17900146789408552472094773 1678138761507051794258885)
                ·
                  refine ⟨314651017782572211423541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678138761507051794258885 314651017782572211423541)
                  ·
                    rfl

theorem cell22_2757513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_2757513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757513 prefixEnd_2757513 := by exact prefixLift 2757513
  have htrace : WordTrace (prefixWord ++ tailWord_2757513) baseStart_2757513 baseEnd_2757513 := by
    simpa [prefixWord, tailWord_2757513, baseEnd_2757513] using wordTrace_append hprefix tailTrace_2757513
  have hstable : (prefixWord ++ tailWord_2757513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757513).length < 2 ^ (prefixWord ++ tailWord_2757513).sum := by decide
  have hdescent : baseEnd_2757513 < baseStart_2757513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757545 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_2757545 : Nat := 118140960795 + 2757545 * 2 ^ 59
def prefixEnd_2757545 : Nat := 4983230072969 + 3 ^ 40 * 2757545 * 2
def baseEnd_2757545 : Nat := 943964007601679217470525

theorem tailTrace_2757545 : CollatzResearch.WordTrace tailWord_2757545 prefixEnd_2757545 943964007601679217470525 := by
  unfold tailWord_2757545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100575928794892891036770089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67050619196595260691180059 100575928794892891036770089)
  ·
    refine ⟨75431946596169668277577567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100575928794892891036770089 75431946596169668277577567)
    ·
      refine ⟨113147919894254502416366351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75431946596169668277577567 113147919894254502416366351)
      ·
        refine ⟨169721879841381753624549527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113147919894254502416366351 169721879841381753624549527)
        ·
          refine ⟨254582819762072630436824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169721879841381753624549527 254582819762072630436824291)
          ·
            refine ⟨381874229643108945655236437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254582819762072630436824291 381874229643108945655236437)
            ·
              refine ⟨2237544314315091478448651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 381874229643108945655236437 2237544314315091478448651)
              ·
                refine ⟨3356316471472637217672977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237544314315091478448651 3356316471472637217672977)
                ·
                  refine ⟨2517237353604477913254733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356316471472637217672977 2517237353604477913254733)
                  ·
                    refine ⟨943964007601679217470525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517237353604477913254733 943964007601679217470525)
                    ·
                      rfl

theorem cell22_2757545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_2757545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757545 prefixEnd_2757545 := by exact prefixLift 2757545
  have htrace : WordTrace (prefixWord ++ tailWord_2757545) baseStart_2757545 baseEnd_2757545 := by
    simpa [prefixWord, tailWord_2757545, baseEnd_2757545] using wordTrace_append hprefix tailTrace_2757545
  have hstable : (prefixWord ++ tailWord_2757545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757545).length < 2 ^ (prefixWord ++ tailWord_2757545).sum := by decide
  have hdescent : baseEnd_2757545 < baseStart_2757545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757581 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2757581 : Nat := 118140960795 + 2757581 * 2 ^ 59
def prefixEnd_2757581 : Nat := 4983230072969 + 3 ^ 40 * 2757581 * 2
def baseEnd_2757581 : Nat := 314658777045795707856805

theorem tailTrace_2757581 : CollatzResearch.WordTrace tailWord_2757581 prefixEnd_2757581 314658777045795707856805 := by
  unfold tailWord_2757581
  simp only [CollatzResearch.WordTrace]
  refine ⟨100577241822762469185080597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67051494548508312790053731 100577241822762469185080597)
  ·
    refine ⟨4714558210441990743050653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100577241822762469185080597 4714558210441990743050653)
    ·
      refine ⟨1767959328915746528643995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4714558210441990743050653 1767959328915746528643995)
      ·
        refine ⟨2651938993373619792965993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767959328915746528643995 2651938993373619792965993)
        ·
          refine ⟨1988954245030214844724495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651938993373619792965993 1988954245030214844724495)
          ·
            refine ⟨2983431367545322267086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988954245030214844724495 2983431367545322267086743)
            ·
              refine ⟨4475147051317983400630115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983431367545322267086743 4475147051317983400630115)
              ·
                refine ⟨6712720576976975100945173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475147051317983400630115 6712720576976975100945173)
                ·
                  refine ⟨314658777045795707856805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6712720576976975100945173 314658777045795707856805)
                  ·
                    rfl

theorem cell22_2757581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2757581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757581 prefixEnd_2757581 := by exact prefixLift 2757581
  have htrace : WordTrace (prefixWord ++ tailWord_2757581) baseStart_2757581 baseEnd_2757581 := by
    simpa [prefixWord, tailWord_2757581, baseEnd_2757581] using wordTrace_append hprefix tailTrace_2757581
  have hstable : (prefixWord ++ tailWord_2757581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757581).length < 2 ^ (prefixWord ++ tailWord_2757581).sum := by decide
  have hdescent : baseEnd_2757581 < baseStart_2757581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757601 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2757601 : Nat := 118140960795 + 2757601 * 2 ^ 59
def prefixEnd_2757601 : Nat := 4983230072969 + 3 ^ 40 * 2757601 * 2
def baseEnd_2757601 : Nat := 943983177546113738070353

theorem tailTrace_2757601 : CollatzResearch.WordTrace tailWord_2757601 prefixEnd_2757601 943983177546113738070353 := by
  unfold tailWord_2757601
  simp only [CollatzResearch.WordTrace]
  refine ⟨100577971282690012600808657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67051980855126675067205771 100577971282690012600808657)
  ·
    refine ⟨75433478462017509450606493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100577971282690012600808657 75433478462017509450606493)
    ·
      refine ⟨28287554423256566043977435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75433478462017509450606493 28287554423256566043977435)
      ·
        refine ⟨42431331634884849065966153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28287554423256566043977435 42431331634884849065966153)
        ·
          refine ⟨31823498726163636799474615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42431331634884849065966153 31823498726163636799474615)
          ·
            refine ⟨47735248089245455199211923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31823498726163636799474615 47735248089245455199211923)
            ·
              refine ⟨71602872133868182798817885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47735248089245455199211923 71602872133868182798817885)
              ·
                refine ⟨26851077050200568549556707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71602872133868182798817885 26851077050200568549556707)
                ·
                  refine ⟨40276615575300852824335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26851077050200568549556707 40276615575300852824335061)
                  ·
                    refine ⟨943983177546113738070353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40276615575300852824335061 943983177546113738070353)
                    ·
                      rfl

theorem cell22_2757601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2757601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757601 prefixEnd_2757601 := by exact prefixLift 2757601
  have htrace : WordTrace (prefixWord ++ tailWord_2757601) baseStart_2757601 baseEnd_2757601 := by
    simpa [prefixWord, tailWord_2757601, baseEnd_2757601] using wordTrace_append hprefix tailTrace_2757601
  have hstable : (prefixWord ++ tailWord_2757601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757601).length < 2 ^ (prefixWord ++ tailWord_2757601).sum := by decide
  have hdescent : baseEnd_2757601 < baseStart_2757601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757603 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 5]
def baseStart_2757603 : Nat := 118140960795 + 2757603 * 2 ^ 59
def prefixEnd_2757603 : Nat := 4983230072969 + 3 ^ 40 * 2757603 * 2
def baseEnd_2757603 : Nat := 314661287395662133173449

theorem tailTrace_2757603 : CollatzResearch.WordTrace tailWord_2757603 prefixEnd_2757603 314661287395662133173449 := by
  unfold tailWord_2757603
  simp only [CollatzResearch.WordTrace]
  refine ⟨100578044228682766942381463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67052029485788511294920975 100578044228682766942381463)
  ·
    refine ⟨150867066343024150413572195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100578044228682766942381463 150867066343024150413572195)
    ·
      refine ⟨226300599514536225620358293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150867066343024150413572195 226300599514536225620358293)
      ·
        refine ⟨10607840602243885575954295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226300599514536225620358293 10607840602243885575954295)
        ·
          refine ⟨15911760903365828363931443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607840602243885575954295 15911760903365828363931443)
          ·
            refine ⟨23867641355048742545897165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15911760903365828363931443 23867641355048742545897165)
            ·
              refine ⟨8950365508143278454711437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23867641355048742545897165 8950365508143278454711437)
              ·
                refine ⟨3356387065553729420516789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8950365508143278454711437 3356387065553729420516789)
                ·
                  refine ⟨314661287395662133173449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356387065553729420516789 314661287395662133173449)
                  ·
                    rfl

theorem cell22_2757603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].length) (baseStart_2757603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757603 prefixEnd_2757603 := by exact prefixLift 2757603
  have htrace : WordTrace (prefixWord ++ tailWord_2757603) baseStart_2757603 baseEnd_2757603 := by
    simpa [prefixWord, tailWord_2757603, baseEnd_2757603] using wordTrace_append hprefix tailTrace_2757603
  have hstable : (prefixWord ++ tailWord_2757603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757603).length < 2 ^ (prefixWord ++ tailWord_2757603).sum := by decide
  have hdescent : baseEnd_2757603 < baseStart_2757603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757663 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_2757663 : Nat := 118140960795 + 2757663 * 2 ^ 59
def prefixEnd_2757663 : Nat := 4983230072969 + 3 ^ 40 * 2757663 * 2
def baseEnd_2757663 : Nat := 944004401413166243020163

theorem tailTrace_2757663 : CollatzResearch.WordTrace tailWord_2757663 prefixEnd_2757663 944004401413166243020163 := by
  unfold tailWord_2757663
  simp only [CollatzResearch.WordTrace]
  refine ⟨100580232608465397189565643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67053488405643598126377095 100580232608465397189565643)
  ·
    refine ⟨150870348912698095784348465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100580232608465397189565643 150870348912698095784348465)
    ·
      refine ⟨113152761684523571838261349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150870348912698095784348465 113152761684523571838261349)
      ·
        refine ⟨21216142815848169719674003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113152761684523571838261349 21216142815848169719674003)
        ·
          refine ⟨31824214223772254579511005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21216142815848169719674003 31824214223772254579511005)
          ·
            refine ⟨11934080333914595467316627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31824214223772254579511005 11934080333914595467316627)
            ·
              refine ⟨17901120500871893200974941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11934080333914595467316627 17901120500871893200974941)
              ·
                refine ⟨6712920187826959950365603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17901120500871893200974941 6712920187826959950365603)
                ·
                  refine ⟨10069380281740439925548405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6712920187826959950365603 10069380281740439925548405)
                  ·
                    refine ⟨944004401413166243020163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10069380281740439925548405 944004401413166243020163)
                    ·
                      rfl

theorem cell22_2757663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_2757663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757663 prefixEnd_2757663 := by exact prefixLift 2757663
  have htrace : WordTrace (prefixWord ++ tailWord_2757663) baseStart_2757663 baseEnd_2757663 := by
    simpa [prefixWord, tailWord_2757663, baseEnd_2757663] using wordTrace_append hprefix tailTrace_2757663
  have hstable : (prefixWord ++ tailWord_2757663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757663).length < 2 ^ (prefixWord ++ tailWord_2757663).sum := by decide
  have hdescent : baseEnd_2757663 < baseStart_2757663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757684 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2757684 : Nat := 118140960795 + 2757684 * 2 ^ 59
def prefixEnd_2757684 : Nat := 4983230072969 + 3 ^ 40 * 2757684 * 2
def baseEnd_2757684 : Nat := 944011590142329188245099

theorem tailTrace_2757684 : CollatzResearch.WordTrace tailWord_2757684 prefixEnd_2757684 944011590142329188245099 := by
  unfold tailWord_2757684
  simp only [CollatzResearch.WordTrace]
  refine ⟨50290499270694658888040053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67053999027592878517386737 50290499270694658888040053)
  ·
    refine ⟨4714734306627624270753755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50290499270694658888040053 4714734306627624270753755)
    ·
      refine ⟨7072101459941436406130633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714734306627624270753755 7072101459941436406130633)
      ·
        refine ⟨5304076094956077304597975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7072101459941436406130633 5304076094956077304597975)
        ·
          refine ⟨7956114142434115956896963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304076094956077304597975 7956114142434115956896963)
          ·
            refine ⟨11934171213651173935345445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956114142434115956896963 11934171213651173935345445)
            ·
              refine ⟨2237657102559595112877271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11934171213651173935345445 2237657102559595112877271)
              ·
                refine ⟨3356485653839392669315907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237657102559595112877271 3356485653839392669315907)
                ·
                  refine ⟨5034728480759089003973861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356485653839392669315907 5034728480759089003973861)
                  ·
                    refine ⟨944011590142329188245099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5034728480759089003973861 944011590142329188245099)
                    ·
                      rfl

theorem cell22_2757684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2757684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757684 prefixEnd_2757684 := by exact prefixLift 2757684
  have htrace : WordTrace (prefixWord ++ tailWord_2757684) baseStart_2757684 baseEnd_2757684 := by
    simpa [prefixWord, tailWord_2757684, baseEnd_2757684] using wordTrace_append hprefix tailTrace_2757684
  have hstable : (prefixWord ++ tailWord_2757684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757684).length < 2 ^ (prefixWord ++ tailWord_2757684).sum := by decide
  have hdescent : baseEnd_2757684 < baseStart_2757684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757693 : List Nat := [1, 4, 1, 3, 1, 3, 9]
def baseStart_2757693 : Nat := 118140960795 + 2757693 * 2 ^ 59
def prefixEnd_2757693 : Nat := 4983230072969 + 3 ^ 40 * 2757693 * 2
def baseEnd_2757693 : Nat := 34963506334305783880373

theorem tailTrace_2757693 : CollatzResearch.WordTrace tailWord_2757693 prefixEnd_2757693 34963506334305783880373 := by
  unfold tailWord_2757693
  simp only [CollatzResearch.WordTrace]
  refine ⟨100581326798356712313157733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67054217865571141542105155 100581326798356712313157733)
  ·
    refine ⟨18858998774691883558717075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100581326798356712313157733 18858998774691883558717075)
    ·
      refine ⟨28288498162037825338075613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18858998774691883558717075 28288498162037825338075613)
      ·
        refine ⟨10608186810764184501778355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28288498162037825338075613 10608186810764184501778355)
        ·
          refine ⟨15912280216146276752667533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10608186810764184501778355 15912280216146276752667533)
          ·
            refine ⟨5967105081054853782250325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15912280216146276752667533 5967105081054853782250325)
            ·
              refine ⟨34963506334305783880373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5967105081054853782250325 34963506334305783880373)
              ·
                rfl

theorem cell22_2757693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 9].length) (baseStart_2757693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757693 prefixEnd_2757693 := by exact prefixLift 2757693
  have htrace : WordTrace (prefixWord ++ tailWord_2757693) baseStart_2757693 baseEnd_2757693 := by
    simpa [prefixWord, tailWord_2757693, baseEnd_2757693] using wordTrace_append hprefix tailTrace_2757693
  have hstable : (prefixWord ++ tailWord_2757693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757693).length < 2 ^ (prefixWord ++ tailWord_2757693).sum := by decide
  have hdescent : baseEnd_2757693 < baseStart_2757693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757697 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2757697 : Nat := 118140960795 + 2757697 * 2 ^ 59
def prefixEnd_2757697 : Nat := 4983230072969 + 3 ^ 40 * 2757697 * 2
def baseEnd_2757697 : Nat := 944016040308001487670059

theorem tailTrace_2757697 : CollatzResearch.WordTrace tailWord_2757697 prefixEnd_2757697 944016040308001487670059 := by
  unfold tailWord_2757697
  simp only [CollatzResearch.WordTrace]
  refine ⟨100581472690342220996303345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67054315126894813997535563 100581472690342220996303345)
  ·
    refine ⟨75436104517756665747227509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100581472690342220996303345 75436104517756665747227509)
    ·
      refine ⟨7072134798539687413802579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75436104517756665747227509 7072134798539687413802579)
      ·
        refine ⟨10608202197809531120703869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7072134798539687413802579 10608202197809531120703869)
        ·
          refine ⟨3978075824178574170263951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10608202197809531120703869 3978075824178574170263951)
          ·
            refine ⟨5967113736267861255395927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978075824178574170263951 5967113736267861255395927)
            ·
              refine ⟨8950670604401791883093891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967113736267861255395927 8950670604401791883093891)
              ·
                refine ⟨13426005906602687824640837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8950670604401791883093891 13426005906602687824640837)
                ·
                  refine ⟨2517376107488003967120157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13426005906602687824640837 2517376107488003967120157)
                  ·
                    refine ⟨944016040308001487670059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517376107488003967120157 944016040308001487670059)
                    ·
                      rfl

theorem cell22_2757697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2757697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757697 prefixEnd_2757697 := by exact prefixLift 2757697
  have htrace : WordTrace (prefixWord ++ tailWord_2757697) baseStart_2757697 baseEnd_2757697 := by
    simpa [prefixWord, tailWord_2757697, baseEnd_2757697] using wordTrace_append hprefix tailTrace_2757697
  have hstable : (prefixWord ++ tailWord_2757697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757697).length < 2 ^ (prefixWord ++ tailWord_2757697).sum := by decide
  have hdescent : baseEnd_2757697 < baseStart_2757697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757714 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2757714 : Nat := 118140960795 + 2757714 * 2 ^ 59
def prefixEnd_2757714 : Nat := 4983230072969 + 3 ^ 40 * 2757714 * 2
def baseEnd_2757714 : Nat := 944021859755419109995007

theorem tailTrace_2757714 : CollatzResearch.WordTrace tailWord_2757714 prefixEnd_2757714 944021859755419109995007 := by
  unfold tailWord_2757714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25145523182820158224918049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67054728487520421933114797 25145523182820158224918049)
  ·
    refine ⟨18859142387115118668688537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25145523182820158224918049 18859142387115118668688537)
    ·
      refine ⟨14144356790336339001516403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18859142387115118668688537 14144356790336339001516403)
      ·
        refine ⟨21216535185504508502274605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144356790336339001516403 21216535185504508502274605)
        ·
          refine ⟨7956200694564190688352977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21216535185504508502274605 7956200694564190688352977)
          ·
            refine ⟨5967150520923143016264733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7956200694564190688352977 5967150520923143016264733)
            ·
              refine ⟨2237681445346178631099275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5967150520923143016264733 2237681445346178631099275)
              ·
                refine ⟨3356522168019267946648913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237681445346178631099275 3356522168019267946648913)
                ·
                  refine ⟨2517391626014450959986685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356522168019267946648913 2517391626014450959986685)
                  ·
                    refine ⟨944021859755419109995007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517391626014450959986685 944021859755419109995007)
                    ·
                      rfl

theorem cell22_2757714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2757714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757714 prefixEnd_2757714 := by exact prefixLift 2757714
  have htrace : WordTrace (prefixWord ++ tailWord_2757714) baseStart_2757714 baseEnd_2757714 := by
    simpa [prefixWord, tailWord_2757714, baseEnd_2757714] using wordTrace_append hprefix tailTrace_2757714
  have hstable : (prefixWord ++ tailWord_2757714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757714).length < 2 ^ (prefixWord ++ tailWord_2757714).sum := by decide
  have hdescent : baseEnd_2757714 < baseStart_2757714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757817 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 4]
def baseStart_2757817 : Nat := 118140960795 + 2757817 * 2 ^ 59
def prefixEnd_2757817 : Nat := 4983230072969 + 3 ^ 40 * 2757817 * 2
def baseEnd_2757817 : Nat := 314685706253453724889897

theorem tailTrace_2757817 : CollatzResearch.WordTrace tailWord_2757817 prefixEnd_2757817 314685706253453724889897 := by
  unfold tailWord_2757817
  simp only [CollatzResearch.WordTrace]
  refine ⟨100585849449907481490671705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67057232966604987660447803 100585849449907481490671705)
  ·
    refine ⟨75439387087430611118003779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100585849449907481490671705 75439387087430611118003779)
    ·
      refine ⟨113159080631145916677005669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75439387087430611118003779 113159080631145916677005669)
      ·
        refine ⟨21217327618339859376938563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113159080631145916677005669 21217327618339859376938563)
        ·
          refine ⟨31825991427509789065407845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21217327618339859376938563 31825991427509789065407845)
          ·
            refine ⟨5967373392658085449763971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31825991427509789065407845 5967373392658085449763971)
            ·
              refine ⟨8951060088987128174645957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967373392658085449763971 8951060088987128174645957)
              ·
                refine ⟨1678323766685086532746117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8951060088987128174645957 1678323766685086532746117)
                ·
                  refine ⟨314685706253453724889897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678323766685086532746117 314685706253453724889897)
                  ·
                    rfl

theorem cell22_2757817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_2757817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757817 prefixEnd_2757817 := by exact prefixLift 2757817
  have htrace : WordTrace (prefixWord ++ tailWord_2757817) baseStart_2757817 baseEnd_2757817 := by
    simpa [prefixWord, tailWord_2757817, baseEnd_2757817] using wordTrace_append hprefix tailTrace_2757817
  have hstable : (prefixWord ++ tailWord_2757817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757817).length < 2 ^ (prefixWord ++ tailWord_2757817).sum := by decide
  have hdescent : baseEnd_2757817 < baseStart_2757817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757832 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_2757832 : Nat := 118140960795 + 2757832 * 2 ^ 59
def prefixEnd_2757832 : Nat := 4983230072969 + 3 ^ 40 * 2757832 * 2
def baseEnd_2757832 : Nat := 944062253566906135544645

theorem tailTrace_2757832 : CollatzResearch.WordTrace tailWord_2757832 prefixEnd_2757832 944062253566906135544645 := by
  unfold tailWord_2757832
  simp only [CollatzResearch.WordTrace]
  refine ⟨50293198272426569526233875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67057597696568759368311833 50293198272426569526233875)
  ·
    refine ⟨75439797408639854289350813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50293198272426569526233875 75439797408639854289350813)
    ·
      refine ⟨28289924028239945358506555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75439797408639854289350813 28289924028239945358506555)
      ·
        refine ⟨42434886042359918037759833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28289924028239945358506555 42434886042359918037759833)
        ·
          refine ⟨31826164531769938528319875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42434886042359918037759833 31826164531769938528319875)
          ·
            refine ⟨47739246797654907792479813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31826164531769938528319875 47739246797654907792479813)
            ·
              refine ⟨8951108774560295211089965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47739246797654907792479813 8951108774560295211089965)
              ·
                refine ⟨3356665790460110704158737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8951108774560295211089965 3356665790460110704158737)
                ·
                  refine ⟨2517499342845083028119053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356665790460110704158737 2517499342845083028119053)
                  ·
                    refine ⟨944062253566906135544645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517499342845083028119053 944062253566906135544645)
                    ·
                      rfl

theorem cell22_2757832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_2757832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757832 prefixEnd_2757832 := by exact prefixLift 2757832
  have htrace : WordTrace (prefixWord ++ tailWord_2757832) baseStart_2757832 baseEnd_2757832 := by
    simpa [prefixWord, tailWord_2757832, baseEnd_2757832] using wordTrace_append hprefix tailTrace_2757832
  have hstable : (prefixWord ++ tailWord_2757832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757832).length < 2 ^ (prefixWord ++ tailWord_2757832).sum := by decide
  have hdescent : baseEnd_2757832 < baseStart_2757832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757843 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_2757843 : Nat := 118140960795 + 2757843 * 2 ^ 59
def prefixEnd_2757843 : Nat := 4983230072969 + 3 ^ 40 * 2757843 * 2
def baseEnd_2757843 : Nat := 944066019091705773519611

theorem tailTrace_2757843 : CollatzResearch.WordTrace tailWord_2757843 prefixEnd_2757843 944066019091705773519611 := by
  unfold tailWord_2757843
  simp only [CollatzResearch.WordTrace]
  refine ⟨100586797747813287931118183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67057865165208858620745455 100586797747813287931118183)
  ·
    refine ⟨150880196621719931896677275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100586797747813287931118183 150880196621719931896677275)
    ·
      refine ⟨226320294932579897845015913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150880196621719931896677275 226320294932579897845015913)
      ·
        refine ⟨169740221199434923383761935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226320294932579897845015913 169740221199434923383761935)
        ·
          refine ⟨254610331799152385075642903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169740221199434923383761935 254610331799152385075642903)
          ·
            refine ⟨381915497698728577613464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254610331799152385075642903 381915497698728577613464355)
            ·
              refine ⟨572873246548092866420196533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381915497698728577613464355 572873246548092866420196533)
              ·
                refine ⟨53706866863883706226893425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 572873246548092866420196533 53706866863883706226893425)
                ·
                  refine ⟨40280150147912779670170069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53706866863883706226893425 40280150147912779670170069)
                  ·
                    refine ⟨944066019091705773519611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40280150147912779670170069 944066019091705773519611)
                    ·
                      rfl

theorem cell22_2757843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_2757843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757843 prefixEnd_2757843 := by exact prefixLift 2757843
  have htrace : WordTrace (prefixWord ++ tailWord_2757843) baseStart_2757843 baseEnd_2757843 := by
    simpa [prefixWord, tailWord_2757843, baseEnd_2757843] using wordTrace_append hprefix tailTrace_2757843
  have hstable : (prefixWord ++ tailWord_2757843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757843).length < 2 ^ (prefixWord ++ tailWord_2757843).sum := by decide
  have hdescent : baseEnd_2757843 < baseStart_2757843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757853 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2757853 : Nat := 118140960795 + 2757853 * 2 ^ 59
def prefixEnd_2757853 : Nat := 4983230072969 + 3 ^ 40 * 2757853 * 2
def baseEnd_2757853 : Nat := 944069442296069080769581

theorem tailTrace_2757853 : CollatzResearch.WordTrace tailWord_2757853 prefixEnd_2757853 944069442296069080769581 := by
  unfold tailWord_2757853
  simp only [CollatzResearch.WordTrace]
  refine ⟨100587162477777059638982213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67058108318518039759321475 100587162477777059638982213)
  ·
    refine ⟨18860092964583198682309165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100587162477777059638982213 18860092964583198682309165)
    ·
      refine ⟨7072534861718699505865937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18860092964583198682309165 7072534861718699505865937)
      ·
        refine ⟨5304401146289024629399453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7072534861718699505865937 5304401146289024629399453)
        ·
          refine ⟨1989150429858384236024795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5304401146289024629399453 1989150429858384236024795)
          ·
            refine ⟨2983725644787576354037193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989150429858384236024795 2983725644787576354037193)
            ·
              refine ⟨2237794233590682265527895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983725644787576354037193 2237794233590682265527895)
              ·
                refine ⟨3356691350386023398291843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237794233590682265527895 3356691350386023398291843)
                ·
                  refine ⟨5035037025579035097437765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356691350386023398291843 5035037025579035097437765)
                  ·
                    refine ⟨944069442296069080769581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035037025579035097437765 944069442296069080769581)
                    ·
                      rfl

theorem cell22_2757853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2757853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757853 prefixEnd_2757853 := by exact prefixLift 2757853
  have htrace : WordTrace (prefixWord ++ tailWord_2757853) baseStart_2757853 baseEnd_2757853 := by
    simpa [prefixWord, tailWord_2757853, baseEnd_2757853] using wordTrace_append hprefix tailTrace_2757853
  have hstable : (prefixWord ++ tailWord_2757853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757853).length < 2 ^ (prefixWord ++ tailWord_2757853).sum := by decide
  have hdescent : baseEnd_2757853 < baseStart_2757853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757928 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2757928 : Nat := 118140960795 + 2757928 * 2 ^ 59
def prefixEnd_2757928 : Nat := 4983230072969 + 3 ^ 40 * 2757928 * 2
def baseEnd_2757928 : Nat := 944095116328793885144351

theorem tailTrace_2757928 : CollatzResearch.WordTrace tailWord_2757928 prefixEnd_2757928 944095116328793885144351 := by
  unfold tailWord_2757928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50294948976252673723981219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67059931968336898298641625 50294948976252673723981219)
  ·
    refine ⟨75442423464379010585971829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50294948976252673723981219 75442423464379010585971829)
    ·
      refine ⟨7072727199785532242434859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75442423464379010585971829 7072727199785532242434859)
      ·
        refine ⟨10609090799678298363652289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7072727199785532242434859 10609090799678298363652289)
        ·
          refine ⟨7956818099758723772739217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10609090799678298363652289 7956818099758723772739217)
          ·
            refine ⟨5967613574819042829554413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7956818099758723772739217 5967613574819042829554413)
            ·
              refine ⟨2237855090557141061082905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5967613574819042829554413 2237855090557141061082905)
              ·
                refine ⟨1678391317917855795812179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237855090557141061082905 1678391317917855795812179)
                ·
                  refine ⟨2517586976876783693718269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678391317917855795812179 2517586976876783693718269)
                  ·
                    refine ⟨944095116328793885144351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517586976876783693718269 944095116328793885144351)
                    ·
                      rfl

theorem cell22_2757928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2757928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757928 prefixEnd_2757928 := by exact prefixLift 2757928
  have htrace : WordTrace (prefixWord ++ tailWord_2757928) baseStart_2757928 baseEnd_2757928 := by
    simpa [prefixWord, tailWord_2757928, baseEnd_2757928] using wordTrace_append hprefix tailTrace_2757928
  have hstable : (prefixWord ++ tailWord_2757928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757928).length < 2 ^ (prefixWord ++ tailWord_2757928).sum := by decide
  have hdescent : baseEnd_2757928 < baseStart_2757928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757980 : List Nat := [2, 2, 4, 14]
def baseStart_2757980 : Nat := 118140960795 + 2757980 * 2 ^ 59
def prefixEnd_2757980 : Nat := 4983230072969 + 3 ^ 40 * 2757980 * 2
def baseEnd_2757980 : Nat := 1295079447176245655479

theorem tailTrace_2757980 : CollatzResearch.WordTrace tailWord_2757980 prefixEnd_2757980 1295079447176245655479 := by
  unfold tailWord_2757980
  simp only [CollatzResearch.WordTrace]
  refine ⟨50295897274158480164427697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67061196365544640219236929 50295897274158480164427697)
  ·
    refine ⟨37721922955618860123320773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50295897274158480164427697 37721922955618860123320773)
    ·
      refine ⟨7072860554178536273122645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37721922955618860123320773 7072860554178536273122645)
      ·
        refine ⟨1295079447176245655479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7072860554178536273122645 1295079447176245655479)
        ·
          rfl

theorem cell22_2757980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 14].length) (baseStart_2757980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757980 prefixEnd_2757980 := by exact prefixLift 2757980
  have htrace : WordTrace (prefixWord ++ tailWord_2757980) baseStart_2757980 baseEnd_2757980 := by
    simpa [prefixWord, tailWord_2757980, baseEnd_2757980] using wordTrace_append hprefix tailTrace_2757980
  have hstable : (prefixWord ++ tailWord_2757980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757980).length < 2 ^ (prefixWord ++ tailWord_2757980).sum := by decide
  have hdescent : baseEnd_2757980 < baseStart_2757980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757984 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_2757984 : Nat := 118140960795 + 2757984 * 2 ^ 59
def prefixEnd_2757984 : Nat := 4983230072969 + 3 ^ 40 * 2757984 * 2
def baseEnd_2757984 : Nat := 944114286273228405744179

theorem tailTrace_2757984 : CollatzResearch.WordTrace tailWord_2757984 prefixEnd_2757984 944114286273228405744179 := by
  unfold tailWord_2757984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50295970220151234506000503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67061293626868312674667337 50295970220151234506000503)
  ·
    refine ⟨75443955330226851759000755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50295970220151234506000503 75443955330226851759000755)
    ·
      refine ⟨113165932995340277638501133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75443955330226851759000755 113165932995340277638501133)
      ·
        refine ⟨42437224873252604114437925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113165932995340277638501133 42437224873252604114437925)
        ·
          refine ⟨7956979663734863271457111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42437224873252604114437925 7956979663734863271457111)
          ·
            refine ⟨11935469495602294907185667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956979663734863271457111 11935469495602294907185667)
            ·
              refine ⟨17903204243403442360778501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11935469495602294907185667 17903204243403442360778501)
              ·
                refine ⟨3356850795638145442645969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17903204243403442360778501 3356850795638145442645969)
                ·
                  refine ⟨2517638096728609081984477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356850795638145442645969 2517638096728609081984477)
                  ·
                    refine ⟨944114286273228405744179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517638096728609081984477 944114286273228405744179)
                    ·
                      rfl

theorem cell22_2757984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_2757984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757984 prefixEnd_2757984 := by exact prefixLift 2757984
  have htrace : WordTrace (prefixWord ++ tailWord_2757984) baseStart_2757984 baseEnd_2757984 := by
    simpa [prefixWord, tailWord_2757984, baseEnd_2757984] using wordTrace_append hprefix tailTrace_2757984
  have hstable : (prefixWord ++ tailWord_2757984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757984).length < 2 ^ (prefixWord ++ tailWord_2757984).sum := by decide
  have hdescent : baseEnd_2757984 < baseStart_2757984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2757997 : List Nat := [1, 5, 1, 1, 1, 3, 3, 7]
def baseStart_2757997 : Nat := 118140960795 + 2757997 * 2 ^ 59
def prefixEnd_2757997 : Nat := 4983230072969 + 3 ^ 40 * 2757997 * 2
def baseEnd_2757997 : Nat := 104902081826544522796571

theorem tailTrace_2757997 : CollatzResearch.WordTrace tailWord_2757997 prefixEnd_2757997 104902081826544522796571 := by
  unfold tailWord_2757997
  simp only [CollatzResearch.WordTrace]
  refine ⟨100592414589255372232224245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67061609726170248154816163 100592414589255372232224245)
  ·
    refine ⟨9430538867742691146771023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100592414589255372232224245 9430538867742691146771023)
    ·
      refine ⟨14145808301614036720156535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430538867742691146771023 14145808301614036720156535)
      ·
        refine ⟨21218712452421055080234803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145808301614036720156535 21218712452421055080234803)
        ·
          refine ⟨31828068678631582620352205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21218712452421055080234803 31828068678631582620352205)
          ·
            refine ⟨11935525754486843482632077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31828068678631582620352205 11935525754486843482632077)
            ·
              refine ⟨4475822157932566305987029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11935525754486843482632077 4475822157932566305987029)
              ·
                refine ⟨104902081826544522796571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4475822157932566305987029 104902081826544522796571)
                ·
                  rfl

theorem cell22_2757997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 7].length) (baseStart_2757997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2757997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2757997 prefixEnd_2757997 := by exact prefixLift 2757997
  have htrace : WordTrace (prefixWord ++ tailWord_2757997) baseStart_2757997 baseEnd_2757997 := by
    simpa [prefixWord, tailWord_2757997, baseEnd_2757997] using wordTrace_append hprefix tailTrace_2757997
  have hstable : (prefixWord ++ tailWord_2757997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2757997).length < 2 ^ (prefixWord ++ tailWord_2757997).sum := by decide
  have hdescent : baseEnd_2757997 < baseStart_2757997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2757997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758042 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_2758042 : Nat := 118140960795 + 2758042 * 2 ^ 59
def prefixEnd_2758042 : Nat := 4983230072969 + 3 ^ 40 * 2758042 * 2
def baseEnd_2758042 : Nat := 314711380286178529264667

theorem tailTrace_2758042 : CollatzResearch.WordTrace tailWord_2758042 prefixEnd_2758042 314711380286178529264667 := by
  unfold tailWord_2758042
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148513968523086229403095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67062703916061563278408253 25148513968523086229403095)
  ·
    refine ⟨37722770952784629344104643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148513968523086229403095 37722770952784629344104643)
    ·
      refine ⟨56584156429176944016156965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37722770952784629344104643 56584156429176944016156965)
      ·
        refine ⟨10609529330470677003029431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56584156429176944016156965 10609529330470677003029431)
        ·
          refine ⟨15914293995706015504544147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10609529330470677003029431 15914293995706015504544147)
          ·
            refine ⟨23871440993559023256816221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15914293995706015504544147 23871440993559023256816221)
            ·
              refine ⟨8951790372584633721306083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23871440993559023256816221 8951790372584633721306083)
              ·
                refine ⟨13427685558876950581959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951790372584633721306083 13427685558876950581959125)
                ·
                  refine ⟨314711380286178529264667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13427685558876950581959125 314711380286178529264667)
                  ·
                    rfl

theorem cell22_2758042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_2758042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758042 prefixEnd_2758042 := by exact prefixLift 2758042
  have htrace : WordTrace (prefixWord ++ tailWord_2758042) baseStart_2758042 baseEnd_2758042 := by
    simpa [prefixWord, tailWord_2758042, baseEnd_2758042] using wordTrace_append hprefix tailTrace_2758042
  have hstable : (prefixWord ++ tailWord_2758042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758042).length < 2 ^ (prefixWord ++ tailWord_2758042).sum := by decide
  have hdescent : baseEnd_2758042 < baseStart_2758042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758072 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2758072 : Nat := 118140960795 + 2758072 * 2 ^ 59
def prefixEnd_2758072 : Nat := 4983230072969 + 3 ^ 40 * 2758072 * 2
def baseEnd_2758072 : Nat := 944144410471625509543909

theorem tailTrace_2758072 : CollatzResearch.WordTrace tailWord_2758072 prefixEnd_2758072 944144410471625509543909 := by
  unfold tailWord_2758072
  simp only [CollatzResearch.WordTrace]
  refine ⟨50297575031991830020602235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67063433375989106694136313 50297575031991830020602235)
  ·
    refine ⟨75446362547987745030903353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50297575031991830020602235 75446362547987745030903353)
    ·
      refine ⟨56584771910990808773177515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75446362547987745030903353 56584771910990808773177515)
      ·
        refine ⟨84877157866486213159766273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56584771910990808773177515 84877157866486213159766273)
        ·
          refine ⟨63657868399864659869824705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84877157866486213159766273 63657868399864659869824705)
          ·
            refine ⟨47743401299898494902368529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63657868399864659869824705 47743401299898494902368529)
            ·
              refine ⟨35807550974923871176776397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47743401299898494902368529 35807550974923871176776397)
              ·
                refine ⟨13427831615596451691291149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35807550974923871176776397 13427831615596451691291149)
                ·
                  refine ⟨5035436855848669384234181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13427831615596451691291149 5035436855848669384234181)
                  ·
                    refine ⟨944144410471625509543909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035436855848669384234181 944144410471625509543909)
                    ·
                      rfl

theorem cell22_2758072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2758072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758072 prefixEnd_2758072 := by exact prefixLift 2758072
  have htrace : WordTrace (prefixWord ++ tailWord_2758072) baseStart_2758072 baseEnd_2758072 := by
    simpa [prefixWord, tailWord_2758072, baseEnd_2758072] using wordTrace_append hprefix tailTrace_2758072
  have hstable : (prefixWord ++ tailWord_2758072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758072).length < 2 ^ (prefixWord ++ tailWord_2758072).sum := by decide
  have hdescent : baseEnd_2758072 < baseStart_2758072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758104 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_2758104 : Nat := 118140960795 + 2758104 * 2 ^ 59
def prefixEnd_2758104 : Nat := 4983230072969 + 3 ^ 40 * 2758104 * 2
def baseEnd_2758104 : Nat := 314718454908529364247937

theorem tailTrace_2758104 : CollatzResearch.WordTrace tailWord_2758104 prefixEnd_2758104 314718454908529364247937 := by
  unfold tailWord_2758104
  simp only [CollatzResearch.WordTrace]
  refine ⟨50298158599933864753184683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67064211466578486337579577 50298158599933864753184683)
  ·
    refine ⟨75447237899900797129777025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50298158599933864753184683 75447237899900797129777025)
    ·
      refine ⟨56585428424925597847332769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75447237899900797129777025 56585428424925597847332769)
      ·
        refine ⟨42439071318694198385499577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56585428424925597847332769 42439071318694198385499577)
        ·
          refine ⟨31829303489020648789124683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42439071318694198385499577 31829303489020648789124683)
          ·
            refine ⟨47743955233530973183687025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829303489020648789124683 47743955233530973183687025)
            ·
              refine ⟨35807966425148229887765269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47743955233530973183687025 35807966425148229887765269)
              ·
                refine ⟨1678498426178823275988997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35807966425148229887765269 1678498426178823275988997)
                ·
                  refine ⟨314718454908529364247937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678498426178823275988997 314718454908529364247937)
                  ·
                    rfl

theorem cell22_2758104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_2758104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758104 prefixEnd_2758104 := by exact prefixLift 2758104
  have htrace : WordTrace (prefixWord ++ tailWord_2758104) baseStart_2758104 baseEnd_2758104 := by
    simpa [prefixWord, tailWord_2758104, baseEnd_2758104] using wordTrace_append hprefix tailTrace_2758104
  have hstable : (prefixWord ++ tailWord_2758104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758104).length < 2 ^ (prefixWord ++ tailWord_2758104).sum := by decide
  have hdescent : baseEnd_2758104 < baseStart_2758104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758155 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 4]
def baseStart_2758155 : Nat := 118140960795 + 2758155 * 2 ^ 59
def prefixEnd_2758155 : Nat := 4983230072969 + 3 ^ 40 * 2758155 * 2
def baseEnd_2758155 : Nat := 314724274355946986572885

theorem tailTrace_2758155 : CollatzResearch.WordTrace tailWord_2758155 prefixEnd_2758155 314724274355946986572885 := by
  unfold tailWord_2758155
  simp only [CollatzResearch.WordTrace]
  refine ⟨100598177322682965216475919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67065451548455310144317279 100598177322682965216475919)
  ·
    refine ⟨150897265984024447824713879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100598177322682965216475919 150897265984024447824713879)
    ·
      refine ⟨226345898976036671737070819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150897265984024447824713879 226345898976036671737070819)
      ·
        refine ⟨339518848464055007605606229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226345898976036671737070819 339518848464055007605606229)
        ·
          refine ⟨1989368252719072310189099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 339518848464055007605606229 1989368252719072310189099)
          ·
            refine ⟨2984052379078608465283649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989368252719072310189099 2984052379078608465283649)
            ·
              refine ⟨2238039284308956348962737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984052379078608465283649 2238039284308956348962737)
              ·
                refine ⟨1678529463231717261722053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238039284308956348962737 1678529463231717261722053)
                ·
                  refine ⟨314724274355946986572885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678529463231717261722053 314724274355946986572885)
                  ·
                    rfl

theorem cell22_2758155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 4].length) (baseStart_2758155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758155 prefixEnd_2758155 := by exact prefixLift 2758155
  have htrace : WordTrace (prefixWord ++ tailWord_2758155) baseStart_2758155 baseEnd_2758155 := by
    simpa [prefixWord, tailWord_2758155, baseEnd_2758155] using wordTrace_append hprefix tailTrace_2758155
  have hstable : (prefixWord ++ tailWord_2758155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758155).length < 2 ^ (prefixWord ++ tailWord_2758155).sum := by decide
  have hdescent : baseEnd_2758155 < baseStart_2758155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_2758192 : Nat := 118140960795 + 2758192 * 2 ^ 59
def prefixEnd_2758192 : Nat := 4983230072969 + 3 ^ 40 * 2758192 * 2
def baseEnd_2758192 : Nat := 944185488923985196543541

theorem tailTrace_2758192 : CollatzResearch.WordTrace tailWord_2758192 prefixEnd_2758192 944185488923985196543541 := by
  unfold tailWord_2758192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50299763411774460267786415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67066351215699280357048553 50299763411774460267786415)
  ·
    refine ⟨75449645117661690401679623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50299763411774460267786415 75449645117661690401679623)
    ·
      refine ⟨113174467676492535602519435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75449645117661690401679623 113174467676492535602519435)
      ·
        refine ⟨169761701514738803403779153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113174467676492535602519435 169761701514738803403779153)
        ·
          refine ⟨127321276136054102552834365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169761701514738803403779153 127321276136054102552834365)
          ·
            refine ⟨47745478551020288457312887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127321276136054102552834365 47745478551020288457312887)
            ·
              refine ⟨71618217826530432685969331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47745478551020288457312887 71618217826530432685969331)
              ·
                refine ⟨107427326739795649028953997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71618217826530432685969331 107427326739795649028953997)
                ·
                  refine ⟨40285247527423368385857749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107427326739795649028953997 40285247527423368385857749)
                  ·
                    refine ⟨944185488923985196543541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40285247527423368385857749 944185488923985196543541)
                    ·
                      rfl

theorem cell22_2758192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_2758192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758192 prefixEnd_2758192 := by exact prefixLift 2758192
  have htrace : WordTrace (prefixWord ++ tailWord_2758192) baseStart_2758192 baseEnd_2758192 := by
    simpa [prefixWord, tailWord_2758192, baseEnd_2758192] using wordTrace_append hprefix tailTrace_2758192
  have hstable : (prefixWord ++ tailWord_2758192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758192).length < 2 ^ (prefixWord ++ tailWord_2758192).sum := by decide
  have hdescent : baseEnd_2758192 < baseStart_2758192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758209 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2758209 : Nat := 118140960795 + 2758209 * 2 ^ 59
def prefixEnd_2758209 : Nat := 4983230072969 + 3 ^ 40 * 2758209 * 2
def baseEnd_2758209 : Nat := 944191308371402818868489

theorem tailTrace_2758209 : CollatzResearch.WordTrace tailWord_2758209 prefixEnd_2758209 944191308371402818868489 := by
  unfold tailWord_2758209
  simp only [CollatzResearch.WordTrace]
  refine ⟨100600146864487332438941681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67066764576324888292627787 100600146864487332438941681)
  ·
    refine ⟨75450110148365499329206261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100600146864487332438941681 75450110148365499329206261)
    ·
      refine ⟨7073447826409265562113087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75450110148365499329206261 7073447826409265562113087)
      ·
        refine ⟨10610171739613898343169631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073447826409265562113087 10610171739613898343169631)
        ·
          refine ⟨15915257609420847514754447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610171739613898343169631 15915257609420847514754447)
          ·
            refine ⟨23872886414131271272131671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15915257609420847514754447 23872886414131271272131671)
            ·
              refine ⟨35809329621196906908197507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23872886414131271272131671 35809329621196906908197507)
              ·
                refine ⟨53713994431795360362296261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35809329621196906908197507 53713994431795360362296261)
                ·
                  refine ⟨10071373955961630067930549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53713994431795360362296261 10071373955961630067930549)
                  ·
                    refine ⟨944191308371402818868489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10071373955961630067930549 944191308371402818868489)
                    ·
                      rfl

theorem cell22_2758209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2758209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758209 prefixEnd_2758209 := by exact prefixLift 2758209
  have htrace : WordTrace (prefixWord ++ tailWord_2758209) baseStart_2758209 baseEnd_2758209 := by
    simpa [prefixWord, tailWord_2758209, baseEnd_2758209] using wordTrace_append hprefix tailTrace_2758209
  have hstable : (prefixWord ++ tailWord_2758209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758209).length < 2 ^ (prefixWord ++ tailWord_2758209).sum := by decide
  have hdescent : baseEnd_2758209 < baseStart_2758209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758241 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_2758241 : Nat := 118140960795 + 2758241 * 2 ^ 59
def prefixEnd_2758241 : Nat := 4983230072969 + 3 ^ 40 * 2758241 * 2
def baseEnd_2758241 : Nat := 944202262625365402068391

theorem tailTrace_2758241 : CollatzResearch.WordTrace tailWord_2758241 prefixEnd_2758241 944202262625365402068391 := by
  unfold tailWord_2758241
  simp only [CollatzResearch.WordTrace]
  refine ⟨100601314000371401904106577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67067542666914267936071051 100601314000371401904106577)
  ·
    refine ⟨75450985500278551428079933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100601314000371401904106577 75450985500278551428079933)
    ·
      refine ⟨28294119562604456785529975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75450985500278551428079933 28294119562604456785529975)
      ·
        refine ⟨42441179343906685178294963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28294119562604456785529975 42441179343906685178294963)
        ·
          refine ⟨63661769015860027767442445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42441179343906685178294963 63661769015860027767442445)
          ·
            refine ⟨23873163380947510412790917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63661769015860027767442445 23873163380947510412790917)
            ·
              refine ⟨4476218133927658202398297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23873163380947510412790917 4476218133927658202398297)
              ·
                refine ⟨3357163600445743651798723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476218133927658202398297 3357163600445743651798723)
                ·
                  refine ⟨5035745400668615477698085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357163600445743651798723 5035745400668615477698085)
                  ·
                    refine ⟨944202262625365402068391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035745400668615477698085 944202262625365402068391)
                    ·
                      rfl

theorem cell22_2758241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_2758241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758241 prefixEnd_2758241 := by exact prefixLift 2758241
  have htrace : WordTrace (prefixWord ++ tailWord_2758241) baseStart_2758241 baseEnd_2758241 := by
    simpa [prefixWord, tailWord_2758241, baseEnd_2758241] using wordTrace_append hprefix tailTrace_2758241
  have hstable : (prefixWord ++ tailWord_2758241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758241).length < 2 ^ (prefixWord ++ tailWord_2758241).sum := by decide
  have hdescent : baseEnd_2758241 < baseStart_2758241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758284 : List Nat := [2, 2, 1, 2, 1, 1, 6, 7]
def baseStart_2758284 : Nat := 118140960795 + 2758284 * 2 ^ 59
def prefixEnd_2758284 : Nat := 4983230072969 + 3 ^ 40 * 2758284 * 2
def baseEnd_2758284 : Nat := 104912998044903069249251

theorem tailTrace_2758284 : CollatzResearch.WordTrace tailWord_2758284 prefixEnd_2758284 104912998044903069249251 := by
  unfold tailWord_2758284
  simp only [CollatzResearch.WordTrace]
  refine ⟨50301441169607810123960953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67068588226143746831947937 50301441169607810123960953)
  ·
    refine ⟨37726080877205857592970715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50301441169607810123960953 37726080877205857592970715)
    ·
      refine ⟨56589121315808786389456073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37726080877205857592970715 56589121315808786389456073)
      ·
        refine ⟨42441840986856589792092055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56589121315808786389456073 42441840986856589792092055)
        ·
          refine ⟨63662761480284884688138083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42441840986856589792092055 63662761480284884688138083)
          ·
            refine ⟨95494142220427327032207125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63662761480284884688138083 95494142220427327032207125)
            ·
              refine ⟨4476287916582530954634709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95494142220427327032207125 4476287916582530954634709)
              ·
                refine ⟨104912998044903069249251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4476287916582530954634709 104912998044903069249251)
                ·
                  rfl

theorem cell22_2758284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_2758284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758284 prefixEnd_2758284 := by exact prefixLift 2758284
  have htrace : WordTrace (prefixWord ++ tailWord_2758284) baseStart_2758284 baseEnd_2758284 := by
    simpa [prefixWord, tailWord_2758284, baseEnd_2758284] using wordTrace_append hprefix tailTrace_2758284
  have hstable : (prefixWord ++ tailWord_2758284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758284).length < 2 ^ (prefixWord ++ tailWord_2758284).sum := by decide
  have hdescent : baseEnd_2758284 < baseStart_2758284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758292 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2758292 : Nat := 118140960795 + 2758292 * 2 ^ 59
def prefixEnd_2758292 : Nat := 4983230072969 + 3 ^ 40 * 2758292 * 2
def baseEnd_2758292 : Nat := 944219720967618269043235

theorem tailTrace_2758292 : CollatzResearch.WordTrace tailWord_2758292 prefixEnd_2758292 944219720967618269043235 := by
  unfold tailWord_2758292
  simp only [CollatzResearch.WordTrace]
  refine ⟨50301587061593318807106565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67068782748791091742808753 50301587061593318807106565)
  ·
    refine ⟨9431547574048747276332481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50301587061593318807106565 9431547574048747276332481)
    ·
      refine ⟨7073660680536560457249361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9431547574048747276332481 7073660680536560457249361)
      ·
        refine ⟨5305245510402420342937021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7073660680536560457249361 5305245510402420342937021)
        ·
          refine ⟨1989467066400907628601383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5305245510402420342937021 1989467066400907628601383)
          ·
            refine ⟨2984200599601361442902075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989467066400907628601383 2984200599601361442902075)
            ·
              refine ⟨4476300899402042164353113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984200599601361442902075 4476300899402042164353113)
              ·
                refine ⟨3357225674551531623264835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476300899402042164353113 3357225674551531623264835)
                ·
                  refine ⟨5035838511827297434897253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357225674551531623264835 5035838511827297434897253)
                  ·
                    refine ⟨944219720967618269043235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035838511827297434897253 944219720967618269043235)
                    ·
                      rfl

theorem cell22_2758292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2758292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758292 prefixEnd_2758292 := by exact prefixLift 2758292
  have htrace : WordTrace (prefixWord ++ tailWord_2758292) baseStart_2758292 baseEnd_2758292 := by
    simpa [prefixWord, tailWord_2758292, baseEnd_2758292] using wordTrace_append hprefix tailTrace_2758292
  have hstable : (prefixWord ++ tailWord_2758292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758292).length < 2 ^ (prefixWord ++ tailWord_2758292).sum := by decide
  have hdescent : baseEnd_2758292 < baseStart_2758292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758318 : List Nat := [4, 1, 4, 1, 3, 9]
def baseStart_2758318 : Nat := 118140960795 + 2758318 * 2 ^ 59
def prefixEnd_2758318 : Nat := 4983230072969 + 3 ^ 40 * 2758318 * 2
def baseEnd_2758318 : Nat := 11657143472826702072755

theorem tailTrace_2758318 : CollatzResearch.WordTrace tailWord_2758318 prefixEnd_2758318 11657143472826702072755 := by
  unfold tailWord_2758318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575515302636555506832451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67069414947394962703106405 12575515302636555506832451)
  ·
    refine ⟨18863272953954833260248677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575515302636555506832451 18863272953954833260248677)
    ·
      refine ⟨3536863678866531236296627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18863272953954833260248677 3536863678866531236296627)
      ·
        refine ⟨5305295518299796854444941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536863678866531236296627 5305295518299796854444941)
        ·
          refine ⟨1989485819362423820416853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5305295518299796854444941 1989485819362423820416853)
          ·
            refine ⟨11657143472826702072755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1989485819362423820416853 11657143472826702072755)
            ·
              rfl

theorem cell22_2758318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 9].length) (baseStart_2758318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758318 prefixEnd_2758318 := by exact prefixLift 2758318
  have htrace : WordTrace (prefixWord ++ tailWord_2758318) baseStart_2758318 baseEnd_2758318 := by
    simpa [prefixWord, tailWord_2758318, baseEnd_2758318] using wordTrace_append hprefix tailTrace_2758318
  have hstable : (prefixWord ++ tailWord_2758318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758318).length < 2 ^ (prefixWord ++ tailWord_2758318).sum := by decide
  have hdescent : baseEnd_2758318 < baseStart_2758318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758329 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 7]
def baseStart_2758329 : Nat := 118140960795 + 2758329 * 2 ^ 59
def prefixEnd_2758329 : Nat := 4983230072969 + 3 ^ 40 * 2758329 * 2
def baseEnd_2758329 : Nat := 314744128941254168622707

theorem tailTrace_2758329 : CollatzResearch.WordTrace tailWord_2758329 prefixEnd_2758329 314744128941254168622707 := by
  unfold tailWord_2758329
  simp only [CollatzResearch.WordTrace]
  refine ⟨100604523624052592933310041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67069682416035061955540027 100604523624052592933310041)
  ·
    refine ⟨75453392718039444699982531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100604523624052592933310041 75453392718039444699982531)
    ·
      refine ⟨113180089077059167049973797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75453392718039444699982531 113180089077059167049973797)
      ·
        refine ⟨21221266701948593821870087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113180089077059167049973797 21221266701948593821870087)
        ·
          refine ⟨31831900052922890732805131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221266701948593821870087 31831900052922890732805131)
          ·
            refine ⟨47747850079384336099207697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31831900052922890732805131 47747850079384336099207697)
            ·
              refine ⟨35810887559538252074405773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47747850079384336099207697 35810887559538252074405773)
              ·
                refine ⟨13429082834826844527902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35810887559538252074405773 13429082834826844527902165)
                ·
                  refine ⟨314744128941254168622707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13429082834826844527902165 314744128941254168622707)
                  ·
                    rfl

theorem cell22_2758329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_2758329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758329 prefixEnd_2758329 := by exact prefixLift 2758329
  have htrace : WordTrace (prefixWord ++ tailWord_2758329) baseStart_2758329 baseEnd_2758329 := by
    simpa [prefixWord, tailWord_2758329, baseEnd_2758329] using wordTrace_append hprefix tailTrace_2758329
  have hstable : (prefixWord ++ tailWord_2758329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758329).length < 2 ^ (prefixWord ++ tailWord_2758329).sum := by decide
  have hdescent : baseEnd_2758329 < baseStart_2758329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758421 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2758421 : Nat := 118140960795 + 2758421 * 2 ^ 59
def prefixEnd_2758421 : Nat := 4983230072969 + 3 ^ 40 * 2758421 * 2
def baseEnd_2758421 : Nat := 944263880303904932567839

theorem tailTrace_2758421 : CollatzResearch.WordTrace tailWord_2758421 prefixEnd_2758421 944263880303904932567839 := by
  unfold tailWord_2758421
  simp only [CollatzResearch.WordTrace]
  refine ⟨100607879139719292645659117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67071919426479528430439411 100607879139719292645659117)
  ·
    refine ⟨37727954677394734742122169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100607879139719292645659117 37727954677394734742122169)
    ·
      refine ⟨28295966008046051056591627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37727954677394734742122169 28295966008046051056591627)
      ·
        refine ⟨42443949012069076584887441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28295966008046051056591627 42443949012069076584887441)
        ·
          refine ⟨31832961759051807438665581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42443949012069076584887441 31832961759051807438665581)
          ·
            refine ⟨11937360659644427789499593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31832961759051807438665581 11937360659644427789499593)
            ·
              refine ⟨8953020494733320842124695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11937360659644427789499593 8953020494733320842124695)
              ·
                refine ⟨13429530742099981263187043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8953020494733320842124695 13429530742099981263187043)
                ·
                  refine ⟨20144296113149971894780565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13429530742099981263187043 20144296113149971894780565)
                  ·
                    refine ⟨944263880303904932567839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20144296113149971894780565 944263880303904932567839)
                    ·
                      rfl

theorem cell22_2758421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2758421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758421 prefixEnd_2758421 := by exact prefixLift 2758421
  have htrace : WordTrace (prefixWord ++ tailWord_2758421) baseStart_2758421 baseEnd_2758421 := by
    simpa [prefixWord, tailWord_2758421, baseEnd_2758421] using wordTrace_append hprefix tailTrace_2758421
  have hstable : (prefixWord ++ tailWord_2758421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758421).length < 2 ^ (prefixWord ++ tailWord_2758421).sum := by decide
  have hdescent : baseEnd_2758421 < baseStart_2758421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758423 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 4, 3]
def baseStart_2758423 : Nat := 118140960795 + 2758423 * 2 ^ 59
def prefixEnd_2758423 : Nat := 4983230072969 + 3 ^ 40 * 2758423 * 2
def baseEnd_2758423 : Nat := 944264564944777594017833

theorem tailTrace_2758423 : CollatzResearch.WordTrace tailWord_2758423 prefixEnd_2758423 944264564944777594017833 := by
  unfold tailWord_2758423
  simp only [CollatzResearch.WordTrace]
  refine ⟨100607952085712046987231923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67071968057141364658154615 100607952085712046987231923)
  ·
    refine ⟨150911928128568070480847885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100607952085712046987231923 150911928128568070480847885)
    ·
      refine ⟨56591973048213026430317957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150911928128568070480847885 56591973048213026430317957)
      ·
        refine ⟨10610994946539942455684617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56591973048213026430317957 10610994946539942455684617)
        ·
          refine ⟨7958246209904956841763463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10610994946539942455684617 7958246209904956841763463)
          ·
            refine ⟨11937369314857435262645195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958246209904956841763463 11937369314857435262645195)
            ·
              refine ⟨17906053972286152893967793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11937369314857435262645195 17906053972286152893967793)
              ·
                refine ⟨13429540479214614670475845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17906053972286152893967793 13429540479214614670475845)
                ·
                  refine ⟨2518038839852740250714221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13429540479214614670475845 2518038839852740250714221)
                  ·
                    refine ⟨944264564944777594017833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518038839852740250714221 944264564944777594017833)
                    ·
                      rfl

theorem cell22_2758423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_2758423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758423 prefixEnd_2758423 := by exact prefixLift 2758423
  have htrace : WordTrace (prefixWord ++ tailWord_2758423) baseStart_2758423 baseEnd_2758423 := by
    simpa [prefixWord, tailWord_2758423, baseEnd_2758423] using wordTrace_append hprefix tailTrace_2758423
  have hstable : (prefixWord ++ tailWord_2758423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758423).length < 2 ^ (prefixWord ++ tailWord_2758423).sum := by decide
  have hdescent : baseEnd_2758423 < baseStart_2758423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758436 : List Nat := [2, 3, 1, 3, 2, 1, 10]
def baseStart_2758436 : Nat := 118140960795 + 2758436 * 2 ^ 59
def prefixEnd_2758436 : Nat := 4983230072969 + 3 ^ 40 * 2758436 * 2
def baseEnd_2758436 : Nat := 34972926485572218275659

theorem tailTrace_2758436 : CollatzResearch.WordTrace tailWord_2758436 prefixEnd_2758436 34972926485572218275659 := by
  unfold tailWord_2758436
  simp only [CollatzResearch.WordTrace]
  refine ⟨50304213117332475103727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67072284156443300138303441 50304213117332475103727581)
  ·
    refine ⟨18864079918999678163897843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50304213117332475103727581 18864079918999678163897843)
    ·
      refine ⟨28296119878499517245846765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18864079918999678163897843 28296119878499517245846765)
      ·
        refine ⟨10611044954437318967192537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28296119878499517245846765 10611044954437318967192537)
        ·
          refine ⟨7958283715827989225394403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10611044954437318967192537 7958283715827989225394403)
          ·
            refine ⟨11937425573741983838091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958283715827989225394403 11937425573741983838091605)
            ·
              refine ⟨34972926485572218275659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11937425573741983838091605 34972926485572218275659)
              ·
                rfl

theorem cell22_2758436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 10].length) (baseStart_2758436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758436 prefixEnd_2758436 := by exact prefixLift 2758436
  have htrace : WordTrace (prefixWord ++ tailWord_2758436) baseStart_2758436 baseEnd_2758436 := by
    simpa [prefixWord, tailWord_2758436, baseEnd_2758436] using wordTrace_append hprefix tailTrace_2758436
  have hstable : (prefixWord ++ tailWord_2758436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758436).length < 2 ^ (prefixWord ++ tailWord_2758436).sum := by decide
  have hdescent : baseEnd_2758436 < baseStart_2758436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758453 : List Nat := [1, 3, 3, 1, 4, 1, 2, 7]
def baseStart_2758453 : Nat := 118140960795 + 2758453 * 2 ^ 59
def prefixEnd_2758453 : Nat := 4983230072969 + 3 ^ 40 * 2758453 * 2
def baseEnd_2758453 : Nat := 104919426061985279529749

theorem tailTrace_2758453 : CollatzResearch.WordTrace tailWord_2758453 prefixEnd_2758453 104919426061985279529749 := by
  unfold tailWord_2758453
  simp only [CollatzResearch.WordTrace]
  refine ⟨100609046275603362110824013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67072697517068908073882675 100609046275603362110824013)
  ·
    refine ⟨37728392353351260791559005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100609046275603362110824013 37728392353351260791559005)
    ·
      refine ⟨14148147132506722796834627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37728392353351260791559005 14148147132506722796834627)
      ·
        refine ⟨21222220698760084195251941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14148147132506722796834627 21222220698760084195251941)
        ·
          refine ⟨3979166381017515786609739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21222220698760084195251941 3979166381017515786609739)
          ·
            refine ⟨5968749571526273679914609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979166381017515786609739 5968749571526273679914609)
            ·
              refine ⟨4476562178644705259935957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968749571526273679914609 4476562178644705259935957)
              ·
                refine ⟨104919426061985279529749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4476562178644705259935957 104919426061985279529749)
                ·
                  rfl

theorem cell22_2758453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 7].length) (baseStart_2758453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758453 prefixEnd_2758453 := by exact prefixLift 2758453
  have htrace : WordTrace (prefixWord ++ tailWord_2758453) baseStart_2758453 baseEnd_2758453 := by
    simpa [prefixWord, tailWord_2758453, baseEnd_2758453] using wordTrace_append hprefix tailTrace_2758453
  have hstable : (prefixWord ++ tailWord_2758453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758453).length < 2 ^ (prefixWord ++ tailWord_2758453).sum := by decide
  have hdescent : baseEnd_2758453 < baseStart_2758453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758457 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_2758457 : Nat := 118140960795 + 2758457 * 2 ^ 59
def prefixEnd_2758457 : Nat := 4983230072969 + 3 ^ 40 * 2758457 * 2
def baseEnd_2758457 : Nat := 944276203839612838667729

theorem tailTrace_2758457 : CollatzResearch.WordTrace tailWord_2758457 prefixEnd_2758457 944276203839612838667729 := by
  unfold tailWord_2758457
  simp only [CollatzResearch.WordTrace]
  refine ⟨100609192167588870793969625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67072794778392580529313083 100609192167588870793969625)
  ·
    refine ⟨75456894125691653095477219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100609192167588870793969625 75456894125691653095477219)
    ·
      refine ⟨113185341188537479643215829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75456894125691653095477219 113185341188537479643215829)
      ·
        refine ⟨2652781434106347179137871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 113185341188537479643215829 2652781434106347179137871)
        ·
          refine ⟨3979172151159520768706807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652781434106347179137871 3979172151159520768706807)
          ·
            refine ⟨5968758226739281153060211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979172151159520768706807 5968758226739281153060211)
            ·
              refine ⟨8953137340108921729590317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968758226739281153060211 8953137340108921729590317)
              ·
                refine ⟨3357426502540845648596369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8953137340108921729590317 3357426502540845648596369)
                ·
                  refine ⟨2518069876905634236447277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357426502540845648596369 2518069876905634236447277)
                  ·
                    refine ⟨944276203839612838667729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518069876905634236447277 944276203839612838667729)
                    ·
                      rfl

theorem cell22_2758457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_2758457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758457 prefixEnd_2758457 := by exact prefixLift 2758457
  have htrace : WordTrace (prefixWord ++ tailWord_2758457) baseStart_2758457 baseEnd_2758457 := by
    simpa [prefixWord, tailWord_2758457, baseEnd_2758457] using wordTrace_append hprefix tailTrace_2758457
  have hstable : (prefixWord ++ tailWord_2758457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758457).length < 2 ^ (prefixWord ++ tailWord_2758457).sum := by decide
  have hdescent : baseEnd_2758457 < baseStart_2758457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758470 : List Nat := [6, 1, 1, 2, 1, 1, 2, 8]
def baseStart_2758470 : Nat := 118140960795 + 2758470 * 2 ^ 59
def prefixEnd_2758470 : Nat := 4983230072969 + 3 ^ 40 * 2758470 * 2
def baseEnd_2758470 : Nat := 104920072667253904232521

theorem tailTrace_2758470 : CollatzResearch.WordTrace tailWord_2758470 prefixEnd_2758470 104920072667253904232521 := by
  unfold tailWord_2758470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144052072391930437943527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67073110877694516009461909 3144052072391930437943527)
  ·
    refine ⟨4716078108587895656915291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144052072391930437943527 4716078108587895656915291)
    ·
      refine ⟨7074117162881843485372937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716078108587895656915291 7074117162881843485372937)
      ·
        refine ⟨5305587872161382614029703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074117162881843485372937 5305587872161382614029703)
        ·
          refine ⟨7958381808242073921044555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5305587872161382614029703 7958381808242073921044555)
          ·
            refine ⟨11937572712363110881566833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958381808242073921044555 11937572712363110881566833)
            ·
              refine ⟨8953179534272333161175125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11937572712363110881566833 8953179534272333161175125)
              ·
                refine ⟨104920072667253904232521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8953179534272333161175125 104920072667253904232521)
                ·
                  rfl

theorem cell22_2758470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_2758470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758470 prefixEnd_2758470 := by exact prefixLift 2758470
  have htrace : WordTrace (prefixWord ++ tailWord_2758470) baseStart_2758470 baseEnd_2758470 := by
    simpa [prefixWord, tailWord_2758470, baseEnd_2758470] using wordTrace_append hprefix tailTrace_2758470
  have hstable : (prefixWord ++ tailWord_2758470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758470).length < 2 ^ (prefixWord ++ tailWord_2758470).sum := by decide
  have hdescent : baseEnd_2758470 < baseStart_2758470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758528 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_2758528 : Nat := 118140960795 + 2758528 * 2 ^ 59
def prefixEnd_2758528 : Nat := 4983230072969 + 3 ^ 40 * 2758528 * 2
def baseEnd_2758528 : Nat := 944300508590592320142511

theorem tailTrace_2758528 : CollatzResearch.WordTrace tailWord_2758528 prefixEnd_2758528 944300508590592320142511 := by
  unfold tailWord_2758528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50305890875165824959902119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67074521166887766613202825 50305890875165824959902119)
  ·
    refine ⟨75458836312748737439853179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50305890875165824959902119 75458836312748737439853179)
    ·
      refine ⟨113188254469123106159779769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75458836312748737439853179 113188254469123106159779769)
      ·
        refine ⟨84891190851842329619834827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113188254469123106159779769 84891190851842329619834827)
        ·
          refine ⟨127336786277763494429752241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84891190851842329619834827 127336786277763494429752241)
          ·
            refine ⟨95502589708322620822314181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127336786277763494429752241 95502589708322620822314181)
            ·
              refine ⟨17906735570310491404183909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95502589708322620822314181 17906735570310491404183909)
              ·
                refine ⟨3357512919433217138284483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17906735570310491404183909 3357512919433217138284483)
                ·
                  refine ⟨5036269379149825707426725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357512919433217138284483 5036269379149825707426725)
                  ·
                    refine ⟨944300508590592320142511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036269379149825707426725 944300508590592320142511)
                    ·
                      rfl

theorem cell22_2758528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_2758528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758528 prefixEnd_2758528 := by exact prefixLift 2758528
  have htrace : WordTrace (prefixWord ++ tailWord_2758528) baseStart_2758528 baseEnd_2758528 := by
    simpa [prefixWord, tailWord_2758528, baseEnd_2758528] using wordTrace_append hprefix tailTrace_2758528
  have hstable : (prefixWord ++ tailWord_2758528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758528).length < 2 ^ (prefixWord ++ tailWord_2758528).sum := by decide
  have hdescent : baseEnd_2758528 < baseStart_2758528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758545 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2758545 : Nat := 118140960795 + 2758545 * 2 ^ 59
def prefixEnd_2758545 : Nat := 4983230072969 + 3 ^ 40 * 2758545 * 2
def baseEnd_2758545 : Nat := 944306328038009942467459

theorem tailTrace_2758545 : CollatzResearch.WordTrace tailWord_2758545 prefixEnd_2758545 944306328038009942467459 := by
  unfold tailWord_2758545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100612401791270061823173089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67074934527513374548782059 100612401791270061823173089)
  ·
    refine ⟨75459301343452546367379817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100612401791270061823173089 75459301343452546367379817)
    ·
      refine ⟨56594476007589409775534863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75459301343452546367379817 56594476007589409775534863)
      ·
        refine ⟨84891714011384114663302295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56594476007589409775534863 84891714011384114663302295)
        ·
          refine ⟨127337571017076171994953443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84891714011384114663302295 127337571017076171994953443)
          ·
            refine ⟨191006356525614257992430165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127337571017076171994953443 191006356525614257992430165)
            ·
              refine ⟨2238355740534542085848791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 191006356525614257992430165 2238355740534542085848791)
              ·
                refine ⟨3357533610801813128773187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238355740534542085848791 3357533610801813128773187)
                ·
                  refine ⟨5036300416202719693159781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357533610801813128773187 5036300416202719693159781)
                  ·
                    refine ⟨944306328038009942467459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036300416202719693159781 944306328038009942467459)
                    ·
                      rfl

theorem cell22_2758545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2758545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758545 prefixEnd_2758545 := by exact prefixLift 2758545
  have htrace : WordTrace (prefixWord ++ tailWord_2758545) baseStart_2758545 baseEnd_2758545 := by
    simpa [prefixWord, tailWord_2758545, baseEnd_2758545] using wordTrace_append hprefix tailTrace_2758545
  have hstable : (prefixWord ++ tailWord_2758545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758545).length < 2 ^ (prefixWord ++ tailWord_2758545).sum := by decide
  have hdescent : baseEnd_2758545 < baseStart_2758545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758662 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2758662 : Nat := 118140960795 + 2758662 * 2 ^ 59
def prefixEnd_2758662 : Nat := 4983230072969 + 3 ^ 40 * 2758662 * 2
def baseEnd_2758662 : Nat := 314782126509686879097367

theorem tailTrace_2758662 : CollatzResearch.WordTrace tailWord_2758662 prefixEnd_2758662 314782126509686879097367 := by
  unfold tailWord_2758662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144270910370193462661945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67077779421230793870121493 3144270910370193462661945)
  ·
    refine ⟨2358203182777645096996459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144270910370193462661945 2358203182777645096996459)
    ·
      refine ⟨3537304774166467645494689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358203182777645096996459 3537304774166467645494689)
      ·
        refine ⟨2652978580624850734121017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537304774166467645494689 2652978580624850734121017)
        ·
          refine ⟨1989733935468638050590763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652978580624850734121017 1989733935468638050590763)
          ·
            refine ⟨2984600903202957075886145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989733935468638050590763 2984600903202957075886145)
            ·
              refine ⟨2238450677402217806914609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984600903202957075886145 2238450677402217806914609)
              ·
                refine ⟨1678838008051663355185957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2238450677402217806914609 1678838008051663355185957)
                ·
                  refine ⟨314782126509686879097367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678838008051663355185957 314782126509686879097367)
                  ·
                    rfl

theorem cell22_2758662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2758662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758662 prefixEnd_2758662 := by exact prefixLift 2758662
  have htrace : WordTrace (prefixWord ++ tailWord_2758662) baseStart_2758662 baseEnd_2758662 := by
    simpa [prefixWord, tailWord_2758662, baseEnd_2758662] using wordTrace_append hprefix tailTrace_2758662
  have hstable : (prefixWord ++ tailWord_2758662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758662).length < 2 ^ (prefixWord ++ tailWord_2758662).sum := by decide
  have hdescent : baseEnd_2758662 < baseStart_2758662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758744 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_2758744 : Nat := 118140960795 + 2758744 * 2 ^ 59
def prefixEnd_2758744 : Nat := 4983230072969 + 3 ^ 40 * 2758744 * 2
def baseEnd_2758744 : Nat := 944374449804839756741849

theorem tailTrace_2758744 : CollatzResearch.WordTrace tailWord_2758744 prefixEnd_2758744 944374449804839756741849 := by
  unfold tailWord_2758744
  simp only [CollatzResearch.WordTrace]
  refine ⟨50309829958774559404833643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67079773278366079206444857 50309829958774559404833643)
  ·
    refine ⟨75464744938161839107250465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50309829958774559404833643 75464744938161839107250465)
    ·
      refine ⟨56598558703621379330437849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75464744938161839107250465 56598558703621379330437849)
      ·
        refine ⟨42448919027716034497828387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56598558703621379330437849 42448919027716034497828387)
        ·
          refine ⟨63673378541574051746742581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42448919027716034497828387 63673378541574051746742581)
          ·
            refine ⟨5969379238272567351257117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63673378541574051746742581 5969379238272567351257117)
            ·
              refine ⟨2238517214352212756721419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5969379238272567351257117 2238517214352212756721419)
              ·
                refine ⟨3357775821528319135082129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238517214352212756721419 3357775821528319135082129)
                ·
                  refine ⟨2518331866146239351311597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3357775821528319135082129 2518331866146239351311597)
                  ·
                    refine ⟨944374449804839756741849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518331866146239351311597 944374449804839756741849)
                    ·
                      rfl

theorem cell22_2758744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_2758744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758744 prefixEnd_2758744 := by exact prefixLift 2758744
  have htrace : WordTrace (prefixWord ++ tailWord_2758744) baseStart_2758744 baseEnd_2758744 := by
    simpa [prefixWord, tailWord_2758744, baseEnd_2758744] using wordTrace_append hprefix tailTrace_2758744
  have hstable : (prefixWord ++ tailWord_2758744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758744).length < 2 ^ (prefixWord ++ tailWord_2758744).sum := by decide
  have hdescent : baseEnd_2758744 < baseStart_2758744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758757 : List Nat := [1, 3, 1, 3, 2, 4, 2, 6]
def baseStart_2758757 : Nat := 118140960795 + 2758757 * 2 ^ 59
def prefixEnd_2758757 : Nat := 4983230072969 + 3 ^ 40 * 2758757 * 2
def baseEnd_2758757 : Nat := 104930988885612450685201

theorem tailTrace_2758757 : CollatzResearch.WordTrace tailWord_2758757 prefixEnd_2758757 104930988885612450685201 := by
  unfold tailWord_2758757
  simp only [CollatzResearch.WordTrace]
  refine ⟨100620134066502022029890525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67080089377668014686593683 100620134066502022029890525)
  ·
    refine ⟨37732550274938258261208947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100620134066502022029890525 37732550274938258261208947)
    ·
      refine ⟨56598825412407387391813421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37732550274938258261208947 56598825412407387391813421)
      ·
        refine ⟨21224559529652770271930033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56598825412407387391813421 21224559529652770271930033)
        ·
          refine ⟨15918419647239577703947525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21224559529652770271930033 15918419647239577703947525)
          ·
            refine ⟨2984703683857420819490161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15918419647239577703947525 2984703683857420819490161)
            ·
              refine ⟨2238527762893065614617621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984703683857420819490161 2238527762893065614617621)
              ·
                refine ⟨104930988885612450685201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2238527762893065614617621 104930988885612450685201)
                ·
                  rfl

theorem cell22_2758757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 6].length) (baseStart_2758757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758757 prefixEnd_2758757 := by exact prefixLift 2758757
  have htrace : WordTrace (prefixWord ++ tailWord_2758757) baseStart_2758757 baseEnd_2758757 := by
    simpa [prefixWord, tailWord_2758757, baseEnd_2758757] using wordTrace_append hprefix tailTrace_2758757
  have hstable : (prefixWord ++ tailWord_2758757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758757).length < 2 ^ (prefixWord ++ tailWord_2758757).sum := by decide
  have hdescent : baseEnd_2758757 < baseStart_2758757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758789 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2758789 : Nat := 118140960795 + 2758789 * 2 ^ 59
def prefixEnd_2758789 : Nat := 4983230072969 + 3 ^ 40 * 2758789 * 2
def baseEnd_2758789 : Nat := 944389854224474639366711

theorem tailTrace_2758789 : CollatzResearch.WordTrace tailWord_2758789 prefixEnd_2758789 944389854224474639366711 := by
  unfold tailWord_2758789
  simp only [CollatzResearch.WordTrace]
  refine ⟨100621301202386091495055421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67080867468257394330036947 100621301202386091495055421)
  ·
    refine ⟨37732987950894784310645783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100621301202386091495055421 37732987950894784310645783)
    ·
      refine ⟨56599481926342176465968675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37732987950894784310645783 56599481926342176465968675)
      ·
        refine ⟨84899222889513264698953013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56599481926342176465968675 84899222889513264698953013)
        ·
          refine ⟨7959302145891868565526845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84899222889513264698953013 7959302145891868565526845)
          ·
            refine ⟨2984738304709450712072567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7959302145891868565526845 2984738304709450712072567)
            ·
              refine ⟨4477107457064176068108851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984738304709450712072567 4477107457064176068108851)
              ·
                refine ⟨6715661185596264102163277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477107457064176068108851 6715661185596264102163277)
                ·
                  refine ⟨2518372944598599038311229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6715661185596264102163277 2518372944598599038311229)
                  ·
                    refine ⟨944389854224474639366711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518372944598599038311229 944389854224474639366711)
                    ·
                      rfl

theorem cell22_2758789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2758789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758789 prefixEnd_2758789 := by exact prefixLift 2758789
  have htrace : WordTrace (prefixWord ++ tailWord_2758789) baseStart_2758789 baseEnd_2758789 := by
    simpa [prefixWord, tailWord_2758789, baseEnd_2758789] using wordTrace_append hprefix tailTrace_2758789
  have hstable : (prefixWord ++ tailWord_2758789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758789).length < 2 ^ (prefixWord ++ tailWord_2758789).sum := by decide
  have hdescent : baseEnd_2758789 < baseStart_2758789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758802 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2758802 : Nat := 118140960795 + 2758802 * 2 ^ 59
def prefixEnd_2758802 : Nat := 4983230072969 + 3 ^ 40 * 2758802 * 2
def baseEnd_2758802 : Nat := 314798101463382312930557

theorem tailTrace_2758802 : CollatzResearch.WordTrace tailWord_2758802 prefixEnd_2758802 314798101463382312930557 := by
  unfold tailWord_2758802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25155443837834748678819665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67081183567559329810185773 25155443837834748678819665)
  ·
    refine ⟨18866582878376061509114749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25155443837834748678819665 18866582878376061509114749)
    ·
      refine ⟨7074968579391023065918031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18866582878376061509114749 7074968579391023065918031)
      ·
        refine ⟨10612452869086534598877047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7074968579391023065918031 10612452869086534598877047)
        ·
          refine ⟨15918679303629801898315571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10612452869086534598877047 15918679303629801898315571)
          ·
            refine ⟨23878018955444702847473357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15918679303629801898315571 23878018955444702847473357)
            ·
              refine ⟨8954257108291763567802509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23878018955444702847473357 8954257108291763567802509)
              ·
                refine ⟨3357846415609411337925941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8954257108291763567802509 3357846415609411337925941)
                ·
                  refine ⟨314798101463382312930557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357846415609411337925941 314798101463382312930557)
                  ·
                    rfl

theorem cell22_2758802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2758802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758802 prefixEnd_2758802 := by exact prefixLift 2758802
  have htrace : WordTrace (prefixWord ++ tailWord_2758802) baseStart_2758802 baseEnd_2758802 := by
    simpa [prefixWord, tailWord_2758802, baseEnd_2758802] using wordTrace_append hprefix tailTrace_2758802
  have hstable : (prefixWord ++ tailWord_2758802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758802).length < 2 ^ (prefixWord ++ tailWord_2758802).sum := by decide
  have hdescent : baseEnd_2758802 < baseStart_2758802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758845 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2758845 : Nat := 118140960795 + 2758845 * 2 ^ 59
def prefixEnd_2758845 : Nat := 4983230072969 + 3 ^ 40 * 2758845 * 2
def baseEnd_2758845 : Nat := 944409024168909159966539

theorem tailTrace_2758845 : CollatzResearch.WordTrace tailWord_2758845 prefixEnd_2758845 944409024168909159966539 := by
  unfold tailWord_2758845
  simp only [CollatzResearch.WordTrace]
  refine ⟨100623343690183213059093989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67082229126788808706062659 100623343690183213059093989)
  ·
    refine ⟨18866876941909352448580123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100623343690183213059093989 18866876941909352448580123)
    ·
      refine ⟨28300315412864028672870185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18866876941909352448580123 28300315412864028672870185)
      ·
        refine ⟨21225236559648021504652639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28300315412864028672870185 21225236559648021504652639)
        ·
          refine ⟨31837854839472032256978959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21225236559648021504652639 31837854839472032256978959)
          ·
            refine ⟨47756782259208048385468439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31837854839472032256978959 47756782259208048385468439)
            ·
              refine ⟨71635173388812072578202659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47756782259208048385468439 71635173388812072578202659)
              ·
                refine ⟨107452760083218108867303989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71635173388812072578202659 107452760083218108867303989)
                ·
                  refine ⟨10073696257801697706309749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107452760083218108867303989 10073696257801697706309749)
                  ·
                    refine ⟨944409024168909159966539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10073696257801697706309749 944409024168909159966539)
                    ·
                      rfl

theorem cell22_2758845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2758845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758845 prefixEnd_2758845 := by exact prefixLift 2758845
  have htrace : WordTrace (prefixWord ++ tailWord_2758845) baseStart_2758845 baseEnd_2758845 := by
    simpa [prefixWord, tailWord_2758845, baseEnd_2758845] using wordTrace_append hprefix tailTrace_2758845
  have hstable : (prefixWord ++ tailWord_2758845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758845).length < 2 ^ (prefixWord ++ tailWord_2758845).sum := by decide
  have hdescent : baseEnd_2758845 < baseStart_2758845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758862 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2758862 : Nat := 118140960795 + 2758862 * 2 ^ 59
def prefixEnd_2758862 : Nat := 4983230072969 + 3 ^ 40 * 2758862 * 2
def baseEnd_2758862 : Nat := 944414843616326782291487

theorem tailTrace_2758862 : CollatzResearch.WordTrace tailWord_2758862 prefixEnd_2758862 944414843616326782291487 := by
  unfold tailWord_2758862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577995466390203120307855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67082642487414416641641893 12577995466390203120307855)
  ·
    refine ⟨18866993199585304680461783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12577995466390203120307855 18866993199585304680461783)
    ·
      refine ⟨28300489799377957020692675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18866993199585304680461783 28300489799377957020692675)
      ·
        refine ⟨42450734699066935531039013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28300489799377957020692675 42450734699066935531039013)
        ·
          refine ⟨7959512756075050412069815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42450734699066935531039013 7959512756075050412069815)
          ·
            refine ⟨11939269134112575618104723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959512756075050412069815 11939269134112575618104723)
            ·
              refine ⟨17908903701168863427157085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11939269134112575618104723 17908903701168863427157085)
              ·
                refine ⟨6715838887938323785183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17908903701168863427157085 6715838887938323785183907)
                ·
                  refine ⟨10073758331907485677775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715838887938323785183907 10073758331907485677775861)
                  ·
                    refine ⟨944414843616326782291487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10073758331907485677775861 944414843616326782291487)
                    ·
                      rfl

theorem cell22_2758862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2758862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758862 prefixEnd_2758862 := by exact prefixLift 2758862
  have htrace : WordTrace (prefixWord ++ tailWord_2758862) baseStart_2758862 baseEnd_2758862 := by
    simpa [prefixWord, tailWord_2758862, baseEnd_2758862] using wordTrace_append hprefix tailTrace_2758862
  have hstable : (prefixWord ++ tailWord_2758862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758862).length < 2 ^ (prefixWord ++ tailWord_2758862).sum := by decide
  have hdescent : baseEnd_2758862 < baseStart_2758862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758883 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 1, 4]
def baseStart_2758883 : Nat := 118140960795 + 2758883 * 2 ^ 59
def prefixEnd_2758883 : Nat := 4983230072969 + 3 ^ 40 * 2758883 * 2
def baseEnd_2758883 : Nat := 944422032345489727516423

theorem tailTrace_2758883 : CollatzResearch.WordTrace tailWord_2758883 prefixEnd_2758883 944422032345489727516423 := by
  unfold tailWord_2758883
  simp only [CollatzResearch.WordTrace]
  refine ⟨100624729664045545548977303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67083153109363697032651535 100624729664045545548977303)
  ·
    refine ⟨150937094496068318323465955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100624729664045545548977303 150937094496068318323465955)
    ·
      refine ⟨226405641744102477485198933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150937094496068318323465955 226405641744102477485198933)
      ·
        refine ⟨2653191114188700908029675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 226405641744102477485198933 2653191114188700908029675)
        ·
          refine ⟨3979786671283051362044513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653191114188700908029675 3979786671283051362044513)
          ·
            refine ⟨2984840003462288521533385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979786671283051362044513 2984840003462288521533385)
            ·
              refine ⟨2238630002596716391150039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984840003462288521533385 2238630002596716391150039)
              ·
                refine ⟨3357945003895074586725059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238630002596716391150039 3357945003895074586725059)
                ·
                  refine ⟨5036917505842611880087589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357945003895074586725059 5036917505842611880087589)
                  ·
                    refine ⟨944422032345489727516423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036917505842611880087589 944422032345489727516423)
                    ·
                      rfl

theorem cell22_2758883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 4].length) (baseStart_2758883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758883 prefixEnd_2758883 := by exact prefixLift 2758883
  have htrace : WordTrace (prefixWord ++ tailWord_2758883) baseStart_2758883 baseEnd_2758883 := by
    simpa [prefixWord, tailWord_2758883, baseEnd_2758883] using wordTrace_append hprefix tailTrace_2758883
  have hstable : (prefixWord ++ tailWord_2758883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758883).length < 2 ^ (prefixWord ++ tailWord_2758883).sum := by decide
  have hdescent : baseEnd_2758883 < baseStart_2758883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758905 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2758905 : Nat := 118140960795 + 2758905 * 2 ^ 59
def prefixEnd_2758905 : Nat := 4983230072969 + 3 ^ 40 * 2758905 * 2
def baseEnd_2758905 : Nat := 944429563395089003466355

theorem tailTrace_2758905 : CollatzResearch.WordTrace tailWord_2758905 prefixEnd_2758905 944429563395089003466355 := by
  unfold tailWord_2758905
  simp only [CollatzResearch.WordTrace]
  refine ⟨100625532069965843306278169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67083688046643895537518779 100625532069965843306278169)
  ·
    refine ⟨75469149052474382479708627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100625532069965843306278169 75469149052474382479708627)
    ·
      refine ⟨113203723578711573719562941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75469149052474382479708627 113203723578711573719562941)
      ·
        refine ⟨42451396342016840144836103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113203723578711573719562941 42451396342016840144836103)
        ·
          refine ⟨63677094513025260217254155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42451396342016840144836103 63677094513025260217254155)
          ·
            refine ⟨95515641769537890325881233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63677094513025260217254155 95515641769537890325881233)
            ·
              refine ⟨71636731327153417744410925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95515641769537890325881233 71636731327153417744410925)
              ·
                refine ⟨26863774247682531654154097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71636731327153417744410925 26863774247682531654154097)
                ·
                  refine ⟨20147830685761898740615573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26863774247682531654154097 20147830685761898740615573)
                  ·
                    refine ⟨944429563395089003466355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20147830685761898740615573 944429563395089003466355)
                    ·
                      rfl

theorem cell22_2758905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2758905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758905 prefixEnd_2758905 := by exact prefixLift 2758905
  have htrace : WordTrace (prefixWord ++ tailWord_2758905) baseStart_2758905 baseEnd_2758905 := by
    simpa [prefixWord, tailWord_2758905, baseEnd_2758905] using wordTrace_append hprefix tailTrace_2758905
  have hstable : (prefixWord ++ tailWord_2758905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758905).length < 2 ^ (prefixWord ++ tailWord_2758905).sum := by decide
  have hdescent : baseEnd_2758905 < baseStart_2758905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758984 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_2758984 : Nat := 118140960795 + 2758984 * 2 ^ 59
def prefixEnd_2758984 : Nat := 4983230072969 + 3 ^ 40 * 2758984 * 2
def baseEnd_2758984 : Nat := 944456606709559130741113

theorem tailTrace_2758984 : CollatzResearch.WordTrace tailWord_2758984 prefixEnd_2758984 944456606709559130741113 := by
  unfold tailWord_2758984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314206718339819899202003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67085608957786426532269337 50314206718339819899202003)
  ·
    refine ⟨75471310077509729848803005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50314206718339819899202003 75471310077509729848803005)
    ·
      refine ⟨28301741279066148693301127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75471310077509729848803005 28301741279066148693301127)
      ·
        refine ⟨42452611918599223039951691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28301741279066148693301127 42452611918599223039951691)
        ·
          refine ⟨63678917877898834559927537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42452611918599223039951691 63678917877898834559927537)
          ·
            refine ⟨47759188408424125919945653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63678917877898834559927537 47759188408424125919945653)
            ·
              refine ⟨4477423913289761804994905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47759188408424125919945653 4477423913289761804994905)
              ·
                refine ⟨3358067934967321353746179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477423913289761804994905 3358067934967321353746179)
                ·
                  refine ⟨5037101902450982030619269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358067934967321353746179 5037101902450982030619269)
                  ·
                    refine ⟨944456606709559130741113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037101902450982030619269 944456606709559130741113)
                    ·
                      rfl

theorem cell22_2758984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_2758984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758984 prefixEnd_2758984 := by exact prefixLift 2758984
  have htrace : WordTrace (prefixWord ++ tailWord_2758984) baseStart_2758984 baseEnd_2758984 := by
    simpa [prefixWord, tailWord_2758984, baseEnd_2758984] using wordTrace_append hprefix tailTrace_2758984
  have hstable : (prefixWord ++ tailWord_2758984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758984).length < 2 ^ (prefixWord ++ tailWord_2758984).sum := by decide
  have hdescent : baseEnd_2758984 < baseStart_2758984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2758999 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 4]
def baseStart_2758999 : Nat := 118140960795 + 2758999 * 2 ^ 59
def prefixEnd_2758999 : Nat := 4983230072969 + 3 ^ 40 * 2758999 * 2
def baseEnd_2758999 : Nat := 314820580505368030538689

theorem tailTrace_2758999 : CollatzResearch.WordTrace tailWord_2758999 prefixEnd_2758999 314820580505368030538689 := by
  unfold tailWord_2758999
  simp only [CollatzResearch.WordTrace]
  refine ⟨100628960531625297360200051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67085973687750198240133367 100628960531625297360200051)
  ·
    refine ⟨150943440797437946040300077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100628960531625297360200051 150943440797437946040300077)
    ·
      refine ⟨56603790299039229765112529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150943440797437946040300077 56603790299039229765112529)
      ·
        refine ⟨42452842724279422323834397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56603790299039229765112529 42452842724279422323834397)
        ·
          refine ⟨15919816021604783371437899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42452842724279422323834397 15919816021604783371437899)
          ·
            refine ⟨23879724032407175057156849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15919816021604783371437899 23879724032407175057156849)
            ·
              refine ⟨17909793024305381292867637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23879724032407175057156849 17909793024305381292867637)
              ·
                refine ⟨1679043096028629496206341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17909793024305381292867637 1679043096028629496206341)
                ·
                  refine ⟨314820580505368030538689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679043096028629496206341 314820580505368030538689)
                  ·
                    rfl

theorem cell22_2758999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 4].length) (baseStart_2758999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2758999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2758999 prefixEnd_2758999 := by exact prefixLift 2758999
  have htrace : WordTrace (prefixWord ++ tailWord_2758999) baseStart_2758999 baseEnd_2758999 := by
    simpa [prefixWord, tailWord_2758999, baseEnd_2758999] using wordTrace_append hprefix tailTrace_2758999
  have hstable : (prefixWord ++ tailWord_2758999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2758999).length < 2 ^ (prefixWord ++ tailWord_2758999).sum := by decide
  have hdescent : baseEnd_2758999 < baseStart_2758999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2758999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759016 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_2759016 : Nat := 118140960795 + 2759016 * 2 ^ 59
def prefixEnd_2759016 : Nat := 4983230072969 + 3 ^ 40 * 2759016 * 2
def baseEnd_2759016 : Nat := 314822520321173904647005

theorem tailTrace_2759016 : CollatzResearch.WordTrace tailWord_2759016 prefixEnd_2759016 314822520321173904647005 := by
  unfold tailWord_2759016
  simp only [CollatzResearch.WordTrace]
  refine ⟨50314790286281854631784451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67086387048375806175712601 50314790286281854631784451)
  ·
    refine ⟨75472185429422781947676677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50314790286281854631784451 75472185429422781947676677)
    ·
      refine ⟨14151034768016771615189377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75472185429422781947676677 14151034768016771615189377)
      ·
        refine ⟨10613276076012578711392033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14151034768016771615189377 10613276076012578711392033)
        ·
          refine ⟨7959957057009434033544025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10613276076012578711392033 7959957057009434033544025)
          ·
            refine ⟨5969967792757075525158019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7959957057009434033544025 5969967792757075525158019)
            ·
              refine ⟨8954951689135613287737029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5969967792757075525158019 8954951689135613287737029)
              ·
                refine ⟨1679053441712927491450693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8954951689135613287737029 1679053441712927491450693)
                ·
                  refine ⟨314822520321173904647005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679053441712927491450693 314822520321173904647005)
                  ·
                    rfl

theorem cell22_2759016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_2759016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759016 prefixEnd_2759016 := by exact prefixLift 2759016
  have htrace : WordTrace (prefixWord ++ tailWord_2759016) baseStart_2759016 baseEnd_2759016 := by
    simpa [prefixWord, tailWord_2759016, baseEnd_2759016] using wordTrace_append hprefix tailTrace_2759016
  have hstable : (prefixWord ++ tailWord_2759016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759016).length < 2 ^ (prefixWord ++ tailWord_2759016).sum := by decide
  have hdescent : baseEnd_2759016 < baseStart_2759016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759044 : List Nat := [2, 3, 2, 1, 1, 2, 5, 6]
def baseStart_2759044 : Nat := 118140960795 + 2759044 * 2 ^ 59
def prefixEnd_2759044 : Nat := 4983230072969 + 3 ^ 40 * 2759044 * 2
def baseEnd_2759044 : Nat := 104941905103970997137881

theorem tailTrace_2759044 : CollatzResearch.WordTrace tailWord_2759044 prefixEnd_2759044 104941905103970997137881 := by
  unfold tailWord_2759044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50315300908231135022794093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67087067877641513363725457 50315300908231135022794093)
  ·
    refine ⟨18868237840586675633547785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50315300908231135022794093 18868237840586675633547785)
    ·
      refine ⟨14151178380440006725160839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18868237840586675633547785 14151178380440006725160839)
      ·
        refine ⟨21226767570660010087741259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151178380440006725160839 21226767570660010087741259)
        ·
          refine ⟨31840151355990015131611889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21226767570660010087741259 31840151355990015131611889)
          ·
            refine ⟨23880113516992511348708917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31840151355990015131611889 23880113516992511348708917)
            ·
              refine ⟨2238760642218047938941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23880113516992511348708917 2238760642218047938941461)
              ·
                refine ⟨104941905103970997137881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2238760642218047938941461 104941905103970997137881)
                ·
                  rfl

theorem cell22_2759044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_2759044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759044 prefixEnd_2759044 := by exact prefixLift 2759044
  have htrace : WordTrace (prefixWord ++ tailWord_2759044) baseStart_2759044 baseEnd_2759044 := by
    simpa [prefixWord, tailWord_2759044, baseEnd_2759044] using wordTrace_append hprefix tailTrace_2759044
  have hstable : (prefixWord ++ tailWord_2759044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759044).length < 2 ^ (prefixWord ++ tailWord_2759044).sum := by decide
  have hdescent : baseEnd_2759044 < baseStart_2759044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759082 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2759082 : Nat := 118140960795 + 2759082 * 2 ^ 59
def prefixEnd_2759082 : Nat := 4983230072969 + 3 ^ 40 * 2759082 * 2
def baseEnd_2759082 : Nat := 944490154112319541790813

theorem tailTrace_2759082 : CollatzResearch.WordTrace tailWord_2759082 prefixEnd_2759082 944490154112319541790813 := by
  unfold tailWord_2759082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157996947581150633867875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67087991860216401690314333 25157996947581150633867875)
  ·
    refine ⟨37736995421371725950801813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157996947581150633867875 37736995421371725950801813)
    ·
      refine ⟨1768921660376799653943835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37736995421371725950801813 1768921660376799653943835)
      ·
        refine ⟨2653382490565199480915753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768921660376799653943835 2653382490565199480915753)
        ·
          refine ⟨1990036867923899610686815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2653382490565199480915753 1990036867923899610686815)
          ·
            refine ⟨2985055301885849416030223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990036867923899610686815 2985055301885849416030223)
            ·
              refine ⟨4477582952828774124045335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985055301885849416030223 4477582952828774124045335)
              ·
                refine ⟨6716374429243161186068003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477582952828774124045335 6716374429243161186068003)
                ·
                  refine ⟨10074561643864741779102005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716374429243161186068003 10074561643864741779102005)
                  ·
                    refine ⟨944490154112319541790813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10074561643864741779102005 944490154112319541790813)
                    ·
                      rfl

theorem cell22_2759082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2759082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759082 prefixEnd_2759082 := by exact prefixLift 2759082
  have htrace : WordTrace (prefixWord ++ tailWord_2759082) baseStart_2759082 baseEnd_2759082 := by
    simpa [prefixWord, tailWord_2759082, baseEnd_2759082] using wordTrace_append hprefix tailTrace_2759082
  have hstable : (prefixWord ++ tailWord_2759082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759082).length < 2 ^ (prefixWord ++ tailWord_2759082).sum := by decide
  have hdescent : baseEnd_2759082 < baseStart_2759082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759196 : List Nat := [2, 2, 3, 1, 2, 4, 1, 7]
def baseStart_2759196 : Nat := 118140960795 + 2759196 * 2 ^ 59
def prefixEnd_2759196 : Nat := 4983230072969 + 3 ^ 40 * 2759196 * 2
def baseEnd_2759196 : Nat := 104947686515784582715607

theorem tailTrace_2759196 : CollatzResearch.WordTrace tailWord_2759196 prefixEnd_2759196 104947686515784582715607 := by
  unfold tailWord_2759196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50318072855955800002560721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67090763807941066670080961 50318072855955800002560721)
  ·
    refine ⟨37738554641966850001920541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50318072855955800002560721 37738554641966850001920541)
    ·
      refine ⟨14151957990737568750720203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37738554641966850001920541 14151957990737568750720203)
      ·
        refine ⟨21227936986106353126080305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151957990737568750720203 21227936986106353126080305)
        ·
          refine ⟨15920952739579764844560229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21227936986106353126080305 15920952739579764844560229)
          ·
            refine ⟨2985178638671205908355043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15920952739579764844560229 2985178638671205908355043)
            ·
              refine ⟨4477767958006808862532565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985178638671205908355043 4477767958006808862532565)
              ·
                refine ⟨104947686515784582715607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477767958006808862532565 104947686515784582715607)
                ·
                  rfl

theorem cell22_2759196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_2759196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759196 prefixEnd_2759196 := by exact prefixLift 2759196
  have htrace : WordTrace (prefixWord ++ tailWord_2759196) baseStart_2759196 baseEnd_2759196 := by
    simpa [prefixWord, tailWord_2759196, baseEnd_2759196] using wordTrace_append hprefix tailTrace_2759196
  have hstable : (prefixWord ++ tailWord_2759196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759196).length < 2 ^ (prefixWord ++ tailWord_2759196).sum := by decide
  have hdescent : baseEnd_2759196 < baseStart_2759196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759224 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_2759224 : Nat := 118140960795 + 2759224 * 2 ^ 59
def prefixEnd_2759224 : Nat := 4983230072969 + 3 ^ 40 * 2759224 * 2
def baseEnd_2759224 : Nat := 314846254538092834913459

theorem tailTrace_2759224 : CollatzResearch.WordTrace tailWord_2759224 prefixEnd_2759224 314846254538092834913459 := by
  unfold tailWord_2759224
  simp only [CollatzResearch.WordTrace]
  refine ⟨50318583477905080393570363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67091444637206773858093817 50318583477905080393570363)
  ·
    refine ⟨75477875216857620590355545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50318583477905080393570363 75477875216857620590355545)
    ·
      refine ⟨56608406412643215442766659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75477875216857620590355545 56608406412643215442766659)
      ·
        refine ⟨84912609618964823164149989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56608406412643215442766659 84912609618964823164149989)
        ·
          refine ⟨15921114303555904343278123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84912609618964823164149989 15921114303555904343278123)
          ·
            refine ⟨23881671455333856514917185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921114303555904343278123 23881671455333856514917185)
            ·
              refine ⟨17911253591500392386187889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23881671455333856514917185 17911253591500392386187889)
              ·
                refine ⟨13433440193625294289640917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17911253591500392386187889 13433440193625294289640917)
                ·
                  refine ⟨314846254538092834913459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13433440193625294289640917 314846254538092834913459)
                  ·
                    rfl

theorem cell22_2759224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_2759224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759224 prefixEnd_2759224 := by exact prefixLift 2759224
  have htrace : WordTrace (prefixWord ++ tailWord_2759224) baseStart_2759224 baseEnd_2759224 := by
    simpa [prefixWord, tailWord_2759224, baseEnd_2759224] using wordTrace_append hprefix tailTrace_2759224
  have hstable : (prefixWord ++ tailWord_2759224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759224).length < 2 ^ (prefixWord ++ tailWord_2759224).sum := by decide
  have hdescent : baseEnd_2759224 < baseStart_2759224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759245 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2759245 : Nat := 118140960795 + 2759245 * 2 ^ 59
def prefixEnd_2759245 : Nat := 4983230072969 + 3 ^ 40 * 2759245 * 2
def baseEnd_2759245 : Nat := 944545952343441449965313

theorem tailTrace_2759245 : CollatzResearch.WordTrace tailWord_2759245 prefixEnd_2759245 944545952343441449965313 := by
  unfold tailWord_2759245
  simp only [CollatzResearch.WordTrace]
  refine ⟨100637932888734081373655189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67091955259156054249103459 100637932888734081373655189)
  ·
    refine ⟨4717403104159410064390087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100637932888734081373655189 4717403104159410064390087)
    ·
      refine ⟨7076104656239115096585131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717403104159410064390087 7076104656239115096585131)
      ·
        refine ⟨10614156984358672644877697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7076104656239115096585131 10614156984358672644877697)
        ·
          refine ⟨7960617738269004483658273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10614156984358672644877697 7960617738269004483658273)
          ·
            refine ⟨5970463303701753362743705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7960617738269004483658273 5970463303701753362743705)
            ·
              refine ⟨4477847477776315022057779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970463303701753362743705 4477847477776315022057779)
              ·
                refine ⟨6716771216664472533086669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477847477776315022057779 6716771216664472533086669)
                ·
                  refine ⟨2518789206249177199907501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6716771216664472533086669 2518789206249177199907501)
                  ·
                    refine ⟨944545952343441449965313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518789206249177199907501 944545952343441449965313)
                    ·
                      rfl

theorem cell22_2759245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2759245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759245 prefixEnd_2759245 := by exact prefixLift 2759245
  have htrace : WordTrace (prefixWord ++ tailWord_2759245) baseStart_2759245 baseEnd_2759245 := by
    simpa [prefixWord, tailWord_2759245, baseEnd_2759245] using wordTrace_append hprefix tailTrace_2759245
  have hstable : (prefixWord ++ tailWord_2759245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759245).length < 2 ^ (prefixWord ++ tailWord_2759245).sum := by decide
  have hdescent : baseEnd_2759245 < baseStart_2759245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759322 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_2759322 : Nat := 118140960795 + 2759322 * 2 ^ 59
def prefixEnd_2759322 : Nat := 4983230072969 + 3 ^ 40 * 2759322 * 2
def baseEnd_2759322 : Nat := 944572311017038915790077

theorem tailTrace_2759322 : CollatzResearch.WordTrace tailWord_2759322 prefixEnd_2759322 944572311017038915790077 := by
  unfold tailWord_2759322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25160185327363780881052055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67093827539636749016138813 25160185327363780881052055)
  ·
    refine ⟨37740277991045671321578083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25160185327363780881052055 37740277991045671321578083)
    ·
      refine ⟨56610416986568506982367125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37740277991045671321578083 56610416986568506982367125)
      ·
        refine ⟨2653613296245398764798459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56610416986568506982367125 2653613296245398764798459)
        ·
          refine ⟨3980419944368098147197689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653613296245398764798459 3980419944368098147197689)
          ·
            refine ⟨2985314958276073610398267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3980419944368098147197689 2985314958276073610398267)
            ·
              refine ⟨4477972437414110415597401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985314958276073610398267 4477972437414110415597401)
              ·
                refine ⟨3358479328060582811698051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477972437414110415597401 3358479328060582811698051)
                ·
                  refine ⟨5037718992090874217547077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358479328060582811698051 5037718992090874217547077)
                  ·
                    refine ⟨944572311017038915790077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037718992090874217547077 944572311017038915790077)
                    ·
                      rfl

theorem cell22_2759322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_2759322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759322 prefixEnd_2759322 := by exact prefixLift 2759322
  have htrace : WordTrace (prefixWord ++ tailWord_2759322) baseStart_2759322 baseEnd_2759322 := by
    simpa [prefixWord, tailWord_2759322, baseEnd_2759322] using wordTrace_append hprefix tailTrace_2759322
  have hstable : (prefixWord ++ tailWord_2759322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759322).length < 2 ^ (prefixWord ++ tailWord_2759322).sum := by decide
  have hdescent : baseEnd_2759322 < baseStart_2759322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759335 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2759335 : Nat := 118140960795 + 2759335 * 2 ^ 59
def prefixEnd_2759335 : Nat := 4983230072969 + 3 ^ 40 * 2759335 * 2
def baseEnd_2759335 : Nat := 944576761182711215215037

theorem tailTrace_2759335 : CollatzResearch.WordTrace tailWord_2759335 prefixEnd_2759335 944576761182711215215037 := by
  unfold tailWord_2759335
  simp only [CollatzResearch.WordTrace]
  refine ⟨100641215458408026744431459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67094143638938684496287639 100641215458408026744431459)
  ·
    refine ⟨150961823187612040116647189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100641215458408026744431459 150961823187612040116647189)
    ·
      refine ⟨7076335461919314380467837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150961823187612040116647189 7076335461919314380467837)
      ·
        refine ⟨2653625798219742892675439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7076335461919314380467837 2653625798219742892675439)
        ·
          refine ⟨3980438697329614339013159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653625798219742892675439 3980438697329614339013159)
          ·
            refine ⟨5970658045994421508519739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980438697329614339013159 5970658045994421508519739)
            ·
              refine ⟨8955987068991632262779609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970658045994421508519739 8955987068991632262779609)
              ·
                refine ⟨6716990301743724197084707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8955987068991632262779609 6716990301743724197084707)
                ·
                  refine ⟨10075485452615586295627061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716990301743724197084707 10075485452615586295627061)
                  ·
                    refine ⟨944576761182711215215037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10075485452615586295627061 944576761182711215215037)
                    ·
                      rfl

theorem cell22_2759335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2759335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759335 prefixEnd_2759335 := by exact prefixLift 2759335
  have htrace : WordTrace (prefixWord ++ tailWord_2759335) baseStart_2759335 baseEnd_2759335 := by
    simpa [prefixWord, tailWord_2759335, baseEnd_2759335] using wordTrace_append hprefix tailTrace_2759335
  have hstable : (prefixWord ++ tailWord_2759335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759335).length < 2 ^ (prefixWord ++ tailWord_2759335).sum := by decide
  have hdescent : baseEnd_2759335 < baseStart_2759335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759397 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_2759397 : Nat := 118140960795 + 2759397 * 2 ^ 59
def prefixEnd_2759397 : Nat := 4983230072969 + 3 ^ 40 * 2759397 * 2
def baseEnd_2759397 : Nat := 944597985049763720164847

theorem tailTrace_2759397 : CollatzResearch.WordTrace tailWord_2759397 prefixEnd_2759397 944597985049763720164847 := by
  unfold tailWord_2759397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100643476784183411333188445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67095651189455607555458963 100643476784183411333188445)
  ·
    refine ⟨37741303794068779249945667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100643476784183411333188445 37741303794068779249945667)
    ·
      refine ⟨56611955691103168874918501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37741303794068779249945667 56611955691103168874918501)
      ·
        refine ⟨10614741692081844164047219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56611955691103168874918501 10614741692081844164047219)
        ·
          refine ⟨15922112538122766246070829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614741692081844164047219 15922112538122766246070829)
          ·
            refine ⟨5970792201796037342276561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15922112538122766246070829 5970792201796037342276561)
            ·
              refine ⟨4478094151347028006707421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970792201796037342276561 4478094151347028006707421)
              ·
                refine ⟨1679285306755135502515283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4478094151347028006707421 1679285306755135502515283)
                ·
                  refine ⟨2518927960132703253772925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679285306755135502515283 2518927960132703253772925)
                  ·
                    refine ⟨944597985049763720164847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518927960132703253772925 944597985049763720164847)
                    ·
                      rfl

theorem cell22_2759397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_2759397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759397 prefixEnd_2759397 := by exact prefixLift 2759397
  have htrace : WordTrace (prefixWord ++ tailWord_2759397) baseStart_2759397 baseEnd_2759397 := by
    simpa [prefixWord, tailWord_2759397, baseEnd_2759397] using wordTrace_append hprefix tailTrace_2759397
  have hstable : (prefixWord ++ tailWord_2759397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759397).length < 2 ^ (prefixWord ++ tailWord_2759397).sum := by decide
  have hdescent : baseEnd_2759397 < baseStart_2759397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759410 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_2759410 : Nat := 118140960795 + 2759410 * 2 ^ 59
def prefixEnd_2759410 : Nat := 4983230072969 + 3 ^ 40 * 2759410 * 2
def baseEnd_2759410 : Nat := 314867478405145339863269

theorem tailTrace_2759410 : CollatzResearch.WordTrace tailWord_2759410 prefixEnd_2759410 314867478405145339863269 := by
  unfold tailWord_2759410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25160987733284078638352921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67095967288757543035607789 25160987733284078638352921)
  ·
    refine ⟨18870740799963058978764691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25160987733284078638352921 18870740799963058978764691)
    ·
      refine ⟨28306111199944588468147037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18870740799963058978764691 28306111199944588468147037)
      ·
        refine ⟨10614791699979220675555139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28306111199944588468147037 10614791699979220675555139)
        ·
          refine ⟨15922187549968831013332709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614791699979220675555139 15922187549968831013332709)
          ·
            refine ⟨2985410165619155814999883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15922187549968831013332709 2985410165619155814999883)
            ·
              refine ⟨4478115248428733722499825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985410165619155814999883 4478115248428733722499825)
              ·
                refine ⟨3358586436321550291874869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4478115248428733722499825 3358586436321550291874869)
                ·
                  refine ⟨314867478405145339863269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3358586436321550291874869 314867478405145339863269)
                  ·
                    rfl

theorem cell22_2759410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_2759410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759410 prefixEnd_2759410 := by exact prefixLift 2759410
  have htrace : WordTrace (prefixWord ++ tailWord_2759410) baseStart_2759410 baseEnd_2759410 := by
    simpa [prefixWord, tailWord_2759410, baseEnd_2759410] using wordTrace_append hprefix tailTrace_2759410
  have hstable : (prefixWord ++ tailWord_2759410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759410).length < 2 ^ (prefixWord ++ tailWord_2759410).sum := by decide
  have hdescent : baseEnd_2759410 < baseStart_2759410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759455 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 4]
def baseStart_2759455 : Nat := 118140960795 + 2759455 * 2 ^ 59
def prefixEnd_2759455 : Nat := 4983230072969 + 3 ^ 40 * 2759455 * 2
def baseEnd_2759455 : Nat := 314872613211690300738223

theorem tailTrace_2759455 : CollatzResearch.WordTrace tailWord_2759455 prefixEnd_2759455 314872613211690300738223 := by
  unfold tailWord_2759455
  simp only [CollatzResearch.WordTrace]
  refine ⟨100645592217973287238799819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67097061478648858159199879 100645592217973287238799819)
  ·
    refine ⟨150968388326959930858199729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100645592217973287238799819 150968388326959930858199729)
    ·
      refine ⟨113226291245219948143649797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150968388326959930858199729 113226291245219948143649797)
      ·
        refine ⟨21229929608478740276934337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113226291245219948143649797 21229929608478740276934337)
        ·
          refine ⟨15922447206359055207700753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21229929608478740276934337 15922447206359055207700753)
          ·
            refine ⟨11941835404769291405775565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15922447206359055207700753 11941835404769291405775565)
            ·
              refine ⟨4478188276788484277165837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11941835404769291405775565 4478188276788484277165837)
              ·
                refine ⟨1679320603795681603937189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4478188276788484277165837 1679320603795681603937189)
                ·
                  refine ⟨314872613211690300738223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679320603795681603937189 314872613211690300738223)
                  ·
                    rfl

theorem cell22_2759455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 4].length) (baseStart_2759455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759455 prefixEnd_2759455 := by exact prefixLift 2759455
  have htrace : WordTrace (prefixWord ++ tailWord_2759455) baseStart_2759455 baseEnd_2759455 := by
    simpa [prefixWord, tailWord_2759455, baseEnd_2759455] using wordTrace_append hprefix tailTrace_2759455
  have hstable : (prefixWord ++ tailWord_2759455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759455).length < 2 ^ (prefixWord ++ tailWord_2759455).sum := by decide
  have hdescent : baseEnd_2759455 < baseStart_2759455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759468 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_2759468 : Nat := 118140960795 + 2759468 * 2 ^ 59
def prefixEnd_2759468 : Nat := 4983230072969 + 3 ^ 40 * 2759468 * 2
def baseEnd_2759468 : Nat := 944622289800743201639629

theorem tailTrace_2759468 : CollatzResearch.WordTrace tailWord_2759468 prefixEnd_2759468 944622289800743201639629 := by
  unfold tailWord_2759468
  simp only [CollatzResearch.WordTrace]
  refine ⟨50323033183463095229511529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67097377577950793639348705 50323033183463095229511529)
  ·
    refine ⟨37742274887597321422133647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50323033183463095229511529 37742274887597321422133647)
    ·
      refine ⟨56613412331395982133200471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37742274887597321422133647 56613412331395982133200471)
      ·
        refine ⟨84920118497093973199800707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56613412331395982133200471 84920118497093973199800707)
        ·
          refine ⟨127380177745640959799701061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84920118497093973199800707 127380177745640959799701061)
          ·
            refine ⟨23883783327307679962443949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127380177745640959799701061 23883783327307679962443949)
            ·
              refine ⟨8956418747740379985916481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23883783327307679962443949 8956418747740379985916481)
              ·
                refine ⟨6717314060805284989437361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8956418747740379985916481 6717314060805284989437361)
                ·
                  refine ⟨5037985545603963742078021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717314060805284989437361 5037985545603963742078021)
                  ·
                    refine ⟨944622289800743201639629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037985545603963742078021 944622289800743201639629)
                    ·
                      rfl

theorem cell22_2759468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_2759468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759468 prefixEnd_2759468 := by exact prefixLift 2759468
  have htrace : WordTrace (prefixWord ++ tailWord_2759468) baseStart_2759468 baseEnd_2759468 := by
    simpa [prefixWord, tailWord_2759468, baseEnd_2759468] using wordTrace_append hprefix tailTrace_2759468
  have hstable : (prefixWord ++ tailWord_2759468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759468).length < 2 ^ (prefixWord ++ tailWord_2759468).sum := by decide
  have hdescent : baseEnd_2759468 < baseStart_2759468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759487 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 2, 3]
def baseStart_2759487 : Nat := 118140960795 + 2759487 * 2 ^ 59
def prefixEnd_2759487 : Nat := 4983230072969 + 3 ^ 40 * 2759487 * 2
def baseEnd_2759487 : Nat := 944628793889033485414571

theorem tailTrace_2759487 : CollatzResearch.WordTrace tailWord_2759487 prefixEnd_2759487 944628793889033485414571 := by
  unfold tailWord_2759487
  simp only [CollatzResearch.WordTrace]
  refine ⟨100646759353857356703964715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67097839569238237802643143 100646759353857356703964715)
  ·
    refine ⟨150970139030786035055947073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100646759353857356703964715 150970139030786035055947073)
    ·
      refine ⟨113227604273089526291960305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150970139030786035055947073 113227604273089526291960305)
      ·
        refine ⟨84920703204817144718970229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113227604273089526291960305 84920703204817144718970229)
        ·
          refine ⟨7961315925451607317403459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84920703204817144718970229 7961315925451607317403459)
          ·
            refine ⟨11941973888177410976105189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7961315925451607317403459 11941973888177410976105189)
            ·
              refine ⟨2239120104033264558019723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11941973888177410976105189 2239120104033264558019723)
              ·
                refine ⟨3358680156049896837029585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239120104033264558019723 3358680156049896837029585)
                ·
                  refine ⟨2519010117037422627772189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358680156049896837029585 2519010117037422627772189)
                  ·
                    refine ⟨944628793889033485414571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519010117037422627772189 944628793889033485414571)
                    ·
                      rfl

theorem cell22_2759487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_2759487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759487 prefixEnd_2759487 := by exact prefixLift 2759487
  have htrace : WordTrace (prefixWord ++ tailWord_2759487) baseStart_2759487 baseEnd_2759487 := by
    simpa [prefixWord, tailWord_2759487, baseEnd_2759487] using wordTrace_append hprefix tailTrace_2759487
  have hstable : (prefixWord ++ tailWord_2759487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759487).length < 2 ^ (prefixWord ++ tailWord_2759487).sum := by decide
  have hdescent : baseEnd_2759487 < baseStart_2759487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759532 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_2759532 : Nat := 118140960795 + 2759532 * 2 ^ 59
def prefixEnd_2759532 : Nat := 4983230072969 + 3 ^ 40 * 2759532 * 2
def baseEnd_2759532 : Nat := 944644198308668368039433

theorem tailTrace_2759532 : CollatzResearch.WordTrace tailWord_2759532 prefixEnd_2759532 944644198308668368039433 := by
  unfold tailWord_2759532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50324200319347164694676425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67098933759129552926235233 50324200319347164694676425)
  ·
    refine ⟨37743150239510373521007319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50324200319347164694676425 37743150239510373521007319)
    ·
      refine ⟨56614725359265560281510979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37743150239510373521007319 56614725359265560281510979)
      ·
        refine ⟨84922088038898340422266469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56614725359265560281510979 84922088038898340422266469)
        ·
          refine ⟨15922891507293438829174963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84922088038898340422266469 15922891507293438829174963)
          ·
            refine ⟨23884337260940158243762445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15922891507293438829174963 23884337260940158243762445)
            ·
              refine ⟨8956626472852559341410917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23884337260940158243762445 8956626472852559341410917)
              ·
                refine ⟨1679367463659854876514547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8956626472852559341410917 1679367463659854876514547)
                ·
                  refine ⟨2519051195489782314771821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679367463659854876514547 2519051195489782314771821)
                  ·
                    refine ⟨944644198308668368039433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519051195489782314771821 944644198308668368039433)
                    ·
                      rfl

theorem cell22_2759532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_2759532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759532 prefixEnd_2759532 := by exact prefixLift 2759532
  have htrace : WordTrace (prefixWord ++ tailWord_2759532) baseStart_2759532 baseEnd_2759532 := by
    simpa [prefixWord, tailWord_2759532, baseEnd_2759532] using wordTrace_append hprefix tailTrace_2759532
  have hstable : (prefixWord ++ tailWord_2759532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759532).length < 2 ^ (prefixWord ++ tailWord_2759532).sum := by decide
  have hdescent : baseEnd_2759532 < baseStart_2759532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759575 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2759575 : Nat := 118140960795 + 2759575 * 2 ^ 59
def prefixEnd_2759575 : Nat := 4983230072969 + 3 ^ 40 * 2759575 * 2
def baseEnd_2759575 : Nat := 944658918087430589214301

theorem tailTrace_2759575 : CollatzResearch.WordTrace tailWord_2759575 prefixEnd_2759575 944658918087430589214301 := by
  unfold tailWord_2759575
  simp only [CollatzResearch.WordTrace]
  refine ⟨100649968977538547733168179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67099979318359031822112119 100649968977538547733168179)
  ·
    refine ⟨150974953466307821599752269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100649968977538547733168179 150974953466307821599752269)
    ·
      refine ⟨56615607549865433099907101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150974953466307821599752269 56615607549865433099907101)
      ·
        refine ⟨21230852831199537412465163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56615607549865433099907101 21230852831199537412465163)
        ·
          refine ⟨31846279246799306118697745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21230852831199537412465163 31846279246799306118697745)
          ·
            refine ⟨23884709435099479589023309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31846279246799306118697745 23884709435099479589023309)
            ·
              refine ⟨8956766038162304845883741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23884709435099479589023309 8956766038162304845883741)
              ·
                refine ⟨3358787264310864317206403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8956766038162304845883741 3358787264310864317206403)
                ·
                  refine ⟨5038180896466296475809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358787264310864317206403 5038180896466296475809605)
                  ·
                    refine ⟨944658918087430589214301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038180896466296475809605 944658918087430589214301)
                    ·
                      rfl

theorem cell22_2759575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2759575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759575 prefixEnd_2759575 := by exact prefixLift 2759575
  have htrace : WordTrace (prefixWord ++ tailWord_2759575) baseStart_2759575 baseEnd_2759575 := by
    simpa [prefixWord, tailWord_2759575, baseEnd_2759575] using wordTrace_append hprefix tailTrace_2759575
  have hstable : (prefixWord ++ tailWord_2759575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759575).length < 2 ^ (prefixWord ++ tailWord_2759575).sum := by decide
  have hdescent : baseEnd_2759575 < baseStart_2759575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_2759603 : Nat := 118140960795 + 2759603 * 2 ^ 59
def prefixEnd_2759603 : Nat := 4983230072969 + 3 ^ 40 * 2759603 * 2
def baseEnd_2759603 : Nat := 944668503059647849514215

theorem tailTrace_2759603 : CollatzResearch.WordTrace tailWord_2759603 prefixEnd_2759603 944668503059647849514215 := by
  unfold tailWord_2759603
  simp only [CollatzResearch.WordTrace]
  refine ⟨100650990221437108515187463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67100660147624739010124975 100650990221437108515187463)
  ·
    refine ⟨150976485332155662772781195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100650990221437108515187463 150976485332155662772781195)
    ·
      refine ⟨226464727998233494159171793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150976485332155662772781195 226464727998233494159171793)
      ·
        refine ⟨169848545998675120619378845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226464727998233494159171793 169848545998675120619378845)
        ·
          refine ⟨63693204749503170232267067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169848545998675120619378845 63693204749503170232267067)
          ·
            refine ⟨95539807124254755348400601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63693204749503170232267067 95539807124254755348400601)
            ·
              refine ⟨71654855343191066511300451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95539807124254755348400601 71654855343191066511300451)
              ·
                refine ⟨107482283014786599766950677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71654855343191066511300451 107482283014786599766950677)
                ·
                  refine ⟨5038232016318121864075813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107482283014786599766950677 5038232016318121864075813)
                  ·
                    refine ⟨944668503059647849514215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038232016318121864075813 944668503059647849514215)
                    ·
                      rfl

theorem cell22_2759603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_2759603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759603 prefixEnd_2759603 := by exact prefixLift 2759603
  have htrace : WordTrace (prefixWord ++ tailWord_2759603) baseStart_2759603 baseEnd_2759603 := by
    simpa [prefixWord, tailWord_2759603, baseEnd_2759603] using wordTrace_append hprefix tailTrace_2759603
  have hstable : (prefixWord ++ tailWord_2759603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759603).length < 2 ^ (prefixWord ++ tailWord_2759603).sum := by decide
  have hdescent : baseEnd_2759603 < baseStart_2759603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759624 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_2759624 : Nat := 118140960795 + 2759624 * 2 ^ 59
def prefixEnd_2759624 : Nat := 4983230072969 + 3 ^ 40 * 2759624 * 2
def baseEnd_2759624 : Nat := 314891897262936931579717

theorem tailTrace_2759624 : CollatzResearch.WordTrace tailWord_2759624 prefixEnd_2759624 314891897262936931579717 := by
  unfold tailWord_2759624
  simp only [CollatzResearch.WordTrace]
  refine ⟨50325878077180514550850963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67101170769574019401134617 50325878077180514550850963)
  ·
    refine ⟨75488817115770771826276445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50325878077180514550850963 75488817115770771826276445)
    ·
      refine ⟨28308306418414039434853667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75488817115770771826276445 28308306418414039434853667)
      ·
        refine ⟨42462459627621059152280501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28308306418414039434853667 42462459627621059152280501)
        ·
          refine ⟨3980855590089474295526297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42462459627621059152280501 3980855590089474295526297)
          ·
            refine ⟨2985641692567105721644723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3980855590089474295526297 2985641692567105721644723)
            ·
              refine ⟨4478462538850658582467085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985641692567105721644723 4478462538850658582467085)
              ·
                refine ⟨1679423452068996968425157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4478462538850658582467085 1679423452068996968425157)
                ·
                  refine ⟨314891897262936931579717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1679423452068996968425157 314891897262936931579717)
                  ·
                    rfl

theorem cell22_2759624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_2759624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759624 prefixEnd_2759624 := by exact prefixLift 2759624
  have htrace : WordTrace (prefixWord ++ tailWord_2759624) baseStart_2759624 baseEnd_2759624 := by
    simpa [prefixWord, tailWord_2759624, baseEnd_2759624] using wordTrace_append hprefix tailTrace_2759624
  have hstable : (prefixWord ++ tailWord_2759624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759624).length < 2 ^ (prefixWord ++ tailWord_2759624).sum := by decide
  have hdescent : baseEnd_2759624 < baseStart_2759624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759637 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2759637 : Nat := 118140960795 + 2759637 * 2 ^ 59
def prefixEnd_2759637 : Nat := 4983230072969 + 3 ^ 40 * 2759637 * 2
def baseEnd_2759637 : Nat := 944680141954483094164111

theorem tailTrace_2759637 : CollatzResearch.WordTrace tailWord_2759637 prefixEnd_2759637 944680141954483094164111 := by
  unfold tailWord_2759637
  simp only [CollatzResearch.WordTrace]
  refine ⟨100652230303313932321925165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67101486868875954881283443 100652230303313932321925165)
  ·
    refine ⟨37744586363742724620721937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100652230303313932321925165 37744586363742724620721937)
    ·
      refine ⟨28308439772807043465541453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37744586363742724620721937 28308439772807043465541453)
      ·
        refine ⟨10615664914802641299578045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28308439772807043465541453 10615664914802641299578045)
        ·
          refine ⟨3980874343050990487341767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10615664914802641299578045 3980874343050990487341767)
          ·
            refine ⟨5971311514576485731012651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980874343050990487341767 5971311514576485731012651)
            ·
              refine ⟨8956967271864728596518977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5971311514576485731012651 8956967271864728596518977)
              ·
                refine ⟨6717725453898546447389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8956967271864728596518977 6717725453898546447389233)
                ·
                  refine ⟨5038294090423909835541925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717725453898546447389233 5038294090423909835541925)
                  ·
                    refine ⟨944680141954483094164111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038294090423909835541925 944680141954483094164111)
                    ·
                      rfl

theorem cell22_2759637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2759637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759637 prefixEnd_2759637 := by exact prefixLift 2759637
  have htrace : WordTrace (prefixWord ++ tailWord_2759637) baseStart_2759637 baseEnd_2759637 := by
    simpa [prefixWord, tailWord_2759637, baseEnd_2759637] using wordTrace_append hprefix tailTrace_2759637
  have hstable : (prefixWord ++ tailWord_2759637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759637).length < 2 ^ (prefixWord ++ tailWord_2759637).sum := by decide
  have hdescent : baseEnd_2759637 < baseStart_2759637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759701 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2759701 : Nat := 118140960795 + 2759701 * 2 ^ 59
def prefixEnd_2759701 : Nat := 4983230072969 + 3 ^ 40 * 2759701 * 2
def baseEnd_2759701 : Nat := 944702050462408260563915

theorem tailTrace_2759701 : CollatzResearch.WordTrace tailWord_2759701 prefixEnd_2759701 944702050462408260563915 := by
  unfold tailWord_2759701
  simp only [CollatzResearch.WordTrace]
  refine ⟨100654564575082071252254957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67103043050054714168169971 100654564575082071252254957)
  ·
    refine ⟨37745461715655776719595609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100654564575082071252254957 37745461715655776719595609)
    ·
      refine ⟨28309096286741832539696707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37745461715655776719595609 28309096286741832539696707)
      ·
        refine ⟨42463644430112748809545061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28309096286741832539696707 42463644430112748809545061)
        ·
          refine ⟨7961933330646140401789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42463644430112748809545061 7961933330646140401789699)
          ·
            refine ⟨11942899995969210602684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7961933330646140401789699 11942899995969210602684549)
            ·
              refine ⟨2239293749244226988003353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11942899995969210602684549 2239293749244226988003353)
              ·
                refine ⟨1679470311933170241002515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239293749244226988003353 1679470311933170241002515)
                ·
                  refine ⟨2519205467899755361503773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679470311933170241002515 2519205467899755361503773)
                  ·
                    refine ⟨944702050462408260563915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519205467899755361503773 944702050462408260563915)
                    ·
                      rfl

theorem cell22_2759701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2759701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759701 prefixEnd_2759701 := by exact prefixLift 2759701
  have htrace : WordTrace (prefixWord ++ tailWord_2759701) baseStart_2759701 baseEnd_2759701 := by
    simpa [prefixWord, tailWord_2759701, baseEnd_2759701] using wordTrace_append hprefix tailTrace_2759701
  have hstable : (prefixWord ++ tailWord_2759701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759701).length < 2 ^ (prefixWord ++ tailWord_2759701).sum := by decide
  have hdescent : baseEnd_2759701 < baseStart_2759701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759819 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 1, 3]
def baseStart_2759819 : Nat := 118140960795 + 2759819 * 2 ^ 59
def prefixEnd_2759819 : Nat := 4983230072969 + 3 ^ 40 * 2759819 * 2
def baseEnd_2759819 : Nat := 944742444273895286113553

theorem tailTrace_2759819 : CollatzResearch.WordTrace tailWord_2759819 prefixEnd_2759819 944742444273895286113553 := by
  unfold tailWord_2759819
  simp only [CollatzResearch.WordTrace]
  refine ⟨100658868388654577405050511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67105912259103051603367007 100658868388654577405050511)
  ·
    refine ⟨150988302582981866107575767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100658868388654577405050511 150988302582981866107575767)
    ·
      refine ⟨226482453874472799161363651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150988302582981866107575767 226482453874472799161363651)
      ·
        refine ⟨339723680811709198742045477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226482453874472799161363651 339723680811709198742045477)
        ·
          refine ⟨63698190152195474764133527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339723680811709198742045477 63698190152195474764133527)
          ·
            refine ⟨95547285228293212146200291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63698190152195474764133527 95547285228293212146200291)
            ·
              refine ⟨143320927842439818219300437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95547285228293212146200291 143320927842439818219300437)
              ·
                refine ⟨1679542123153591619757427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 143320927842439818219300437 1679542123153591619757427)
                ·
                  refine ⟨2519313184730387429636141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679542123153591619757427 2519313184730387429636141)
                  ·
                    refine ⟨944742444273895286113553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519313184730387429636141 944742444273895286113553)
                    ·
                      rfl

theorem cell22_2759819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 3].length) (baseStart_2759819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759819 prefixEnd_2759819 := by exact prefixLift 2759819
  have htrace : WordTrace (prefixWord ++ tailWord_2759819) baseStart_2759819 baseEnd_2759819 := by
    simpa [prefixWord, tailWord_2759819, baseEnd_2759819] using wordTrace_append hprefix tailTrace_2759819
  have hstable : (prefixWord ++ tailWord_2759819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759819).length < 2 ^ (prefixWord ++ tailWord_2759819).sum := by decide
  have hdescent : baseEnd_2759819 < baseStart_2759819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2759870 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2759870 : Nat := 118140960795 + 2759870 * 2 ^ 59
def prefixEnd_2759870 : Nat := 4983230072969 + 3 ^ 40 * 2759870 * 2
def baseEnd_2759870 : Nat := 944759902616148153088397

theorem tailTrace_2759870 : CollatzResearch.WordTrace tailWord_2759870 prefixEnd_2759870 944759902616148153088397 := by
  unfold tailWord_2759870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582591063933726639394633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67107152340979875410104709 12582591063933726639394633)
  ·
    refine ⟨9436943297950294979545975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12582591063933726639394633 9436943297950294979545975)
    ·
      refine ⟨14155414946925442469318963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9436943297950294979545975 14155414946925442469318963)
      ·
        refine ⟨21233122420388163703978445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155414946925442469318963 21233122420388163703978445)
        ·
          refine ⟨7962420907645561388991917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21233122420388163703978445 7962420907645561388991917)
          ·
            refine ⟨2985907840367085520871969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7962420907645561388991917 2985907840367085520871969)
            ·
              refine ⟨2239430880275314140653977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985907840367085520871969 2239430880275314140653977)
              ·
                refine ⟨1679573160206485605490483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239430880275314140653977 1679573160206485605490483)
                ·
                  refine ⟨2519359740309728408235725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679573160206485605490483 2519359740309728408235725)
                  ·
                    refine ⟨944759902616148153088397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519359740309728408235725 944759902616148153088397)
                    ·
                      rfl

theorem cell22_2759870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2759870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2759870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2759870 prefixEnd_2759870 := by exact prefixLift 2759870
  have htrace : WordTrace (prefixWord ++ tailWord_2759870) baseStart_2759870 baseEnd_2759870 := by
    simpa [prefixWord, tailWord_2759870, baseEnd_2759870] using wordTrace_append hprefix tailTrace_2759870
  have hstable : (prefixWord ++ tailWord_2759870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2759870).length < 2 ^ (prefixWord ++ tailWord_2759870).sum := by decide
  have hdescent : baseEnd_2759870 < baseStart_2759870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2759870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760001 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 5]
def baseStart_2760001 : Nat := 118140960795 + 2760001 * 2 ^ 59
def prefixEnd_2760001 : Nat := 4983230072969 + 3 ^ 40 * 2760001 * 2
def baseEnd_2760001 : Nat := 314934915531102492687665

theorem tailTrace_2760001 : CollatzResearch.WordTrace tailWord_2760001 prefixEnd_2760001 314934915531102492687665 := by
  unfold tailWord_2760001
  simp only [CollatzResearch.WordTrace]
  refine ⟨100665506473995222488175857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67110337649330148325450571 100665506473995222488175857)
  ·
    refine ⟨75499129855496416866131893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100665506473995222488175857 75499129855496416866131893)
    ·
      refine ⟨7078043423952789081199865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75499129855496416866131893 7078043423952789081199865)
      ·
        refine ⟨5308532567964591810899899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7078043423952789081199865 5308532567964591810899899)
        ·
          refine ⟨7962798851946887716349849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308532567964591810899899 7962798851946887716349849)
          ·
            refine ⟨5972099138960165787262387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962798851946887716349849 5972099138960165787262387)
            ·
              refine ⟨8958148708440248680893581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972099138960165787262387 8958148708440248680893581)
              ·
                refine ⟨3359305765665093255335093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8958148708440248680893581 3359305765665093255335093)
                ·
                  refine ⟨314934915531102492687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359305765665093255335093 314934915531102492687665)
                  ·
                    rfl

theorem cell22_2760001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_2760001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760001 prefixEnd_2760001 := by exact prefixLift 2760001
  have htrace : WordTrace (prefixWord ++ tailWord_2760001) baseStart_2760001 baseEnd_2760001 := by
    simpa [prefixWord, tailWord_2760001, baseEnd_2760001] using wordTrace_append hprefix tailTrace_2760001
  have hstable : (prefixWord ++ tailWord_2760001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760001).length < 2 ^ (prefixWord ++ tailWord_2760001).sum := by decide
  have hdescent : baseEnd_2760001 < baseStart_2760001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760014 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2760014 : Nat := 118140960795 + 2760014 * 2 ^ 59
def prefixEnd_2760014 : Nat := 4983230072969 + 3 ^ 40 * 2760014 * 2
def baseEnd_2760014 : Nat := 944809196758979777487955

theorem tailTrace_2760014 : CollatzResearch.WordTrace tailWord_2760014 prefixEnd_2760014 944809196758979777487955 := by
  unfold tailWord_2760014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583247577868515713549887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67110653748632083805599397 12583247577868515713549887)
  ·
    refine ⟨18874871366802773570324831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12583247577868515713549887 18874871366802773570324831)
    ·
      refine ⟨28312307050204160355487247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18874871366802773570324831 28312307050204160355487247)
      ·
        refine ⟨42468460575306240533230871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28312307050204160355487247 42468460575306240533230871)
        ·
          refine ⟨63702690862959360799846307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42468460575306240533230871 63702690862959360799846307)
          ·
            refine ⟨95554036294439041199769461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63702690862959360799846307 95554036294439041199769461)
            ·
              refine ⟨8958190902603660112478387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95554036294439041199769461 8958190902603660112478387)
              ·
                refine ⟨13437286353905490168717581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8958190902603660112478387 13437286353905490168717581)
                ·
                  refine ⟨5038982382714558813269093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13437286353905490168717581 5038982382714558813269093)
                  ·
                    refine ⟨944809196758979777487955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038982382714558813269093 944809196758979777487955)
                    ·
                      rfl

theorem cell22_2760014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2760014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760014 prefixEnd_2760014 := by exact prefixLift 2760014
  have htrace : WordTrace (prefixWord ++ tailWord_2760014) baseStart_2760014 baseEnd_2760014 := by
    simpa [prefixWord, tailWord_2760014, baseEnd_2760014] using wordTrace_append hprefix tailTrace_2760014
  have hstable : (prefixWord ++ tailWord_2760014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760014).length < 2 ^ (prefixWord ++ tailWord_2760014).sum := by decide
  have hdescent : baseEnd_2760014 < baseStart_2760014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760061 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2760061 : Nat := 118140960795 + 2760061 * 2 ^ 59
def prefixEnd_2760061 : Nat := 4983230072969 + 3 ^ 40 * 2760061 * 2
def baseEnd_2760061 : Nat := 944825285819487321562811

theorem tailTrace_2760061 : CollatzResearch.WordTrace tailWord_2760061 prefixEnd_2760061 944825285819487321562811 := by
  unfold tailWord_2760061
  simp only [CollatzResearch.WordTrace]
  refine ⟨100667694853777852735360037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67111796569185235156906691 100667694853777852735360037)
  ·
    refine ⟨18875192785083347387880007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100667694853777852735360037 18875192785083347387880007)
    ·
      refine ⟨28312789177625021081820011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18875192785083347387880007 28312789177625021081820011)
      ·
        refine ⟨42469183766437531622730017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28312789177625021081820011 42469183766437531622730017)
        ·
          refine ⟨31851887824828148717047513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42469183766437531622730017 31851887824828148717047513)
          ·
            refine ⟨23888915868621111537785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31851887824828148717047513 23888915868621111537785635)
            ·
              refine ⟨35833373802931667306678453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23888915868621111537785635 35833373802931667306678453)
              ·
                refine ⟨3359378794024843810001105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35833373802931667306678453 3359378794024843810001105)
                ·
                  refine ⟨2519534095518632857500829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359378794024843810001105 2519534095518632857500829)
                  ·
                    refine ⟨944825285819487321562811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519534095518632857500829 944825285819487321562811)
                    ·
                      rfl

theorem cell22_2760061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2760061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760061 prefixEnd_2760061 := by exact prefixLift 2760061
  have htrace : WordTrace (prefixWord ++ tailWord_2760061) baseStart_2760061 baseEnd_2760061 := by
    simpa [prefixWord, tailWord_2760061, baseEnd_2760061] using wordTrace_append hprefix tailTrace_2760061
  have hstable : (prefixWord ++ tailWord_2760061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760061).length < 2 ^ (prefixWord ++ tailWord_2760061).sum := by decide
  have hdescent : baseEnd_2760061 < baseStart_2760061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760082 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2760082 : Nat := 118140960795 + 2760082 * 2 ^ 59
def prefixEnd_2760082 : Nat := 4983230072969 + 3 ^ 40 * 2760082 * 2
def baseEnd_2760082 : Nat := 944832474548650266787747

theorem tailTrace_2760082 : CollatzResearch.WordTrace tailWord_2760082 prefixEnd_2760082 944832474548650266787747 := by
  unfold tailWord_2760082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167115196675443330468625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67112307191134515547916333 25167115196675443330468625)
  ·
    refine ⟨18875336397506582497851469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25167115196675443330468625 18875336397506582497851469)
    ·
      refine ⟨7078251149064968436694301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18875336397506582497851469 7078251149064968436694301)
      ·
        refine ⟨2654344180899363163760363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7078251149064968436694301 2654344180899363163760363)
        ·
          refine ⟨3981516271349044745640545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2654344180899363163760363 3981516271349044745640545)
          ·
            refine ⟨2986137203511783559230409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981516271349044745640545 2986137203511783559230409)
            ·
              refine ⟨2239602902633837669422807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986137203511783559230409 2239602902633837669422807)
              ·
                refine ⟨3359404353950756504134211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239602902633837669422807 3359404353950756504134211)
                ·
                  refine ⟨5039106530926134756201317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359404353950756504134211 5039106530926134756201317)
                  ·
                    refine ⟨944832474548650266787747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039106530926134756201317 944832474548650266787747)
                    ·
                      rfl

theorem cell22_2760082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2760082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760082 prefixEnd_2760082 := by exact prefixLift 2760082
  have htrace : WordTrace (prefixWord ++ tailWord_2760082) baseStart_2760082 baseEnd_2760082 := by
    simpa [prefixWord, tailWord_2760082, baseEnd_2760082] using wordTrace_append hprefix tailTrace_2760082
  have hstable : (prefixWord ++ tailWord_2760082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760082).length < 2 ^ (prefixWord ++ tailWord_2760082).sum := by decide
  have hdescent : baseEnd_2760082 < baseStart_2760082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760140 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_2760140 : Nat := 118140960795 + 2760140 * 2 ^ 59
def prefixEnd_2760140 : Nat := 4983230072969 + 3 ^ 40 * 2760140 * 2
def baseEnd_2760140 : Nat := 944852329133957448837569

theorem tailTrace_2760140 : CollatzResearch.WordTrace tailWord_2760140 prefixEnd_2760140 944852329133957448837569 := by
  unfold tailWord_2760140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50335288110245824613742937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67113717480327766151657249 50335288110245824613742937)
  ·
    refine ⟨37751466082684368460307203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50335288110245824613742937 37751466082684368460307203)
    ·
      refine ⟨56627199124026552690460805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37751466082684368460307203 56627199124026552690460805)
      ·
        refine ⟨10617599835754978629461401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56627199124026552690460805 10617599835754978629461401)
        ·
          refine ⟨7963199876816233972096051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10617599835754978629461401 7963199876816233972096051)
          ·
            refine ⟨11944799815224350958144077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963199876816233972096051 11944799815224350958144077)
            ·
              refine ⟨4479299930709131609304029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944799815224350958144077 4479299930709131609304029)
              ·
                refine ⟨1679737474015924353489011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4479299930709131609304029 1679737474015924353489011)
                ·
                  refine ⟨2519606211023886530233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679737474015924353489011 2519606211023886530233517)
                  ·
                    refine ⟨944852329133957448837569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519606211023886530233517 944852329133957448837569)
                    ·
                      rfl

theorem cell22_2760140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_2760140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760140 prefixEnd_2760140 := by exact prefixLift 2760140
  have htrace : WordTrace (prefixWord ++ tailWord_2760140) baseStart_2760140 baseEnd_2760140 := by
    simpa [prefixWord, tailWord_2760140, baseEnd_2760140] using wordTrace_append hprefix tailTrace_2760140
  have hstable : (prefixWord ++ tailWord_2760140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760140).length < 2 ^ (prefixWord ++ tailWord_2760140).sum := by decide
  have hdescent : baseEnd_2760140 < baseStart_2760140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760157 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2760157 : Nat := 118140960795 + 2760157 * 2 ^ 59
def prefixEnd_2760157 : Nat := 4983230072969 + 3 ^ 40 * 2760157 * 2
def baseEnd_2760157 : Nat := 944858148581375071162517

theorem tailTrace_2760157 : CollatzResearch.WordTrace tailWord_2760157 prefixEnd_2760157 944858148581375071162517 := by
  unfold tailWord_2760157
  simp only [CollatzResearch.WordTrace]
  refine ⟨100671196261430061130854725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67114130840953374087236483 100671196261430061130854725)
  ·
    refine ⟨18875849299018136462035261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100671196261430061130854725 18875849299018136462035261)
    ·
      refine ⟨7078443487131801173263223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18875849299018136462035261 7078443487131801173263223)
      ·
        refine ⟨10617665230697701759894835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078443487131801173263223 10617665230697701759894835)
        ·
          refine ⟨15926497846046552639842253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617665230697701759894835 15926497846046552639842253)
          ·
            refine ⟨5972436692267457239940845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15926497846046552639842253 5972436692267457239940845)
            ·
              refine ⟨2239663759600296464977817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5972436692267457239940845 2239663759600296464977817)
              ·
                refine ⟨1679747819700222348733363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239663759600296464977817 1679747819700222348733363)
                ·
                  refine ⟨2519621729550333523100045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679747819700222348733363 2519621729550333523100045)
                  ·
                    refine ⟨944858148581375071162517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519621729550333523100045 944858148581375071162517)
                    ·
                      rfl

theorem cell22_2760157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2760157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760157 prefixEnd_2760157 := by exact prefixLift 2760157
  have htrace : WordTrace (prefixWord ++ tailWord_2760157) baseStart_2760157 baseEnd_2760157 := by
    simpa [prefixWord, tailWord_2760157, baseEnd_2760157] using wordTrace_append hprefix tailTrace_2760157
  have hstable : (prefixWord ++ tailWord_2760157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760157).length < 2 ^ (prefixWord ++ tailWord_2760157).sum := by decide
  have hdescent : baseEnd_2760157 < baseStart_2760157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760170 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_2760170 : Nat := 118140960795 + 2760170 * 2 ^ 59
def prefixEnd_2760170 : Nat := 4983230072969 + 3 ^ 40 * 2760170 * 2
def baseEnd_2760170 : Nat := 314954199582349123529159

theorem tailTrace_2760170 : CollatzResearch.WordTrace tailWord_2760170 prefixEnd_2760170 314954199582349123529159 := by
  unfold tailWord_2760170
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167917602595741087769491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67114446940255309567385309 25167917602595741087769491)
  ·
    refine ⟨37751876403893611631654237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25167917602595741087769491 37751876403893611631654237)
    ·
      refine ⟨14156953651460104361870339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37751876403893611631654237 14156953651460104361870339)
      ·
        refine ⟨21235430477190156542805509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14156953651460104361870339 21235430477190156542805509)
        ·
          refine ⟨3981643214473154351776033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21235430477190156542805509 3981643214473154351776033)
          ·
            refine ⟨2986232410854865763832025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981643214473154351776033 2986232410854865763832025)
            ·
              refine ⟨2239674308141149322874019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986232410854865763832025 2239674308141149322874019)
              ·
                refine ⟨3359511462211723984311029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239674308141149322874019 3359511462211723984311029)
                ·
                  refine ⟨314954199582349123529159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359511462211723984311029 314954199582349123529159)
                  ·
                    rfl

theorem cell22_2760170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_2760170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760170 prefixEnd_2760170 := by exact prefixLift 2760170
  have htrace : WordTrace (prefixWord ++ tailWord_2760170) baseStart_2760170 baseEnd_2760170 := by
    simpa [prefixWord, tailWord_2760170, baseEnd_2760170] using wordTrace_append hprefix tailTrace_2760170
  have hstable : (prefixWord ++ tailWord_2760170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760170).length < 2 ^ (prefixWord ++ tailWord_2760170).sum := by decide
  have hdescent : baseEnd_2760170 < baseStart_2760170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760211 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_2760211 : Nat := 118140960795 + 2760211 * 2 ^ 59
def prefixEnd_2760211 : Nat := 4983230072969 + 3 ^ 40 * 2760211 * 2
def baseEnd_2760211 : Nat := 944876633884936930312351

theorem tailTrace_2760211 : CollatzResearch.WordTrace tailWord_2760211 prefixEnd_2760211 944876633884936930312351 := by
  unfold tailWord_2760211
  simp only [CollatzResearch.WordTrace]
  refine ⟨100673165803234428353320487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67115443868822952235546991 100673165803234428353320487)
  ·
    refine ⟨151009748704851642529980731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100673165803234428353320487 151009748704851642529980731)
    ·
      refine ⟨226514623057277463794971097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151009748704851642529980731 226514623057277463794971097)
      ·
        refine ⟨169885967292958097846228323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226514623057277463794971097 169885967292958097846228323)
        ·
          refine ⟨254828950939437146769342485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169885967292958097846228323 254828950939437146769342485)
          ·
            refine ⟨11945107075286116254812929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 254828950939437146769342485 11945107075286116254812929)
            ·
              refine ⟨8958830306464587191109697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11945107075286116254812929 8958830306464587191109697)
              ·
                refine ⟨6719122729848440393332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8958830306464587191109697 6719122729848440393332273)
                ·
                  refine ⟨5039342047386330294999205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6719122729848440393332273 5039342047386330294999205)
                  ·
                    refine ⟨944876633884936930312351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039342047386330294999205 944876633884936930312351)
                    ·
                      rfl

theorem cell22_2760211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_2760211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760211 prefixEnd_2760211 := by exact prefixLift 2760211
  have htrace : WordTrace (prefixWord ++ tailWord_2760211) baseStart_2760211 baseEnd_2760211 := by
    simpa [prefixWord, tailWord_2760211, baseEnd_2760211] using wordTrace_append hprefix tailTrace_2760211
  have hstable : (prefixWord ++ tailWord_2760211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760211).length < 2 ^ (prefixWord ++ tailWord_2760211).sum := by decide
  have hdescent : baseEnd_2760211 < baseStart_2760211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760213 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_2760213 : Nat := 118140960795 + 2760213 * 2 ^ 59
def prefixEnd_2760213 : Nat := 4983230072969 + 3 ^ 40 * 2760213 * 2
def baseEnd_2760213 : Nat := 944877318525809591762345

theorem tailTrace_2760213 : CollatzResearch.WordTrace tailWord_2760213 prefixEnd_2760213 944877318525809591762345 := by
  unfold tailWord_2760213
  simp only [CollatzResearch.WordTrace]
  refine ⟨100673238749227182694893293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67115492499484788463262195 100673238749227182694893293)
  ·
    refine ⟨37752464530960193510584985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100673238749227182694893293 37752464530960193510584985)
    ·
      refine ⟨28314348398220145132938739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37752464530960193510584985 28314348398220145132938739)
      ·
        refine ⟨42471522597330217699408109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28314348398220145132938739 42471522597330217699408109)
        ·
          refine ⟨15926820973998831637278041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42471522597330217699408109 15926820973998831637278041)
          ·
            refine ⟨11945115730499123727958531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15926820973998831637278041 11945115730499123727958531)
            ·
              refine ⟨17917673595748685591937797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11945115730499123727958531 17917673595748685591937797)
              ·
                refine ⟨3359563799202878548488337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17917673595748685591937797 3359563799202878548488337)
                ·
                  refine ⟨2519672849402158911366253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359563799202878548488337 2519672849402158911366253)
                  ·
                    refine ⟨944877318525809591762345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519672849402158911366253 944877318525809591762345)
                    ·
                      rfl

theorem cell22_2760213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_2760213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760213 prefixEnd_2760213 := by exact prefixLift 2760213
  have htrace : WordTrace (prefixWord ++ tailWord_2760213) baseStart_2760213 baseEnd_2760213 := by
    simpa [prefixWord, tailWord_2760213, baseEnd_2760213] using wordTrace_append hprefix tailTrace_2760213
  have hstable : (prefixWord ++ tailWord_2760213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760213).length < 2 ^ (prefixWord ++ tailWord_2760213).sum := by decide
  have hdescent : baseEnd_2760213 < baseStart_2760213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760226 : List Nat := [3, 3, 1, 1, 1, 1, 5, 7]
def baseStart_2760226 : Nat := 118140960795 + 2760226 * 2 ^ 59
def prefixEnd_2760226 : Nat := 4983230072969 + 3 ^ 40 * 2760226 * 2
def baseEnd_2760226 : Nat := 104986863187942432354145

theorem tailTrace_2760226 : CollatzResearch.WordTrace tailWord_2760226 prefixEnd_2760226 104986863187942432354145 := by
  unfold tailWord_2760226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168428224545021478779133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67115808598786723943411021 25168428224545021478779133)
  ·
    refine ⟨9438160584204383054542175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25168428224545021478779133 9438160584204383054542175)
    ·
      refine ⟨14157240876306574581813263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9438160584204383054542175 14157240876306574581813263)
      ·
        refine ⟨21235861314459861872719895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14157240876306574581813263 21235861314459861872719895)
        ·
          refine ⟨31853791971689792809079843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21235861314459861872719895 31853791971689792809079843)
          ·
            refine ⟨47780687957534689213619765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31853791971689792809079843 47780687957534689213619765)
            ·
              refine ⟨4479439496018877113776853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47780687957534689213619765 4479439496018877113776853)
              ·
                refine ⟨104986863187942432354145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4479439496018877113776853 104986863187942432354145)
                ·
                  rfl

theorem cell22_2760226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_2760226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760226 prefixEnd_2760226 := by exact prefixLift 2760226
  have htrace : WordTrace (prefixWord ++ tailWord_2760226) baseStart_2760226 baseEnd_2760226 := by
    simpa [prefixWord, tailWord_2760226, baseEnd_2760226] using wordTrace_append hprefix tailTrace_2760226
  have hstable : (prefixWord ++ tailWord_2760226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760226).length < 2 ^ (prefixWord ++ tailWord_2760226).sum := by decide
  have hdescent : baseEnd_2760226 < baseStart_2760226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760309 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2760309 : Nat := 118140960795 + 2760309 * 2 ^ 59
def prefixEnd_2760309 : Nat := 4983230072969 + 3 ^ 40 * 2760309 * 2
def baseEnd_2760309 : Nat := 944910181287697341362051

theorem tailTrace_2760309 : CollatzResearch.WordTrace tailWord_2760309 prefixEnd_2760309 944910181287697341362051 := by
  unfold tailWord_2760309
  simp only [CollatzResearch.WordTrace]
  refine ⟨100676740156879391090387981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67117826771252927393591987 100676740156879391090387981)
  ·
    refine ⟨37753777558829771658895493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100676740156879391090387981 37753777558829771658895493)
    ·
      refine ⟨7078833292280582186042905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37753777558829771658895493 7078833292280582186042905)
      ·
        refine ⟨5309124969210436639532179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7078833292280582186042905 5309124969210436639532179)
        ·
          refine ⟨7963687453815654959298269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309124969210436639532179 7963687453815654959298269)
          ·
            refine ⟨2986382795180870609736851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7963687453815654959298269 2986382795180870609736851)
            ·
              refine ⟨4479574192771305914605277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986382795180870609736851 4479574192771305914605277)
              ·
                refine ⟨1679840322289239717976979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4479574192771305914605277 1679840322289239717976979)
                ·
                  refine ⟨2519760483433859576965469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1679840322289239717976979 2519760483433859576965469)
                  ·
                    refine ⟨944910181287697341362051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519760483433859576965469 944910181287697341362051)
                    ·
                      rfl

theorem cell22_2760309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2760309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760309 prefixEnd_2760309 := by exact prefixLift 2760309
  have htrace : WordTrace (prefixWord ++ tailWord_2760309) baseStart_2760309 baseEnd_2760309 := by
    simpa [prefixWord, tailWord_2760309, baseEnd_2760309] using wordTrace_append hprefix tailTrace_2760309
  have hstable : (prefixWord ++ tailWord_2760309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760309).length < 2 ^ (prefixWord ++ tailWord_2760309).sum := by decide
  have hdescent : baseEnd_2760309 < baseStart_2760309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760382 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2760382 : Nat := 118140960795 + 2760382 * 2 ^ 59
def prefixEnd_2760382 : Nat := 4983230072969 + 3 ^ 40 * 2760382 * 2
def baseEnd_2760382 : Nat := 944935170679549484286827

theorem tailTrace_2760382 : CollatzResearch.WordTrace tailWord_2760382 prefixEnd_2760382 944935170679549484286827 := by
  unfold tailWord_2760382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584925335701865569724425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67119601790409949705196933 12584925335701865569724425)
  ·
    refine ⟨9438694001776399177293319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12584925335701865569724425 9438694001776399177293319)
    ·
      refine ⟨14158041002664598765939979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9438694001776399177293319 14158041002664598765939979)
      ·
        refine ⟨21237061503996898148909969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14158041002664598765939979 21237061503996898148909969)
        ·
          refine ⟨15927796127997673611682477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21237061503996898148909969 15927796127997673611682477)
          ·
            refine ⟨5972923547999127604380929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15927796127997673611682477 5972923547999127604380929)
            ·
              refine ⟨4479692660999345703285697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972923547999127604380929 4479692660999345703285697)
              ·
                refine ⟨3359769495749509277464273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479692660999345703285697 3359769495749509277464273)
                ·
                  refine ⟨2519827121812131958098205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359769495749509277464273 2519827121812131958098205)
                  ·
                    refine ⟨944935170679549484286827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519827121812131958098205 944935170679549484286827)
                    ·
                      rfl

theorem cell22_2760382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2760382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760382 prefixEnd_2760382 := by exact prefixLift 2760382
  have htrace : WordTrace (prefixWord ++ tailWord_2760382) baseStart_2760382 baseEnd_2760382 := by
    simpa [prefixWord, tailWord_2760382, baseEnd_2760382] using wordTrace_append hprefix tailTrace_2760382
  have hstable : (prefixWord ++ tailWord_2760382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760382).length < 2 ^ (prefixWord ++ tailWord_2760382).sum := by decide
  have hdescent : baseEnd_2760382 < baseStart_2760382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760391 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2760391 : Nat := 118140960795 + 2760391 * 2 ^ 59
def prefixEnd_2760391 : Nat := 4983230072969 + 3 ^ 40 * 2760391 * 2
def baseEnd_2760391 : Nat := 944938251563476460811799

theorem tailTrace_2760391 : CollatzResearch.WordTrace tailWord_2760391 prefixEnd_2760391 944938251563476460811799 := by
  unfold tailWord_2760391
  simp only [CollatzResearch.WordTrace]
  refine ⟨100679730942582319094873027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67119820628388212729915351 100679730942582319094873027)
  ·
    refine ⟨151019596413873478642309541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100679730942582319094873027 151019596413873478642309541)
    ·
      refine ⟨28316174327601277245433039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151019596413873478642309541 28316174327601277245433039)
      ·
        refine ⟨42474261491401915868149559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28316174327601277245433039 42474261491401915868149559)
        ·
          refine ⟨63711392237102873802224339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42474261491401915868149559 63711392237102873802224339)
          ·
            refine ⟨95567088355654310703336509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63711392237102873802224339 95567088355654310703336509)
            ·
              refine ⟨35837658133370366513751191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95567088355654310703336509 35837658133370366513751191)
              ·
                refine ⟨53756487200055549770626787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35837658133370366513751191 53756487200055549770626787)
                ·
                  refine ⟨80634730800083324655940181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53756487200055549770626787 80634730800083324655940181)
                  ·
                    refine ⟨944938251563476460811799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80634730800083324655940181 944938251563476460811799)
                    ·
                      rfl

theorem cell22_2760391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2760391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760391 prefixEnd_2760391 := by exact prefixLift 2760391
  have htrace : WordTrace (prefixWord ++ tailWord_2760391) baseStart_2760391 baseEnd_2760391 := by
    simpa [prefixWord, tailWord_2760391, baseEnd_2760391] using wordTrace_append hprefix tailTrace_2760391
  have hstable : (prefixWord ++ tailWord_2760391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760391).length < 2 ^ (prefixWord ++ tailWord_2760391).sum := by decide
  have hdescent : baseEnd_2760391 < baseStart_2760391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760410 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_2760410 : Nat := 118140960795 + 2760410 * 2 ^ 59
def prefixEnd_2760410 : Nat := 4983230072969 + 3 ^ 40 * 2760410 * 2
def baseEnd_2760410 : Nat := 944944755651766744586741

theorem tailTrace_2760410 : CollatzResearch.WordTrace tailWord_2760410 prefixEnd_2760410 944944755651766744586741 := by
  unfold tailWord_2760410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170105982378371334953671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67120282619675656893209789 25170105982378371334953671)
  ·
    refine ⟨37755158973567557002430507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25170105982378371334953671 37755158973567557002430507)
    ·
      refine ⟨56632738460351335503645761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37755158973567557002430507 56632738460351335503645761)
      ·
        refine ⟨42474553845263501627734321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56632738460351335503645761 42474553845263501627734321)
        ·
          refine ⟨31855915383947626220800741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42474553845263501627734321 31855915383947626220800741)
          ·
            refine ⟨5972984134490179916400139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31855915383947626220800741 5972984134490179916400139)
            ·
              refine ⟨8959476201735269874600209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972984134490179916400139 8959476201735269874600209)
              ·
                refine ⟨6719607151301452405950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8959476201735269874600209 6719607151301452405950157)
                ·
                  refine ⟨2519852681738044652231309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6719607151301452405950157 2519852681738044652231309)
                  ·
                    refine ⟨944944755651766744586741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2519852681738044652231309 944944755651766744586741)
                    ·
                      rfl

theorem cell22_2760410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_2760410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760410 prefixEnd_2760410 := by exact prefixLift 2760410
  have htrace : WordTrace (prefixWord ++ tailWord_2760410) baseStart_2760410 baseEnd_2760410 := by
    simpa [prefixWord, tailWord_2760410, baseEnd_2760410] using wordTrace_append hprefix tailTrace_2760410
  have hstable : (prefixWord ++ tailWord_2760410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760410).length < 2 ^ (prefixWord ++ tailWord_2760410).sum := by decide
  have hdescent : baseEnd_2760410 < baseStart_2760410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760412 : List Nat := [2, 2, 5, 1, 2, 1, 3, 6]
def baseStart_2760412 : Nat := 118140960795 + 2760412 * 2 ^ 59
def prefixEnd_2760412 : Nat := 4983230072969 + 3 ^ 40 * 2760412 * 2
def baseEnd_2760412 : Nat := 104993937810293267337415

theorem tailTrace_2760412 : CollatzResearch.WordTrace tailWord_2760412 prefixEnd_2760412 104993937810293267337415 := by
  unfold tailWord_2760412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50340248437753119840693745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67120331250337493120924993 50340248437753119840693745)
  ·
    refine ⟨37755186328314839880520309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50340248437753119840693745 37755186328314839880520309)
    ·
      refine ⟨3539548718279516238798779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37755186328314839880520309 3539548718279516238798779)
      ·
        refine ⟨5309323077419274358198169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539548718279516238798779 5309323077419274358198169)
        ·
          refine ⟨3981992308064455768648627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309323077419274358198169 3981992308064455768648627)
          ·
            refine ⟨5972988462096683652972941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981992308064455768648627 5972988462096683652972941)
            ·
              refine ⟨2239870673286256369864853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5972988462096683652972941 2239870673286256369864853)
              ·
                refine ⟨104993937810293267337415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2239870673286256369864853 104993937810293267337415)
                ·
                  rfl

theorem cell22_2760412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_2760412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760412 prefixEnd_2760412 := by exact prefixLift 2760412
  have htrace : WordTrace (prefixWord ++ tailWord_2760412) baseStart_2760412 baseEnd_2760412 := by
    simpa [prefixWord, tailWord_2760412, baseEnd_2760412] using wordTrace_append hprefix tailTrace_2760412
  have hstable : (prefixWord ++ tailWord_2760412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760412).length < 2 ^ (prefixWord ++ tailWord_2760412).sum := by decide
  have hdescent : baseEnd_2760412 < baseStart_2760412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760483 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_2760483 : Nat := 118140960795 + 2760483 * 2 ^ 59
def prefixEnd_2760483 : Nat := 4983230072969 + 3 ^ 40 * 2760483 * 2
def baseEnd_2760483 : Nat := 944969745043618887511517

theorem tailTrace_2760483 : CollatzResearch.WordTrace tailWord_2760483 prefixEnd_2760483 944969745043618887511517 := by
  unfold tailWord_2760483
  simp only [CollatzResearch.WordTrace]
  refine ⟨100683086458249018807222103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67122057638832679204814735 100683086458249018807222103)
  ·
    refine ⟨151024629687373528210833155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100683086458249018807222103 151024629687373528210833155)
    ·
      refine ⟨226536944531060292316249733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151024629687373528210833155 226536944531060292316249733)
      ·
        refine ⟨42475677099573804809296825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226536944531060292316249733 42475677099573804809296825)
        ·
          refine ⟨31856757824680353606972619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42475677099573804809296825 31856757824680353606972619)
          ·
            refine ⟨47785136737020530410458929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31856757824680353606972619 47785136737020530410458929)
            ·
              refine ⟨35838852552765397807844197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47785136737020530410458929 35838852552765397807844197)
              ·
                refine ⟨6719784853643512088970787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35838852552765397807844197 6719784853643512088970787)
                ·
                  refine ⟨10079677280465268133456181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719784853643512088970787 10079677280465268133456181)
                  ·
                    refine ⟨944969745043618887511517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10079677280465268133456181 944969745043618887511517)
                    ·
                      rfl

theorem cell22_2760483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_2760483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760483 prefixEnd_2760483 := by exact prefixLift 2760483
  have htrace : WordTrace (prefixWord ++ tailWord_2760483) baseStart_2760483 baseEnd_2760483 := by
    simpa [prefixWord, tailWord_2760483, baseEnd_2760483] using wordTrace_append hprefix tailTrace_2760483
  have hstable : (prefixWord ++ tailWord_2760483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760483).length < 2 ^ (prefixWord ++ tailWord_2760483).sum := by decide
  have hdescent : baseEnd_2760483 < baseStart_2760483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760502 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2760502 : Nat := 118140960795 + 2760502 * 2 ^ 59
def prefixEnd_2760502 : Nat := 4983230072969 + 3 ^ 40 * 2760502 * 2
def baseEnd_2760502 : Nat := 314992083043969723762153

theorem tailTrace_2760502 : CollatzResearch.WordTrace tailWord_2760502 prefixEnd_2760502 314992083043969723762153 := by
  unfold tailWord_2760502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292736215323761565760235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67122519630120123368109173 6292736215323761565760235)
  ·
    refine ⟨9439104322985642348640353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6292736215323761565760235 9439104322985642348640353)
    ·
      refine ⟨7079328242239231761480265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9439104322985642348640353 7079328242239231761480265)
      ·
        refine ⟨5309496181679423821110199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7079328242239231761480265 5309496181679423821110199)
        ·
          refine ⟨7964244272519135731665299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309496181679423821110199 7964244272519135731665299)
          ·
            refine ⟨11946366408778703597497949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7964244272519135731665299 11946366408778703597497949)
            ·
              refine ⟨4479887403292013849061731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11946366408778703597497949 4479887403292013849061731)
              ·
                refine ⟨6719831104938020773592597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479887403292013849061731 6719831104938020773592597)
                ·
                  refine ⟨314992083043969723762153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6719831104938020773592597 314992083043969723762153)
                  ·
                    rfl

theorem cell22_2760502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2760502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760502 prefixEnd_2760502 := by exact prefixLift 2760502
  have htrace : WordTrace (prefixWord ++ tailWord_2760502) baseStart_2760502 baseEnd_2760502 := by
    simpa [prefixWord, tailWord_2760502, baseEnd_2760502] using wordTrace_append hprefix tailTrace_2760502
  have hstable : (prefixWord ++ tailWord_2760502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760502).length < 2 ^ (prefixWord ++ tailWord_2760502).sum := by decide
  have hdescent : baseEnd_2760502 < baseStart_2760502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760532 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2760532 : Nat := 118140960795 + 2760532 * 2 ^ 59
def prefixEnd_2760532 : Nat := 4983230072969 + 3 ^ 40 * 2760532 * 2
def baseEnd_2760532 : Nat := 944986518744999093036367

theorem tailTrace_2760532 : CollatzResearch.WordTrace tailWord_2760532 prefixEnd_2760532 944986518744999093036367 := by
  unfold tailWord_2760532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50342436817535750087877925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67123249090047666783837233 50342436817535750087877925)
  ·
    refine ⟨9439206903287953141477111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50342436817535750087877925 9439206903287953141477111)
    ·
      refine ⟨14158810354931929712215667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439206903287953141477111 14158810354931929712215667)
      ·
        refine ⟨21238215532397894568323501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14158810354931929712215667 21238215532397894568323501)
        ·
          refine ⟨7964330824649210463121313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21238215532397894568323501 7964330824649210463121313)
          ·
            refine ⟨5973248118486907847340985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7964330824649210463121313 5973248118486907847340985)
            ·
              refine ⟨4479936088865180885505739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973248118486907847340985 4479936088865180885505739)
              ·
                refine ⟨6719904133297771328258609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479936088865180885505739 6719904133297771328258609)
                ·
                  refine ⟨5039928099973328496193957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6719904133297771328258609 5039928099973328496193957)
                  ·
                    refine ⟨944986518744999093036367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039928099973328496193957 944986518744999093036367)
                    ·
                      rfl

theorem cell22_2760532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2760532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760532 prefixEnd_2760532 := by exact prefixLift 2760532
  have htrace : WordTrace (prefixWord ++ tailWord_2760532) baseStart_2760532 baseEnd_2760532 := by
    simpa [prefixWord, tailWord_2760532, baseEnd_2760532] using wordTrace_append hprefix tailTrace_2760532
  have hstable : (prefixWord ++ tailWord_2760532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760532).length < 2 ^ (prefixWord ++ tailWord_2760532).sum := by decide
  have hdescent : baseEnd_2760532 < baseStart_2760532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760596 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2760596 : Nat := 118140960795 + 2760596 * 2 ^ 59
def prefixEnd_2760596 : Nat := 4983230072969 + 3 ^ 40 * 2760596 * 2
def baseEnd_2760596 : Nat := 945008427252924259436171

theorem tailTrace_2760596 : CollatzResearch.WordTrace tailWord_2760596 prefixEnd_2760596 945008427252924259436171 := by
  unfold tailWord_2760596
  simp only [CollatzResearch.WordTrace]
  refine ⟨50343603953419819553042821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67124805271226426070723761 50343603953419819553042821)
  ·
    refine ⟨9439425741266216166195529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50343603953419819553042821 9439425741266216166195529)
    ·
      refine ⟨7079569305949662124646647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9439425741266216166195529 7079569305949662124646647)
      ·
        refine ⟨10619353958924493186969971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7079569305949662124646647 10619353958924493186969971)
        ·
          refine ⟨15929030938386739780454957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619353958924493186969971 15929030938386739780454957)
          ·
            refine ⟨5973386601895027417670609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15929030938386739780454957 5973386601895027417670609)
            ·
              refine ⟨4480039951421270563252957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5973386601895027417670609 4480039951421270563252957)
              ·
                refine ⟨1680014981782976461219859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4480039951421270563252957 1680014981782976461219859)
                ·
                  refine ⟨2520022472674464691829789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680014981782976461219859 2520022472674464691829789)
                  ·
                    refine ⟨945008427252924259436171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520022472674464691829789 945008427252924259436171)
                    ·
                      rfl

theorem cell22_2760596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2760596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760596 prefixEnd_2760596 := by exact prefixLift 2760596
  have htrace : WordTrace (prefixWord ++ tailWord_2760596) baseStart_2760596 baseEnd_2760596 := by
    simpa [prefixWord, tailWord_2760596, baseEnd_2760596] using wordTrace_append hprefix tailTrace_2760596
  have hstable : (prefixWord ++ tailWord_2760596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760596).length < 2 ^ (prefixWord ++ tailWord_2760596).sum := by decide
  have hdescent : baseEnd_2760596 < baseStart_2760596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760609 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 5]
def baseStart_2760609 : Nat := 118140960795 + 2760609 * 2 ^ 59
def prefixEnd_2760609 : Nat := 4983230072969 + 3 ^ 40 * 2760609 * 2
def baseEnd_2760609 : Nat := 315004292472865519620377

theorem tailTrace_2760609 : CollatzResearch.WordTrace tailWord_2760609 prefixEnd_2760609 315004292472865519620377 := by
  unfold tailWord_2760609
  simp only [CollatzResearch.WordTrace]
  refine ⟨100687682055792542326308881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67125121370528361550872587 100687682055792542326308881)
  ·
    refine ⟨75515761541844406744731661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100687682055792542326308881 75515761541844406744731661)
    ·
      refine ⟨28318410578191652529274373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75515761541844406744731661 28318410578191652529274373)
      ·
        refine ⟨5309701983410934849238945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28318410578191652529274373 5309701983410934849238945)
        ·
          refine ⟨3982276487558201136929209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309701983410934849238945 3982276487558201136929209)
          ·
            refine ⟨2986707365668650852696907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3982276487558201136929209 2986707365668650852696907)
            ·
              refine ⟨4480061048502976279045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2986707365668650852696907 4480061048502976279045361)
              ·
                refine ⟨3360045786377232209284021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480061048502976279045361 3360045786377232209284021)
                ·
                  refine ⟨315004292472865519620377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360045786377232209284021 315004292472865519620377)
                  ·
                    rfl

theorem cell22_2760609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_2760609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760609 prefixEnd_2760609 := by exact prefixLift 2760609
  have htrace : WordTrace (prefixWord ++ tailWord_2760609) baseStart_2760609 baseEnd_2760609 := by
    simpa [prefixWord, tailWord_2760609, baseEnd_2760609] using wordTrace_append hprefix tailTrace_2760609
  have hstable : (prefixWord ++ tailWord_2760609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760609).length < 2 ^ (prefixWord ++ tailWord_2760609).sum := by decide
  have hdescent : baseEnd_2760609 < baseStart_2760609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760635 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 6, 3]
def baseStart_2760635 : Nat := 118140960795 + 2760635 * 2 ^ 59
def prefixEnd_2760635 : Nat := 4983230072969 + 3 ^ 40 * 2760635 * 2
def baseEnd_2760635 : Nat := 945021777749941157711051

theorem tailTrace_2760635 : CollatzResearch.WordTrace tailWord_2760635 prefixEnd_2760635 945021777749941157711051 := by
  unfold tailWord_2760635
  simp only [CollatzResearch.WordTrace]
  refine ⟨100688630353698348766755359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67125753569132232511170239 100688630353698348766755359)
  ·
    refine ⟨151032945530547523150133039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100688630353698348766755359 151032945530547523150133039)
    ·
      refine ⟨226549418295821284725199559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151032945530547523150133039 226549418295821284725199559)
      ·
        refine ⟨339824127443731927087799339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226549418295821284725199559 339824127443731927087799339)
        ·
          refine ⟨509736191165597890631699009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339824127443731927087799339 509736191165597890631699009)
          ·
            refine ⟨382302143374198417973774257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509736191165597890631699009 382302143374198417973774257)
            ·
              refine ⟨286726607530648813480330693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382302143374198417973774257 286726607530648813480330693)
              ·
                refine ⟨53761238911996652527562005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286726607530648813480330693 53761238911996652527562005)
                ·
                  refine ⟨2520058073999843087229469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53761238911996652527562005 2520058073999843087229469)
                  ·
                    refine ⟨945021777749941157711051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520058073999843087229469 945021777749941157711051)
                    ·
                      rfl

theorem cell22_2760635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].length) (baseStart_2760635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760635 prefixEnd_2760635 := by exact prefixLift 2760635
  have htrace : WordTrace (prefixWord ++ tailWord_2760635) baseStart_2760635 baseEnd_2760635 := by
    simpa [prefixWord, tailWord_2760635, baseEnd_2760635] using wordTrace_append hprefix tailTrace_2760635
  have hstable : (prefixWord ++ tailWord_2760635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760635).length < 2 ^ (prefixWord ++ tailWord_2760635).sum := by decide
  have hdescent : baseEnd_2760635 < baseStart_2760635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760650 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2760650 : Nat := 118140960795 + 2760650 * 2 ^ 59
def prefixEnd_2760650 : Nat := 4983230072969 + 3 ^ 40 * 2760650 * 2
def baseEnd_2760650 : Nat := 945026912556486118586005

theorem tailTrace_2760650 : CollatzResearch.WordTrace tailWord_2760650 prefixEnd_2760650 945026912556486118586005 := by
  unfold tailWord_2760650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25172294362161001582137851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67126118299096004219034269 25172294362161001582137851)
  ·
    refine ⟨37758441543241502373206777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25172294362161001582137851 37758441543241502373206777)
    ·
      refine ⟨28318831157431126779905083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37758441543241502373206777 28318831157431126779905083)
      ·
        refine ⟨42478246736146690169857625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28318831157431126779905083 42478246736146690169857625)
        ·
          refine ⟨31858685052110017627393219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42478246736146690169857625 31858685052110017627393219)
          ·
            refine ⟨47788027578165026441089829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31858685052110017627393219 47788027578165026441089829)
            ·
              refine ⟨8960255170905942457704343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47788027578165026441089829 8960255170905942457704343)
              ·
                refine ⟨13440382756358913686556515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960255170905942457704343 13440382756358913686556515)
                ·
                  refine ⟨20160574134538370529834773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13440382756358913686556515 20160574134538370529834773)
                  ·
                    refine ⟨945026912556486118586005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20160574134538370529834773 945026912556486118586005)
                    ·
                      rfl

theorem cell22_2760650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2760650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760650 prefixEnd_2760650 := by exact prefixLift 2760650
  have htrace : WordTrace (prefixWord ++ tailWord_2760650) baseStart_2760650 baseEnd_2760650 := by
    simpa [prefixWord, tailWord_2760650, baseEnd_2760650] using wordTrace_append hprefix tailTrace_2760650
  have hstable : (prefixWord ++ tailWord_2760650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760650).length < 2 ^ (prefixWord ++ tailWord_2760650).sum := by decide
  have hdescent : baseEnd_2760650 < baseStart_2760650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760652 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_2760652 : Nat := 118140960795 + 2760652 * 2 ^ 59
def prefixEnd_2760652 : Nat := 4983230072969 + 3 ^ 40 * 2760652 * 2
def baseEnd_2760652 : Nat := 945027597197358780035999

theorem tailTrace_2760652 : CollatzResearch.WordTrace tailWord_2760652 prefixEnd_2760652 945027597197358780035999 := by
  unfold tailWord_2760652
  simp only [CollatzResearch.WordTrace]
  refine ⟨50344625197318380335062105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67126166929757840446749473 50344625197318380335062105)
  ·
    refine ⟨37758468897988785251296579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50344625197318380335062105 37758468897988785251296579)
    ·
      refine ⟨56637703346983177876944869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37758468897988785251296579 56637703346983177876944869)
      ·
        refine ⟨10619569377559345851927163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56637703346983177876944869 10619569377559345851927163)
        ·
          refine ⟨15929354066339018777890745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619569377559345851927163 15929354066339018777890745)
          ·
            refine ⟨11947015549754264083418059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15929354066339018777890745 11947015549754264083418059)
            ·
              refine ⟨17920523324631396125127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11947015549754264083418059 17920523324631396125127089)
              ·
                refine ⟨13440392493473547093845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17920523324631396125127089 13440392493473547093845317)
                ·
                  refine ⟨2520073592526290080095997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13440392493473547093845317 2520073592526290080095997)
                  ·
                    refine ⟨945027597197358780035999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520073592526290080095997 945027597197358780035999)
                    ·
                      rfl

theorem cell22_2760652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_2760652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760652 prefixEnd_2760652 := by exact prefixLift 2760652
  have htrace : WordTrace (prefixWord ++ tailWord_2760652) baseStart_2760652 baseEnd_2760652 := by
    simpa [prefixWord, tailWord_2760652, baseEnd_2760652] using wordTrace_append hprefix tailTrace_2760652
  have hstable : (prefixWord ++ tailWord_2760652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760652).length < 2 ^ (prefixWord ++ tailWord_2760652).sum := by decide
  have hdescent : baseEnd_2760652 < baseStart_2760652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760686 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2760686 : Nat := 118140960795 + 2760686 * 2 ^ 59
def prefixEnd_2760686 : Nat := 4983230072969 + 3 ^ 40 * 2760686 * 2
def baseEnd_2760686 : Nat := 945039236092194024685895

theorem tailTrace_2760686 : CollatzResearch.WordTrace tailWord_2760686 prefixEnd_2760686 945039236092194024685895 := by
  unfold tailWord_2760686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586311309564198059607739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67126993651009056317907941 12586311309564198059607739)
  ·
    refine ⟨18879466964346297089411609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12586311309564198059607739 18879466964346297089411609)
    ·
      refine ⟨14159600223259722817058707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18879466964346297089411609 14159600223259722817058707)
      ·
        refine ⟨21239400334889584225588061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159600223259722817058707 21239400334889584225588061)
        ·
          refine ⟨7964775125583594084595523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21239400334889584225588061 7964775125583594084595523)
          ·
            refine ⟨11947162688375391126893285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7964775125583594084595523 11947162688375391126893285)
            ·
              refine ⟨2240093004070385836292491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11947162688375391126893285 2240093004070385836292491)
              ·
                refine ⟨3360139506105578754438737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240093004070385836292491 3360139506105578754438737)
                ·
                  refine ⟨2520104629579184065829053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3360139506105578754438737 2520104629579184065829053)
                  ·
                    refine ⟨945039236092194024685895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520104629579184065829053 945039236092194024685895)
                    ·
                      rfl

theorem cell22_2760686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2760686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760686 prefixEnd_2760686 := by exact prefixLift 2760686
  have htrace : WordTrace (prefixWord ++ tailWord_2760686) baseStart_2760686 baseEnd_2760686 := by
    simpa [prefixWord, tailWord_2760686, baseEnd_2760686] using wordTrace_append hprefix tailTrace_2760686
  have hstable : (prefixWord ++ tailWord_2760686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760686).length < 2 ^ (prefixWord ++ tailWord_2760686).sum := by decide
  have hdescent : baseEnd_2760686 < baseStart_2760686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760755 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 8]
def baseStart_2760755 : Nat := 118140960795 + 2760755 * 2 ^ 59
def prefixEnd_2760755 : Nat := 4983230072969 + 3 ^ 40 * 2760755 * 2
def baseEnd_2760755 : Nat := 315020952067433614903561

theorem tailTrace_2760755 : CollatzResearch.WordTrace tailWord_2760755 prefixEnd_2760755 315020952067433614903561 := by
  unfold tailWord_2760755
  simp only [CollatzResearch.WordTrace]
  refine ⟨100693007113263609261123719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67128671408842406174082479 100693007113263609261123719)
  ·
    refine ⟨151039510669895413891685579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100693007113263609261123719 151039510669895413891685579)
    ·
      refine ⟨226559266004843120837528369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151039510669895413891685579 226559266004843120837528369)
      ·
        refine ⟨169919449503632340628146277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226559266004843120837528369 169919449503632340628146277)
        ·
          refine ⟨31859896781931063867777427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169919449503632340628146277 31859896781931063867777427)
          ·
            refine ⟨47789845172896595801666141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31859896781931063867777427 47789845172896595801666141)
            ·
              refine ⟨17921191939836223425624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47789845172896595801666141 17921191939836223425624803)
              ·
                refine ⟨26881787909754335138437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17921191939836223425624803 26881787909754335138437205)
                ·
                  refine ⟨315020952067433614903561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26881787909754335138437205 315020952067433614903561)
                  ·
                    rfl

theorem cell22_2760755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_2760755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760755 prefixEnd_2760755 := by exact prefixLift 2760755
  have htrace : WordTrace (prefixWord ++ tailWord_2760755) baseStart_2760755 baseEnd_2760755 := by
    simpa [prefixWord, tailWord_2760755, baseEnd_2760755] using wordTrace_append hprefix tailTrace_2760755
  have hstable : (prefixWord ++ tailWord_2760755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760755).length < 2 ^ (prefixWord ++ tailWord_2760755).sum := by decide
  have hdescent : baseEnd_2760755 < baseStart_2760755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760757 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2760757 : Nat := 118140960795 + 2760757 * 2 ^ 59
def prefixEnd_2760757 : Nat := 4983230072969 + 3 ^ 40 * 2760757 * 2
def baseEnd_2760757 : Nat := 945063540843173506160677

theorem tailTrace_2760757 : CollatzResearch.WordTrace tailWord_2760757 prefixEnd_2760757 945063540843173506160677 := by
  unfold tailWord_2760757
  simp only [CollatzResearch.WordTrace]
  refine ⟨100693080059256363602696525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67128720039504242401797683 100693080059256363602696525)
  ·
    refine ⟨37759905022221136351011197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100693080059256363602696525 37759905022221136351011197)
    ·
      refine ⟨14159964383332926131629199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37759905022221136351011197 14159964383332926131629199)
      ·
        refine ⟨21239946574999389197443799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159964383332926131629199 21239946574999389197443799)
        ·
          refine ⟨31859919862499083796165699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239946574999389197443799 31859919862499083796165699)
          ·
            refine ⟨47789879793748625694248549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31859919862499083796165699 47789879793748625694248549)
            ·
              refine ⟨8960602461327867317671603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47789879793748625694248549 8960602461327867317671603)
              ·
                refine ⟨13440903691991800976507405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960602461327867317671603 13440903691991800976507405)
                ·
                  refine ⟨5040338884496925366190277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13440903691991800976507405 5040338884496925366190277)
                  ·
                    refine ⟨945063540843173506160677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040338884496925366190277 945063540843173506160677)
                    ·
                      rfl

theorem cell22_2760757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2760757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760757 prefixEnd_2760757 := by exact prefixLift 2760757
  have htrace : WordTrace (prefixWord ++ tailWord_2760757) baseStart_2760757 baseEnd_2760757 := by
    simpa [prefixWord, tailWord_2760757, baseEnd_2760757] using wordTrace_append hprefix tailTrace_2760757
  have hstable : (prefixWord ++ tailWord_2760757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760757).length < 2 ^ (prefixWord ++ tailWord_2760757).sum := by decide
  have hdescent : baseEnd_2760757 < baseStart_2760757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760789 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 4]
def baseStart_2760789 : Nat := 118140960795 + 2760789 * 2 ^ 59
def prefixEnd_2760789 : Nat := 4983230072969 + 3 ^ 40 * 2760789 * 2
def baseEnd_2760789 : Nat := 315024831699045363120193

theorem tailTrace_2760789 : CollatzResearch.WordTrace tailWord_2760789 prefixEnd_2760789 315024831699045363120193 := by
  unfold tailWord_2760789
  simp only [CollatzResearch.WordTrace]
  refine ⟨100694247195140433067861421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67129498130093622045240947 100694247195140433067861421)
  ·
    refine ⟨37760342698177662400448033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100694247195140433067861421 37760342698177662400448033)
    ·
      refine ⟨28320257023633246800336025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37760342698177662400448033 28320257023633246800336025)
      ·
        refine ⟨21240192767724935100252019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28320257023633246800336025 21240192767724935100252019)
        ·
          refine ⟨31860289151587402650378029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21240192767724935100252019 31860289151587402650378029)
          ·
            refine ⟨11947608431845275993891761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31860289151587402650378029 11947608431845275993891761)
            ·
              refine ⟨8960706323883956995418821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11947608431845275993891761 8960706323883956995418821)
              ·
                refine ⟨1680132435728241936641029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8960706323883956995418821 1680132435728241936641029)
                ·
                  refine ⟨315024831699045363120193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680132435728241936641029 315024831699045363120193)
                  ·
                    rfl

theorem cell22_2760789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_2760789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760789 prefixEnd_2760789 := by exact prefixLift 2760789
  have htrace : WordTrace (prefixWord ++ tailWord_2760789) baseStart_2760789 baseEnd_2760789 := by
    simpa [prefixWord, tailWord_2760789, baseEnd_2760789] using wordTrace_append hprefix tailTrace_2760789
  have hstable : (prefixWord ++ tailWord_2760789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760789).length < 2 ^ (prefixWord ++ tailWord_2760789).sum := by decide
  have hdescent : baseEnd_2760789 < baseStart_2760789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760804 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2760804 : Nat := 118140960795 + 2760804 * 2 ^ 59
def prefixEnd_2760804 : Nat := 4983230072969 + 3 ^ 40 * 2760804 * 2
def baseEnd_2760804 : Nat := 945079629903681050235533

theorem tailTrace_2760804 : CollatzResearch.WordTrace tailWord_2760804 prefixEnd_2760804 945079629903681050235533 := by
  unfold tailWord_2760804
  simp only [CollatzResearch.WordTrace]
  refine ⟨50347397145043045314828733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67129862860057393753104977 50347397145043045314828733)
  ·
    refine ⟨18880273929391141993060775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50347397145043045314828733 18880273929391141993060775)
    ·
      refine ⟨28320410894086712989591163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18880273929391141993060775 28320410894086712989591163)
      ·
        refine ⟨42480616341130069484386745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28320410894086712989591163 42480616341130069484386745)
        ·
          refine ⟨31860462255847552113290059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42480616341130069484386745 31860462255847552113290059)
          ·
            refine ⟨47790693383771328169935089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31860462255847552113290059 47790693383771328169935089)
            ·
              refine ⟨35843020037828496127451317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47790693383771328169935089 35843020037828496127451317)
              ·
                refine ⟨3360283128546421511948561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35843020037828496127451317 3360283128546421511948561)
                ·
                  refine ⟨2520212346409816133961421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3360283128546421511948561 2520212346409816133961421)
                  ·
                    refine ⟨945079629903681050235533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520212346409816133961421 945079629903681050235533)
                    ·
                      rfl

theorem cell22_2760804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2760804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760804 prefixEnd_2760804 := by exact prefixLift 2760804
  have htrace : WordTrace (prefixWord ++ tailWord_2760804) baseStart_2760804 baseEnd_2760804 := by
    simpa [prefixWord, tailWord_2760804, baseEnd_2760804] using wordTrace_append hprefix tailTrace_2760804
  have hstable : (prefixWord ++ tailWord_2760804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760804).length < 2 ^ (prefixWord ++ tailWord_2760804).sum := by decide
  have hdescent : baseEnd_2760804 < baseStart_2760804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760855 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 2, 3]
def baseStart_2760855 : Nat := 118140960795 + 2760855 * 2 ^ 59
def prefixEnd_2760855 : Nat := 4983230072969 + 3 ^ 40 * 2760855 * 2
def baseEnd_2760855 : Nat := 945097088245933917210377

theorem tailTrace_2760855 : CollatzResearch.WordTrace tailWord_2760855 prefixEnd_2760855 945097088245933917210377 := by
  unfold tailWord_2760855
  simp only [CollatzResearch.WordTrace]
  refine ⟨100696654412901326339764019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67131102941934217559842679 100696654412901326339764019)
  ·
    refine ⟨151044981619351989509646029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100696654412901326339764019 151044981619351989509646029)
    ·
      refine ⟨56641868107256996066117261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151044981619351989509646029 56641868107256996066117261)
      ·
        refine ⟨21240700540221373524793973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56641868107256996066117261 21240700540221373524793973)
        ·
          refine ⟨1991315675645753767949435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21240700540221373524793973 1991315675645753767949435)
          ·
            refine ⟨2986973513468630651924153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991315675645753767949435 2986973513468630651924153)
            ·
              refine ⟨2240230135101472988943115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986973513468630651924153 2240230135101472988943115)
              ·
                refine ⟨3360345202652209483414673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240230135101472988943115 3360345202652209483414673)
                ·
                  refine ⟨2520258901989157112561005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3360345202652209483414673 2520258901989157112561005)
                  ·
                    refine ⟨945097088245933917210377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520258901989157112561005 945097088245933917210377)
                    ·
                      rfl

theorem cell22_2760855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_2760855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760855 prefixEnd_2760855 := by exact prefixLift 2760855
  have htrace : WordTrace (prefixWord ++ tailWord_2760855) baseStart_2760855 baseEnd_2760855 := by
    simpa [prefixWord, tailWord_2760855, baseEnd_2760855] using wordTrace_append hprefix tailTrace_2760855
  have hstable : (prefixWord ++ tailWord_2760855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760855).length < 2 ^ (prefixWord ++ tailWord_2760855).sum := by decide
  have hdescent : baseEnd_2760855 < baseStart_2760855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760900 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2760900 : Nat := 118140960795 + 2760900 * 2 ^ 59
def prefixEnd_2760900 : Nat := 4983230072969 + 3 ^ 40 * 2760900 * 2
def baseEnd_2760900 : Nat := 945112492665568799835239

theorem tailTrace_2760900 : CollatzResearch.WordTrace tailWord_2760900 prefixEnd_2760900 945112492665568799835239 := by
  unfold tailWord_2760900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50349147848869149512576077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67132197131825532683434769 50349147848869149512576077)
  ·
    refine ⟨18880930443325931067216029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50349147848869149512576077 18880930443325931067216029)
    ·
      refine ⟨7080348916247224150206011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18880930443325931067216029 7080348916247224150206011)
      ·
        refine ⟨10620523374370836225309017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080348916247224150206011 10620523374370836225309017)
        ·
          refine ⟨7965392530778127168981763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10620523374370836225309017 7965392530778127168981763)
          ·
            refine ⟨11948088796167190753472645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965392530778127168981763 11948088796167190753472645)
            ·
              refine ⟨2240266649281348266276121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11948088796167190753472645 2240266649281348266276121)
              ·
                refine ⟨1680199986961011199707091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2240266649281348266276121 1680199986961011199707091)
                ·
                  refine ⟨2520299980441516799560637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680199986961011199707091 2520299980441516799560637)
                  ·
                    refine ⟨945112492665568799835239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520299980441516799560637 945112492665568799835239)
                    ·
                      rfl

theorem cell22_2760900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2760900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760900 prefixEnd_2760900 := by exact prefixLift 2760900
  have htrace : WordTrace (prefixWord ++ tailWord_2760900) baseStart_2760900 baseEnd_2760900 := by
    simpa [prefixWord, tailWord_2760900, baseEnd_2760900] using wordTrace_append hprefix tailTrace_2760900
  have hstable : (prefixWord ++ tailWord_2760900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760900).length < 2 ^ (prefixWord ++ tailWord_2760900).sum := by decide
  have hdescent : baseEnd_2760900 < baseStart_2760900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760907 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 6]
def baseStart_2760907 : Nat := 118140960795 + 2760907 * 2 ^ 59
def prefixEnd_2760907 : Nat := 4983230072969 + 3 ^ 40 * 2760907 * 2
def baseEnd_2760907 : Nat := 315038296302874371636739

theorem tailTrace_2760907 : CollatzResearch.WordTrace tailWord_2760907 prefixEnd_2760907 315038296302874371636739 := by
  unfold tailWord_2760907
  simp only [CollatzResearch.WordTrace]
  refine ⟨100698551008712939220656975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67132367339141959480437983 100698551008712939220656975)
  ·
    refine ⟨151047826513069408830985463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100698551008712939220656975 151047826513069408830985463)
    ·
      refine ⟨226571739769604113246478195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151047826513069408830985463 226571739769604113246478195)
      ·
        refine ⟨339857609654406169869717293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226571739769604113246478195 339857609654406169869717293)
        ·
          refine ⟨127446603620402313701143985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339857609654406169869717293 127446603620402313701143985)
          ·
            refine ⟨95584952715301735275857989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127446603620402313701143985 95584952715301735275857989)
            ·
              refine ⟨17922178634119075364223373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95584952715301735275857989 17922178634119075364223373)
              ·
                refine ⟨6720816987794653261583765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17922178634119075364223373 6720816987794653261583765)
                ·
                  refine ⟨315038296302874371636739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6720816987794653261583765 315038296302874371636739)
                  ·
                    rfl

theorem cell22_2760907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_2760907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760907 prefixEnd_2760907 := by exact prefixLift 2760907
  have htrace : WordTrace (prefixWord ++ tailWord_2760907) baseStart_2760907 baseEnd_2760907 := by
    simpa [prefixWord, tailWord_2760907, baseEnd_2760907] using wordTrace_append hprefix tailTrace_2760907
  have hstable : (prefixWord ++ tailWord_2760907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760907).length < 2 ^ (prefixWord ++ tailWord_2760907).sum := by decide
  have hdescent : baseEnd_2760907 < baseStart_2760907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760937 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2760937 : Nat := 118140960795 + 2760937 * 2 ^ 59
def prefixEnd_2760937 : Nat := 4983230072969 + 3 ^ 40 * 2760937 * 2
def baseEnd_2760937 : Nat := 945125158521713036660125

theorem tailTrace_2760937 : CollatzResearch.WordTrace tailWord_2760937 prefixEnd_2760937 945125158521713036660125 := by
  unfold tailWord_2760937
  simp only [CollatzResearch.WordTrace]
  refine ⟨100699645198604254344249065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67133096799069502896166043 100699645198604254344249065)
  ·
    refine ⟨75524733898953190758186799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100699645198604254344249065 75524733898953190758186799)
    ·
      refine ⟨113287100848429786137280199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75524733898953190758186799 113287100848429786137280199)
      ·
        refine ⟨169930651272644679205920299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113287100848429786137280199 169930651272644679205920299)
        ·
          refine ⟨254895976908967018808880449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169930651272644679205920299 254895976908967018808880449)
          ·
            refine ⟨191171982681725264106660337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254895976908967018808880449 191171982681725264106660337)
            ·
              refine ⟨143378987011293948079995253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191171982681725264106660337 143378987011293948079995253)
              ·
                refine ⟨13441780032308807632499555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143378987011293948079995253 13441780032308807632499555)
                ·
                  refine ⟨20162670048463211448749333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13441780032308807632499555 20162670048463211448749333)
                  ·
                    refine ⟨945125158521713036660125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20162670048463211448749333 945125158521713036660125)
                    ·
                      rfl

theorem cell22_2760937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2760937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760937 prefixEnd_2760937 := by exact prefixLift 2760937
  have htrace : WordTrace (prefixWord ++ tailWord_2760937) baseStart_2760937 baseEnd_2760937 := by
    simpa [prefixWord, tailWord_2760937, baseEnd_2760937] using wordTrace_append hprefix tailTrace_2760937
  have hstable : (prefixWord ++ tailWord_2760937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760937).length < 2 ^ (prefixWord ++ tailWord_2760937).sum := by decide
  have hdescent : baseEnd_2760937 < baseStart_2760937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760939 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 4, 3]
def baseStart_2760939 : Nat := 118140960795 + 2760939 * 2 ^ 59
def prefixEnd_2760939 : Nat := 4983230072969 + 3 ^ 40 * 2760939 * 2
def baseEnd_2760939 : Nat := 945125843162585698110119

theorem tailTrace_2760939 : CollatzResearch.WordTrace tailWord_2760939 prefixEnd_2760939 945125843162585698110119 := by
  unfold tailWord_2760939
  simp only [CollatzResearch.WordTrace]
  refine ⟨100699718144597008685821871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67133145429731339123881247 100699718144597008685821871)
  ·
    refine ⟨151049577216895513028732807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100699718144597008685821871 151049577216895513028732807)
    ·
      refine ⟨226574365825343269543099211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151049577216895513028732807 226574365825343269543099211)
      ·
        refine ⟨339861548738014904314648817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226574365825343269543099211 339861548738014904314648817)
        ·
          refine ⟨254896161553511178235986613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339861548738014904314648817 254896161553511178235986613)
          ·
            refine ⟨23896515145641672959623745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 254896161553511178235986613 23896515145641672959623745)
            ·
              refine ⟨17922386359231254719717809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23896515145641672959623745 17922386359231254719717809)
              ·
                refine ⟨13441789769423441039788357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17922386359231254719717809 13441789769423441039788357)
                ·
                  refine ⟨2520335581766895194960317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13441789769423441039788357 2520335581766895194960317)
                  ·
                    refine ⟨945125843162585698110119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520335581766895194960317 945125843162585698110119)
                    ·
                      rfl

theorem cell22_2760939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].length) (baseStart_2760939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760939 prefixEnd_2760939 := by exact prefixLift 2760939
  have htrace : WordTrace (prefixWord ++ tailWord_2760939) baseStart_2760939 baseEnd_2760939 := by
    simpa [prefixWord, tailWord_2760939, baseEnd_2760939] using wordTrace_append hprefix tailTrace_2760939
  have hstable : (prefixWord ++ tailWord_2760939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760939).length < 2 ^ (prefixWord ++ tailWord_2760939).sum := by decide
  have hdescent : baseEnd_2760939 < baseStart_2760939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760943 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 1, 4]
def baseStart_2760943 : Nat := 118140960795 + 2760943 * 2 ^ 59
def prefixEnd_2760943 : Nat := 4983230072969 + 3 ^ 40 * 2760943 * 2
def baseEnd_2760943 : Nat := 945127212444331021010107

theorem tailTrace_2760943 : CollatzResearch.WordTrace tailWord_2760943 prefixEnd_2760943 945127212444331021010107 := by
  unfold tailWord_2760943
  simp only [CollatzResearch.WordTrace]
  refine ⟨100699864036582517368967483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67133242691055011579311655 100699864036582517368967483)
  ·
    refine ⟨151049796054873776053451225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100699864036582517368967483 151049796054873776053451225)
    ·
      refine ⟨113287347041155332040088419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151049796054873776053451225 113287347041155332040088419)
      ·
        refine ⟨169931020561732998060132629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113287347041155332040088419 169931020561732998060132629)
        ·
          refine ⟨7965516588831234284068717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169931020561732998060132629 7965516588831234284068717)
          ·
            refine ⟨2987068720811712856525769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7965516588831234284068717 2987068720811712856525769)
            ·
              refine ⟨2240301540608784642394327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987068720811712856525769 2240301540608784642394327)
              ·
                refine ⟨3360452310913176963591491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240301540608784642394327 3360452310913176963591491)
                ·
                  refine ⟨5040678466369765445387237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360452310913176963591491 5040678466369765445387237)
                  ·
                    refine ⟨945127212444331021010107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040678466369765445387237 945127212444331021010107)
                    ·
                      rfl

theorem cell22_2760943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 4].length) (baseStart_2760943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760943 prefixEnd_2760943 := by exact prefixLift 2760943
  have htrace : WordTrace (prefixWord ++ tailWord_2760943) baseStart_2760943 baseEnd_2760943 := by
    simpa [prefixWord, tailWord_2760943, baseEnd_2760943] using wordTrace_append hprefix tailTrace_2760943
  have hstable : (prefixWord ++ tailWord_2760943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760943).length < 2 ^ (prefixWord ++ tailWord_2760943).sum := by decide
  have hdescent : baseEnd_2760943 < baseStart_2760943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2760956 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_2760956 : Nat := 118140960795 + 2760956 * 2 ^ 59
def prefixEnd_2760956 : Nat := 4983230072969 + 3 ^ 40 * 2760956 * 2
def baseEnd_2760956 : Nat := 945131662610003320435067

theorem tailTrace_2760956 : CollatzResearch.WordTrace tailWord_2760956 prefixEnd_2760956 945131662610003320435067 := by
  unfold tailWord_2760956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50350169092767710294595361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67133558790356947059460481 50350169092767710294595361)
  ·
    refine ⟨37762626819575782720946521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50350169092767710294595361 37762626819575782720946521)
    ·
      refine ⟨28321970114681837040709891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37762626819575782720946521 28321970114681837040709891)
      ·
        refine ⟨42482955172022755561064837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28321970114681837040709891 42482955172022755561064837)
        ·
          refine ⟨7965554094754266667699657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42482955172022755561064837 7965554094754266667699657)
          ·
            refine ⟨5974165571065700000774743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7965554094754266667699657 5974165571065700000774743)
            ·
              refine ⟨8961248356598550001162115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974165571065700000774743 8961248356598550001162115)
              ·
                refine ⟨13441872534897825001743173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961248356598550001162115 13441872534897825001743173)
                ·
                  refine ⟨2520351100293342187826845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13441872534897825001743173 2520351100293342187826845)
                  ·
                    refine ⟨945131662610003320435067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520351100293342187826845 945131662610003320435067)
                    ·
                      rfl

theorem cell22_2760956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_2760956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2760956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2760956 prefixEnd_2760956 := by exact prefixLift 2760956
  have htrace : WordTrace (prefixWord ++ tailWord_2760956) baseStart_2760956 baseEnd_2760956 := by
    simpa [prefixWord, tailWord_2760956, baseEnd_2760956] using wordTrace_append hprefix tailTrace_2760956
  have hstable : (prefixWord ++ tailWord_2760956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2760956).length < 2 ^ (prefixWord ++ tailWord_2760956).sum := by decide
  have hdescent : baseEnd_2760956 < baseStart_2760956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2760956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761018 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_2761018 : Nat := 118140960795 + 2761018 * 2 ^ 59
def prefixEnd_2761018 : Nat := 4983230072969 + 3 ^ 40 * 2761018 * 2
def baseEnd_2761018 : Nat := 945152886477055825384877

theorem tailTrace_2761018 : CollatzResearch.WordTrace tailWord_2761018 prefixEnd_2761018 945152886477055825384877 := by
  unfold tailWord_2761018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25175649877827701294486927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67135066340873870118631805 25175649877827701294486927)
  ·
    refine ⟨37763474816741551941730391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25175649877827701294486927 37763474816741551941730391)
    ·
      refine ⟨56645212225112327912595587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37763474816741551941730391 56645212225112327912595587)
      ·
        refine ⟨84967818337668491868893381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56645212225112327912595587 84967818337668491868893381)
        ·
          refine ⟨15931465938312842225417509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84967818337668491868893381 15931465938312842225417509)
          ·
            refine ⟨2987149863433657917265783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15931465938312842225417509 2987149863433657917265783)
            ·
              refine ⟨4480724795150486875898675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987149863433657917265783 4480724795150486875898675)
              ·
                refine ⟨6721087192725730313848013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480724795150486875898675 6721087192725730313848013)
                ·
                  refine ⟨2520407697272148867693005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6721087192725730313848013 2520407697272148867693005)
                  ·
                    refine ⟨945152886477055825384877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520407697272148867693005 945152886477055825384877)
                    ·
                      rfl

theorem cell22_2761018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_2761018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761018 prefixEnd_2761018 := by exact prefixLift 2761018
  have htrace : WordTrace (prefixWord ++ tailWord_2761018) baseStart_2761018 baseEnd_2761018 := by
    simpa [prefixWord, tailWord_2761018, baseEnd_2761018] using wordTrace_append hprefix tailTrace_2761018
  have hstable : (prefixWord ++ tailWord_2761018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761018).length < 2 ^ (prefixWord ++ tailWord_2761018).sum := by decide
  have hdescent : baseEnd_2761018 < baseStart_2761018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761187 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 3, 3]
def baseStart_2761187 : Nat := 118140960795 + 2761187 * 2 ^ 59
def prefixEnd_2761187 : Nat := 4983230072969 + 3 ^ 40 * 2761187 * 2
def baseEnd_2761187 : Nat := 945210738630795717909359

theorem tailTrace_2761187 : CollatzResearch.WordTrace tailWord_2761187 prefixEnd_2761187 945210738630795717909359 := by
  unfold tailWord_2761187
  simp only [CollatzResearch.WordTrace]
  refine ⟨100708763447698547040849815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67139175631799031360566543 100708763447698547040849815)
  ·
    refine ⟨151063145171547820561274723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100708763447698547040849815 151063145171547820561274723)
    ·
      refine ⟨226594717757321730841912085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151063145171547820561274723 226594717757321730841912085)
      ·
        refine ⟨10621627394874456133214629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226594717757321730841912085 10621627394874456133214629)
        ·
          refine ⟨1991555136538960524977743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10621627394874456133214629 1991555136538960524977743)
          ·
            refine ⟨2987332704808440787466615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991555136538960524977743 2987332704808440787466615)
            ·
              refine ⟨4480999057212661181199923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987332704808440787466615 4480999057212661181199923)
              ·
                refine ⟨6721498585818991771799885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480999057212661181199923 6721498585818991771799885)
                ·
                  refine ⟨2520561969682121914424957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6721498585818991771799885 2520561969682121914424957)
                  ·
                    refine ⟨945210738630795717909359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520561969682121914424957 945210738630795717909359)
                    ·
                      rfl

theorem cell22_2761187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 3].length) (baseStart_2761187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761187 prefixEnd_2761187 := by exact prefixLift 2761187
  have htrace : WordTrace (prefixWord ++ tailWord_2761187) baseStart_2761187 baseEnd_2761187 := by
    simpa [prefixWord, tailWord_2761187, baseEnd_2761187] using wordTrace_append hprefix tailTrace_2761187
  have hstable : (prefixWord ++ tailWord_2761187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761187).length < 2 ^ (prefixWord ++ tailWord_2761187).sum := by decide
  have hdescent : baseEnd_2761187 < baseStart_2761187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761196 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_2761196 : Nat := 118140960795 + 2761196 * 2 ^ 59
def prefixEnd_2761196 : Nat := 4983230072969 + 3 ^ 40 * 2761196 * 2
def baseEnd_2761196 : Nat := 945213819514722694434331

theorem tailTrace_2761196 : CollatzResearch.WordTrace tailWord_2761196 prefixEnd_2761196 945213819514722694434331 := by
  unfold tailWord_2761196
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354545852332970788963721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67139394469777294385284961 50354545852332970788963721)
  ·
    refine ⟨37765909389249728091722791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50354545852332970788963721 37765909389249728091722791)
    ·
      refine ⟨56648864083874592137584187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37765909389249728091722791 56648864083874592137584187)
      ·
        refine ⟨84973296125811888206376281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56648864083874592137584187 84973296125811888206376281)
        ·
          refine ⟨63729972094358916154782211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84973296125811888206376281 63729972094358916154782211)
          ·
            refine ⟨95594958141538374232173317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63729972094358916154782211 95594958141538374232173317)
            ·
              refine ⟨17924054651538445168532497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95594958141538374232173317 17924054651538445168532497)
              ·
                refine ⟨13443040988653833876399373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17924054651538445168532497 13443040988653833876399373)
                ·
                  refine ⟨5041140370745187703649765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13443040988653833876399373 5041140370745187703649765)
                  ·
                    refine ⟨945213819514722694434331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041140370745187703649765 945213819514722694434331)
                    ·
                      rfl

theorem cell22_2761196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_2761196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761196 prefixEnd_2761196 := by exact prefixLift 2761196
  have htrace : WordTrace (prefixWord ++ tailWord_2761196) baseStart_2761196 baseEnd_2761196 := by
    simpa [prefixWord, tailWord_2761196, baseEnd_2761196] using wordTrace_append hprefix tailTrace_2761196
  have hstable : (prefixWord ++ tailWord_2761196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761196).length < 2 ^ (prefixWord ++ tailWord_2761196).sum := by decide
  have hdescent : baseEnd_2761196 < baseStart_2761196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761245 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2761245 : Nat := 118140960795 + 2761245 * 2 ^ 59
def prefixEnd_2761245 : Nat := 4983230072969 + 3 ^ 40 * 2761245 * 2
def baseEnd_2761245 : Nat := 315076864405367633319727

theorem tailTrace_2761245 : CollatzResearch.WordTrace tailWord_2761245 prefixEnd_2761245 315076864405367633319727 := by
  unfold tailWord_2761245
  simp only [CollatzResearch.WordTrace]
  refine ⟨100710878881488422946461189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67140585920992281964307459 100710878881488422946461189)
  ·
    refine ⟨18883289790279079302461473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100710878881488422946461189 18883289790279079302461473)
    ·
      refine ⟨14162467342709309476846105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18883289790279079302461473 14162467342709309476846105)
      ·
        refine ⟨10621850507031982107634579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14162467342709309476846105 10621850507031982107634579)
        ·
          refine ⟨15932775760547973161451869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10621850507031982107634579 15932775760547973161451869)
          ·
            refine ⟨5974790910205489935544451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15932775760547973161451869 5974790910205489935544451)
            ·
              refine ⟨8962186365308234903316677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974790910205489935544451 8962186365308234903316677)
              ·
                refine ⟨1680409943495294044371877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8962186365308234903316677 1680409943495294044371877)
                ·
                  refine ⟨315076864405367633319727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680409943495294044371877 315076864405367633319727)
                  ·
                    rfl

theorem cell22_2761245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2761245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761245 prefixEnd_2761245 := by exact prefixLift 2761245
  have htrace : WordTrace (prefixWord ++ tailWord_2761245) baseStart_2761245 baseEnd_2761245 := by
    simpa [prefixWord, tailWord_2761245, baseEnd_2761245] using wordTrace_append hprefix tailTrace_2761245
  have hstable : (prefixWord ++ tailWord_2761245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761245).length < 2 ^ (prefixWord ++ tailWord_2761245).sum := by decide
  have hdescent : baseEnd_2761245 < baseStart_2761245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761273 : List Nat := [1, 2, 1, 5, 1, 1, 5, 6]
def baseStart_2761273 : Nat := 118140960795 + 2761273 * 2 ^ 59
def prefixEnd_2761273 : Nat := 4983230072969 + 3 ^ 40 * 2761273 * 2
def baseEnd_2761273 : Nat := 105026686465368906695455

theorem tailTrace_2761273 : CollatzResearch.WordTrace tailWord_2761273 prefixEnd_2761273 105026686465368906695455 := by
  unfold tailWord_2761273
  simp only [CollatzResearch.WordTrace]
  refine ⟨100711900125386983728480473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67141266750257989152320315 100711900125386983728480473)
  ·
    refine ⟨75533925094040237796360355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100711900125386983728480473 75533925094040237796360355)
    ·
      refine ⟨113300887641060356694540533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75533925094040237796360355 113300887641060356694540533)
      ·
        refine ⟨10621958216349408440113175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113300887641060356694540533 10621958216349408440113175)
        ·
          refine ⟨15932937324524112660169763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10621958216349408440113175 15932937324524112660169763)
          ·
            refine ⟨23899405986786168990254645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15932937324524112660169763 23899405986786168990254645)
            ·
              refine ⟨2240569311261203342836373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23899405986786168990254645 2240569311261203342836373)
              ·
                refine ⟨105026686465368906695455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2240569311261203342836373 105026686465368906695455)
                ·
                  rfl

theorem cell22_2761273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 6].length) (baseStart_2761273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761273 prefixEnd_2761273 := by exact prefixLift 2761273
  have htrace : WordTrace (prefixWord ++ tailWord_2761273) baseStart_2761273 baseEnd_2761273 := by
    simpa [prefixWord, tailWord_2761273, baseEnd_2761273] using wordTrace_append hprefix tailTrace_2761273
  have hstable : (prefixWord ++ tailWord_2761273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761273).length < 2 ^ (prefixWord ++ tailWord_2761273).sum := by decide
  have hdescent : baseEnd_2761273 < baseStart_2761273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761412 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2761412 : Nat := 118140960795 + 2761412 * 2 ^ 59
def prefixEnd_2761412 : Nat := 4983230072969 + 3 ^ 40 * 2761412 * 2
def baseEnd_2761412 : Nat := 945287760728970131033669

theorem tailTrace_2761412 : CollatzResearch.WordTrace tailWord_2761412 prefixEnd_2761412 945287760728970131033669 := by
  unfold tailWord_2761412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50358484935941705233895245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67144646581255606978526993 50358484935941705233895245)
  ·
    refine ⟨18884431850978139462710717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50358484935941705233895245 18884431850978139462710717)
    ·
      refine ⟨7081661944116802298516519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18884431850978139462710717 7081661944116802298516519)
      ·
        refine ⟨10622492916175203447774779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081661944116802298516519 10622492916175203447774779)
        ·
          refine ⟨15933739374262805171662169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10622492916175203447774779 15933739374262805171662169)
          ·
            refine ⟨11950304530697103878746627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15933739374262805171662169 11950304530697103878746627)
            ·
              refine ⟨17925456796045655818119941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11950304530697103878746627 17925456796045655818119941)
              ·
                refine ⟨3361023149258560465897489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17925456796045655818119941 3361023149258560465897489)
                ·
                  refine ⟨2520767361943920349423117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361023149258560465897489 2520767361943920349423117)
                  ·
                    refine ⟨945287760728970131033669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520767361943920349423117 945287760728970131033669)
                    ·
                      rfl

theorem cell22_2761412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2761412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761412 prefixEnd_2761412 := by exact prefixLift 2761412
  have htrace : WordTrace (prefixWord ++ tailWord_2761412) baseStart_2761412 baseEnd_2761412 := by
    simpa [prefixWord, tailWord_2761412, baseEnd_2761412] using wordTrace_append hprefix tailTrace_2761412
  have hstable : (prefixWord ++ tailWord_2761412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761412).length < 2 ^ (prefixWord ++ tailWord_2761412).sum := by decide
  have hdescent : baseEnd_2761412 < baseStart_2761412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761474 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2761474 : Nat := 118140960795 + 2761474 * 2 ^ 59
def prefixEnd_2761474 : Nat := 4983230072969 + 3 ^ 40 * 2761474 * 2
def baseEnd_2761474 : Nat := 945308984596022635983479

theorem tailTrace_2761474 : CollatzResearch.WordTrace tailWord_2761474 prefixEnd_2761474 945308984596022635983479 := by
  unfold tailWord_2761474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179807799414698764136869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67146154131772530037698317 25179807799414698764136869)
  ·
    refine ⟨4721213962390256018275663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25179807799414698764136869 4721213962390256018275663)
    ·
      refine ⟨7081820943585384027413495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721213962390256018275663 7081820943585384027413495)
      ·
        refine ⟨10622731415378076041120243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081820943585384027413495 10622731415378076041120243)
        ·
          refine ⟨15934097123067114061680365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10622731415378076041120243 15934097123067114061680365)
          ·
            refine ⟨5975286421150167773130137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15934097123067114061680365 5975286421150167773130137)
            ·
              refine ⟨4481464815862625829847603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975286421150167773130137 4481464815862625829847603)
              ·
                refine ⟨6722197223793938744771405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481464815862625829847603 6722197223793938744771405)
                ·
                  refine ⟨2520823958922727029289277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6722197223793938744771405 2520823958922727029289277)
                  ·
                    refine ⟨945308984596022635983479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520823958922727029289277 945308984596022635983479)
                    ·
                      rfl

theorem cell22_2761474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2761474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761474 prefixEnd_2761474 := by exact prefixLift 2761474
  have htrace : WordTrace (prefixWord ++ tailWord_2761474) baseStart_2761474 baseEnd_2761474 := by
    simpa [prefixWord, tailWord_2761474, baseEnd_2761474] using wordTrace_append hprefix tailTrace_2761474
  have hstable : (prefixWord ++ tailWord_2761474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761474).length < 2 ^ (prefixWord ++ tailWord_2761474).sum := by decide
  have hdescent : baseEnd_2761474 < baseStart_2761474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761508 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2761508 : Nat := 118140960795 + 2761508 * 2 ^ 59
def prefixEnd_2761508 : Nat := 4983230072969 + 3 ^ 40 * 2761508 * 2
def baseEnd_2761508 : Nat := 945320623490857880633375

theorem tailTrace_2761508 : CollatzResearch.WordTrace tailWord_2761508 prefixEnd_2761508 945320623490857880633375 := by
  unfold tailWord_2761508
  simp only [CollatzResearch.WordTrace]
  refine ⟨50360235639767809431642589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67146980853023745908856785 50360235639767809431642589)
  ·
    refine ⟨18885088364912928536865971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50360235639767809431642589 18885088364912928536865971)
    ·
      refine ⟨28327632547369392805298957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18885088364912928536865971 28327632547369392805298957)
      ·
        refine ⟨10622862205263522301987109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28327632547369392805298957 10622862205263522301987109)
        ·
          refine ⟨1991786663486910431622583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10622862205263522301987109 1991786663486910431622583)
          ·
            refine ⟨2987679995230365647433875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991786663486910431622583 2987679995230365647433875)
            ·
              refine ⟨4481519992845548471150813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987679995230365647433875 4481519992845548471150813)
              ·
                refine ⟨1680569997317080676681555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4481519992845548471150813 1680569997317080676681555)
                ·
                  refine ⟨2520854995975621015022333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680569997317080676681555 2520854995975621015022333)
                  ·
                    refine ⟨945320623490857880633375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2520854995975621015022333 945320623490857880633375)
                    ·
                      rfl

theorem cell22_2761508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2761508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761508 prefixEnd_2761508 := by exact prefixLift 2761508
  have htrace : WordTrace (prefixWord ++ tailWord_2761508) baseStart_2761508 baseEnd_2761508 := by
    simpa [prefixWord, tailWord_2761508, baseEnd_2761508] using wordTrace_append hprefix tailTrace_2761508
  have hstable : (prefixWord ++ tailWord_2761508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761508).length < 2 ^ (prefixWord ++ tailWord_2761508).sum := by decide
  have hdescent : baseEnd_2761508 < baseStart_2761508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761562 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_2761562 : Nat := 118140960795 + 2761562 * 2 ^ 59
def prefixEnd_2761562 : Nat := 4983230072969 + 3 ^ 40 * 2761562 * 2
def baseEnd_2761562 : Nat := 945339108794419739783209

theorem tailTrace_2761562 : CollatzResearch.WordTrace tailWord_2761562 prefixEnd_2761562 945339108794419739783209 := by
  unfold tailWord_2761562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25180610205334996521437735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67148293880893324057167293 25180610205334996521437735)
  ·
    refine ⟨37770915308002494782156603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25180610205334996521437735 37770915308002494782156603)
    ·
      refine ⟨56656372962003742173234905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37770915308002494782156603 56656372962003742173234905)
      ·
        refine ⟨42492279721502806629926179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56656372962003742173234905 42492279721502806629926179)
        ·
          refine ⟨63738419582254209944889269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42492279721502806629926179 63738419582254209944889269)
          ·
            refine ⟨5975476835836332182333369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63738419582254209944889269 5975476835836332182333369)
            ·
              refine ⟨4481607626877249136750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975476835836332182333369 4481607626877249136750027)
              ·
                refine ⟨6722411440315873705125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481607626877249136750027 6722411440315873705125041)
                ·
                  refine ⟨5041808580236905278843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6722411440315873705125041 5041808580236905278843781)
                  ·
                    refine ⟨945339108794419739783209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041808580236905278843781 945339108794419739783209)
                    ·
                      rfl

theorem cell22_2761562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_2761562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761562 prefixEnd_2761562 := by exact prefixLift 2761562
  have htrace : WordTrace (prefixWord ++ tailWord_2761562) baseStart_2761562 baseEnd_2761562 := by
    simpa [prefixWord, tailWord_2761562, baseEnd_2761562] using wordTrace_append hprefix tailTrace_2761562
  have hstable : (prefixWord ++ tailWord_2761562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761562).length < 2 ^ (prefixWord ++ tailWord_2761562).sum := by decide
  have hdescent : baseEnd_2761562 < baseStart_2761562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761686 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2761686 : Nat := 118140960795 + 2761686 * 2 ^ 59
def prefixEnd_2761686 : Nat := 4983230072969 + 3 ^ 40 * 2761686 * 2
def baseEnd_2761686 : Nat := 945381556528524749682829

theorem tailTrace_2761686 : CollatzResearch.WordTrace tailWord_2761686 prefixEnd_2761686 945381556528524749682829 := by
  unfold tailWord_2761686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295435217055672203954057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67151308981927170175509941 6295435217055672203954057)
  ·
    refine ⟨4721576412791754152965543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6295435217055672203954057 4721576412791754152965543)
    ·
      refine ⟨7082364619187631229448315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4721576412791754152965543 7082364619187631229448315)
      ·
        refine ⟨10623546928781446844172473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7082364619187631229448315 10623546928781446844172473)
        ·
          refine ⟨7967660196586085133129355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10623546928781446844172473 7967660196586085133129355)
          ·
            refine ⟨11951490294879127699694033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7967660196586085133129355 11951490294879127699694033)
            ·
              refine ⟨8963617721159345774770525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11951490294879127699694033 8963617721159345774770525)
              ·
                refine ⟨3361356645434754665538947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8963617721159345774770525 3361356645434754665538947)
                ·
                  refine ⟨5042034968152131998308421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361356645434754665538947 5042034968152131998308421)
                  ·
                    refine ⟨945381556528524749682829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5042034968152131998308421 945381556528524749682829)
                    ·
                      rfl

theorem cell22_2761686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2761686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761686 prefixEnd_2761686 := by exact prefixLift 2761686
  have htrace : WordTrace (prefixWord ++ tailWord_2761686) baseStart_2761686 baseEnd_2761686 := by
    simpa [prefixWord, tailWord_2761686, baseEnd_2761686] using wordTrace_append hprefix tailTrace_2761686
  have hstable : (prefixWord ++ tailWord_2761686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761686).length < 2 ^ (prefixWord ++ tailWord_2761686).sum := by decide
  have hdescent : baseEnd_2761686 < baseStart_2761686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761699 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 2, 3]
def baseStart_2761699 : Nat := 118140960795 + 2761699 * 2 ^ 59
def prefixEnd_2761699 : Nat := 4983230072969 + 3 ^ 40 * 2761699 * 2
def baseEnd_2761699 : Nat := 945386006694197049107789

theorem tailTrace_2761699 : CollatzResearch.WordTrace tailWord_2761699 prefixEnd_2761699 945386006694197049107789 := by
  unfold tailWord_2761699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100727437621843658483488151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67151625081229105655658767 100727437621843658483488151)
  ·
    refine ⟨151091156432765487725232227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100727437621843658483488151 151091156432765487725232227)
    ·
      refine ⟨226636734649148231587848341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151091156432765487725232227 226636734649148231587848341)
      ·
        refine ⟨10623596936678823355680391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226636734649148231587848341 10623596936678823355680391)
        ·
          refine ⟨15935395405018235033520587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10623596936678823355680391 15935395405018235033520587)
          ·
            refine ⟨23903093107527352550280881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15935395405018235033520587 23903093107527352550280881)
            ·
              refine ⟨17927319830645514412710661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23903093107527352550280881 17927319830645514412710661)
              ·
                refine ⟨3361372468246033952383249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17927319830645514412710661 3361372468246033952383249)
                ·
                  refine ⟨2521029351184525464287437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361372468246033952383249 2521029351184525464287437)
                  ·
                    refine ⟨945386006694197049107789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521029351184525464287437 945386006694197049107789)
                    ·
                      rfl

theorem cell22_2761699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].length) (baseStart_2761699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761699 prefixEnd_2761699 := by exact prefixLift 2761699
  have htrace : WordTrace (prefixWord ++ tailWord_2761699) baseStart_2761699 baseEnd_2761699 := by
    simpa [prefixWord, tailWord_2761699, baseEnd_2761699] using wordTrace_append hprefix tailTrace_2761699
  have hstable : (prefixWord ++ tailWord_2761699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761699).length < 2 ^ (prefixWord ++ tailWord_2761699).sum := by decide
  have hdescent : baseEnd_2761699 < baseStart_2761699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761701 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 6]
def baseStart_2761701 : Nat := 118140960795 + 2761701 * 2 ^ 59
def prefixEnd_2761701 : Nat := 4983230072969 + 3 ^ 40 * 2761701 * 2
def baseEnd_2761701 : Nat := 315128897111689903519261

theorem tailTrace_2761701 : CollatzResearch.WordTrace tailWord_2761701 prefixEnd_2761701 315128897111689903519261 := by
  unfold tailWord_2761701
  simp only [CollatzResearch.WordTrace]
  refine ⟨100727510567836412825060957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67151673711890941883373971 100727510567836412825060957)
  ·
    refine ⟨37772816462938654809397859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100727510567836412825060957 37772816462938654809397859)
    ·
      refine ⟨56659224694407982214096789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37772816462938654809397859 56659224694407982214096789)
      ·
        refine ⟨2655901157550374166285787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56659224694407982214096789 2655901157550374166285787)
        ·
          refine ⟨3983851736325561249428681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655901157550374166285787 3983851736325561249428681)
          ·
            refine ⟨2987888802244170937071511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983851736325561249428681 2987888802244170937071511)
            ·
              refine ⟨4481833203366256405607267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987888802244170937071511 4481833203366256405607267)
              ·
                refine ⟨6722749805049384608410901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481833203366256405607267 6722749805049384608410901)
                ·
                  refine ⟨315128897111689903519261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6722749805049384608410901 315128897111689903519261)
                  ·
                    rfl

theorem cell22_2761701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_2761701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761701 prefixEnd_2761701 := by exact prefixLift 2761701
  have htrace : WordTrace (prefixWord ++ tailWord_2761701) baseStart_2761701 baseEnd_2761701 := by
    simpa [prefixWord, tailWord_2761701, baseEnd_2761701] using wordTrace_append hprefix tailTrace_2761701
  have hstable : (prefixWord ++ tailWord_2761701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761701).length < 2 ^ (prefixWord ++ tailWord_2761701).sum := by decide
  have hdescent : baseEnd_2761701 < baseStart_2761701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761746 : List Nat := [3, 2, 5, 1, 1, 10]
def baseStart_2761746 : Nat := 118140960795 + 2761746 * 2 ^ 59
def prefixEnd_2761746 : Nat := 4983230072969 + 3 ^ 40 * 2761746 * 2
def baseEnd_2761746 : Nat := 11671630811786476459045

theorem tailTrace_2761746 : CollatzResearch.WordTrace tailWord_2761746 prefixEnd_2761746 11671630811786476459045 := by
  unfold tailWord_2761746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25182287963168346377612273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67152767901782257006966061 25182287963168346377612273)
  ·
    refine ⟨18886715972376259783209205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25182287963168346377612273 18886715972376259783209205)
    ·
      refine ⟨1770629622410274354675863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18886715972376259783209205 1770629622410274354675863)
      ·
        refine ⟨2655944433615411532013795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770629622410274354675863 2655944433615411532013795)
        ·
          refine ⟨3983916650423117298020693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655944433615411532013795 3983916650423117298020693)
          ·
            refine ⟨11671630811786476459045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3983916650423117298020693 11671630811786476459045)
            ·
              rfl

theorem cell22_2761746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 10].length) (baseStart_2761746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761746 prefixEnd_2761746 := by exact prefixLift 2761746
  have htrace : WordTrace (prefixWord ++ tailWord_2761746) baseStart_2761746 baseEnd_2761746 := by
    simpa [prefixWord, tailWord_2761746, baseEnd_2761746] using wordTrace_append hprefix tailTrace_2761746
  have hstable : (prefixWord ++ tailWord_2761746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761746).length < 2 ^ (prefixWord ++ tailWord_2761746).sum := by decide
  have hdescent : baseEnd_2761746 < baseStart_2761746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761772 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_2761772 : Nat := 118140960795 + 2761772 * 2 ^ 59
def prefixEnd_2761772 : Nat := 4983230072969 + 3 ^ 40 * 2761772 * 2
def baseEnd_2761772 : Nat := 945410996086049192032565

theorem tailTrace_2761772 : CollatzResearch.WordTrace tailWord_2761772 prefixEnd_2761772 945410996086049192032565 := by
  unfold tailWord_2761772
  simp only [CollatzResearch.WordTrace]
  refine ⟨50365050075289595975447785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67153400100386127967263713 50365050075289595975447785)
  ·
    refine ⟨37773787556467196981585839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50365050075289595975447785 37773787556467196981585839)
    ·
      refine ⟨56660681334700795472378759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37773787556467196981585839 56660681334700795472378759)
      ·
        refine ⟨84991022002051193208568139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56660681334700795472378759 84991022002051193208568139)
        ·
          refine ⟨127486533003076789812852209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84991022002051193208568139 127486533003076789812852209)
          ·
            refine ⟨95614899752307592359639157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127486533003076789812852209 95614899752307592359639157)
            ·
              refine ⟨8963896851778836783716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95614899752307592359639157 8963896851778836783716171)
              ·
                refine ⟨13445845277668255175574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963896851778836783716171 13445845277668255175574257)
                ·
                  refine ⟨10084383958251191381680693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13445845277668255175574257 10084383958251191381680693)
                  ·
                    refine ⟨945410996086049192032565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10084383958251191381680693 945410996086049192032565)
                    ·
                      rfl

theorem cell22_2761772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_2761772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761772 prefixEnd_2761772 := by exact prefixLift 2761772
  have htrace : WordTrace (prefixWord ++ tailWord_2761772) baseStart_2761772 baseEnd_2761772 := by
    simpa [prefixWord, tailWord_2761772, baseEnd_2761772] using wordTrace_append hprefix tailTrace_2761772
  have hstable : (prefixWord ++ tailWord_2761772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761772).length < 2 ^ (prefixWord ++ tailWord_2761772).sum := by decide
  have hdescent : baseEnd_2761772 < baseStart_2761772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761774 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_2761774 : Nat := 118140960795 + 2761774 * 2 ^ 59
def prefixEnd_2761774 : Nat := 4983230072969 + 3 ^ 40 * 2761774 * 2
def baseEnd_2761774 : Nat := 315137226908973951160853

theorem tailTrace_2761774 : CollatzResearch.WordTrace tailWord_2761774 prefixEnd_2761774 315137226908973951160853 := by
  unfold tailWord_2761774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591271637071493286558547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67153448731047964194978917 12591271637071493286558547)
  ·
    refine ⟨18886907455607239929837821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12591271637071493286558547 18886907455607239929837821)
    ·
      refine ⟨7082590295852714973689183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18886907455607239929837821 7082590295852714973689183)
      ·
        refine ⟨10623885443779072460533775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7082590295852714973689183 10623885443779072460533775)
        ·
          refine ⟨15935828165668608690800663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10623885443779072460533775 15935828165668608690800663)
          ·
            refine ⟨23903742248502913036200995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15935828165668608690800663 23903742248502913036200995)
            ·
              refine ⟨35855613372754369554301493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23903742248502913036200995 35855613372754369554301493)
              ·
                refine ⟨3361463753695722145715765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35855613372754369554301493 3361463753695722145715765)
                ·
                  refine ⟨315137226908973951160853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3361463753695722145715765 315137226908973951160853)
                  ·
                    rfl

theorem cell22_2761774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_2761774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761774 prefixEnd_2761774 := by exact prefixLift 2761774
  have htrace : WordTrace (prefixWord ++ tailWord_2761774) baseStart_2761774 baseEnd_2761774 := by
    simpa [prefixWord, tailWord_2761774, baseEnd_2761774] using wordTrace_append hprefix tailTrace_2761774
  have hstable : (prefixWord ++ tailWord_2761774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761774).length < 2 ^ (prefixWord ++ tailWord_2761774).sum := by decide
  have hdescent : baseEnd_2761774 < baseStart_2761774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761847 : List Nat := [1, 1, 3, 1, 1, 4, 3, 8]
def baseStart_2761847 : Nat := 118140960795 + 2761847 * 2 ^ 59
def prefixEnd_2761847 : Nat := 4983230072969 + 3 ^ 40 * 2761847 * 2
def baseEnd_2761847 : Nat := 105048518902085999600815

theorem tailTrace_2761847 : CollatzResearch.WordTrace tailWord_2761847 prefixEnd_2761847 105048518902085999600815 := by
  unfold tailWord_2761847
  simp only [CollatzResearch.WordTrace]
  refine ⟨100732835625307479759875795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67155223750204986506583863 100732835625307479759875795)
  ·
    refine ⟨151099253437961219639813693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100732835625307479759875795 151099253437961219639813693)
    ·
      refine ⟨56662220039235457364930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151099253437961219639813693 56662220039235457364930135)
      ·
        refine ⟨84993330058853186047395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56662220039235457364930135 84993330058853186047395203)
        ·
          refine ⟨127489995088279779071092805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84993330058853186047395203 127489995088279779071092805)
          ·
            refine ⟨23904374079052458575829901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127489995088279779071092805 23904374079052458575829901)
            ·
              refine ⟨8964140279644671965936213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23904374079052458575829901 8964140279644671965936213)
              ·
                refine ⟨105048518902085999600815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8964140279644671965936213 105048518902085999600815)
                ·
                  rfl

theorem cell22_2761847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 8].length) (baseStart_2761847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761847 prefixEnd_2761847 := by exact prefixLift 2761847
  have htrace : WordTrace (prefixWord ++ tailWord_2761847) baseStart_2761847 baseEnd_2761847 := by
    simpa [prefixWord, tailWord_2761847, baseEnd_2761847] using wordTrace_append hprefix tailTrace_2761847
  have hstable : (prefixWord ++ tailWord_2761847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761847).length < 2 ^ (prefixWord ++ tailWord_2761847).sum := by decide
  have hdescent : baseEnd_2761847 < baseStart_2761847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761930 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2761930 : Nat := 118140960795 + 2761930 * 2 ^ 59
def prefixEnd_2761930 : Nat := 4983230072969 + 3 ^ 40 * 2761930 * 2
def baseEnd_2761930 : Nat := 945465082714989446582081

theorem tailTrace_2761930 : CollatzResearch.WordTrace tailWord_2761930 prefixEnd_2761930 945465082714989446582081 := by
  unfold tailWord_2761930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183965721001696233786811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67157241922671189956764829 25183965721001696233786811)
  ·
    refine ⟨37775948581502544350680217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25183965721001696233786811 37775948581502544350680217)
    ·
      refine ⟨28331961436126908263010163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37775948581502544350680217 28331961436126908263010163)
      ·
        refine ⟨42497942154190362394515245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28331961436126908263010163 42497942154190362394515245)
        ·
          refine ⟨15936728307821385897943217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42497942154190362394515245 15936728307821385897943217)
          ·
            refine ⟨11952546230866039423457413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15936728307821385897943217 11952546230866039423457413)
            ·
              refine ⟨2241102418287382391898265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11952546230866039423457413 2241102418287382391898265)
              ·
                refine ⟨1680826813715536793923699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241102418287382391898265 1680826813715536793923699)
                ·
                  refine ⟨2521240220573305190885549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680826813715536793923699 2521240220573305190885549)
                  ·
                    refine ⟨945465082714989446582081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521240220573305190885549 945465082714989446582081)
                    ·
                      rfl

theorem cell22_2761930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2761930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761930 prefixEnd_2761930 := by exact prefixLift 2761930
  have htrace : WordTrace (prefixWord ++ tailWord_2761930) baseStart_2761930 baseEnd_2761930 := by
    simpa [prefixWord, tailWord_2761930, baseEnd_2761930] using wordTrace_append hprefix tailTrace_2761930
  have hstable : (prefixWord ++ tailWord_2761930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761930).length < 2 ^ (prefixWord ++ tailWord_2761930).sum := by decide
  have hdescent : baseEnd_2761930 < baseStart_2761930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761941 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2761941 : Nat := 118140960795 + 2761941 * 2 ^ 59
def prefixEnd_2761941 : Nat := 4983230072969 + 3 ^ 40 * 2761941 * 2
def baseEnd_2761941 : Nat := 945468848239789084557047

theorem tailTrace_2761941 : CollatzResearch.WordTrace tailWord_2761941 prefixEnd_2761941 945468848239789084557047 := by
  unfold tailWord_2761941
  simp only [CollatzResearch.WordTrace]
  refine ⟨100736264086966933813797677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67157509391311289209198451 100736264086966933813797677)
  ·
    refine ⟨37776099032612600180174129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100736264086966933813797677 37776099032612600180174129)
    ·
      refine ⟨28332074274459450135130597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37776099032612600180174129 28332074274459450135130597)
      ·
        refine ⟨5312263926461146900336987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28332074274459450135130597 5312263926461146900336987)
        ·
          refine ⟨7968395889691720350505481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312263926461146900336987 7968395889691720350505481)
          ·
            refine ⟨5976296917268790262879111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7968395889691720350505481 5976296917268790262879111)
            ·
              refine ⟨8964445375903185394318667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976296917268790262879111 8964445375903185394318667)
              ·
                refine ⟨13446668063854778091478001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964445375903185394318667 13446668063854778091478001)
                ·
                  refine ⟨10085001047891083568608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13446668063854778091478001 10085001047891083568608501)
                  ·
                    refine ⟨945468848239789084557047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085001047891083568608501 945468848239789084557047)
                    ·
                      rfl

theorem cell22_2761941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2761941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761941 prefixEnd_2761941 := by exact prefixLift 2761941
  have htrace : WordTrace (prefixWord ++ tailWord_2761941) baseStart_2761941 baseEnd_2761941 := by
    simpa [prefixWord, tailWord_2761941, baseEnd_2761941] using wordTrace_append hprefix tailTrace_2761941
  have hstable : (prefixWord ++ tailWord_2761941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761941).length < 2 ^ (prefixWord ++ tailWord_2761941).sum := by decide
  have hdescent : baseEnd_2761941 < baseStart_2761941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761971 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 4]
def baseStart_2761971 : Nat := 118140960795 + 2761971 * 2 ^ 59
def prefixEnd_2761971 : Nat := 4983230072969 + 3 ^ 40 * 2761971 * 2
def baseEnd_2761971 : Nat := 315159705950959668768985

theorem tailTrace_2761971 : CollatzResearch.WordTrace tailWord_2761971 prefixEnd_2761971 315159705950959668768985 := by
  unfold tailWord_2761971
  simp only [CollatzResearch.WordTrace]
  refine ⟨100737358276858248937389767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67158238851238832624926511 100737358276858248937389767)
  ·
    refine ⟨151106037415287373406084651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100737358276858248937389767 151106037415287373406084651)
    ·
      refine ⟨226659056122931060109126977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151106037415287373406084651 226659056122931060109126977)
      ·
        refine ⟨169994292092198295081845233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226659056122931060109126977 169994292092198295081845233)
        ·
          refine ⟨127495719069148721311383925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169994292092198295081845233 127495719069148721311383925)
          ·
            refine ⟨11952723662732692622942243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127495719069148721311383925 11952723662732692622942243)
            ·
              refine ⟨17929085494099038934413365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11952723662732692622942243 17929085494099038934413365)
              ·
                refine ⟨1680851765071784900101253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17929085494099038934413365 1680851765071784900101253)
                ·
                  refine ⟨315159705950959668768985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680851765071784900101253 315159705950959668768985)
                  ·
                    rfl

theorem cell22_2761971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 4].length) (baseStart_2761971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761971 prefixEnd_2761971 := by exact prefixLift 2761971
  have htrace : WordTrace (prefixWord ++ tailWord_2761971) baseStart_2761971 baseEnd_2761971 := by
    simpa [prefixWord, tailWord_2761971, baseEnd_2761971] using wordTrace_append hprefix tailTrace_2761971
  have hstable : (prefixWord ++ tailWord_2761971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761971).length < 2 ^ (prefixWord ++ tailWord_2761971).sum := by decide
  have hdescent : baseEnd_2761971 < baseStart_2761971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761984 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_2761984 : Nat := 118140960795 + 2761984 * 2 ^ 59
def prefixEnd_2761984 : Nat := 4983230072969 + 3 ^ 40 * 2761984 * 2
def baseEnd_2761984 : Nat := 945483568018551305731915

theorem tailTrace_2761984 : CollatzResearch.WordTrace tailWord_2761984 prefixEnd_2761984 945483568018551305731915 := by
  unfold tailWord_2761984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50368916212905576078806503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67158554950540768105075337 50368916212905576078806503)
  ·
    refine ⟨75553374319358364118209755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50368916212905576078806503 75553374319358364118209755)
    ·
      refine ⟨113330061479037546177314633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75553374319358364118209755 113330061479037546177314633)
      ·
        refine ⟨84997546109278159632985975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113330061479037546177314633 84997546109278159632985975)
        ·
          refine ⟨127496319163917239449478963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84997546109278159632985975 127496319163917239449478963)
          ·
            refine ⟨191244478745875859174218445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127496319163917239449478963 191244478745875859174218445)
            ·
              refine ⟨71716679529703447190331917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191244478745875859174218445 71716679529703447190331917)
              ·
                refine ⟨26893754823638792696374469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71716679529703447190331917 26893754823638792696374469)
                ·
                  refine ⟨5042579029432273630570213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26893754823638792696374469 5042579029432273630570213)
                  ·
                    refine ⟨945483568018551305731915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5042579029432273630570213 945483568018551305731915)
                    ·
                      rfl

theorem cell22_2761984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_2761984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761984 prefixEnd_2761984 := by exact prefixLift 2761984
  have htrace : WordTrace (prefixWord ++ tailWord_2761984) baseStart_2761984 baseEnd_2761984 := by
    simpa [prefixWord, tailWord_2761984, baseEnd_2761984] using wordTrace_append hprefix tailTrace_2761984
  have hstable : (prefixWord ++ tailWord_2761984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761984).length < 2 ^ (prefixWord ++ tailWord_2761984).sum := by decide
  have hdescent : baseEnd_2761984 < baseStart_2761984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2761988 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2761988 : Nat := 118140960795 + 2761988 * 2 ^ 59
def prefixEnd_2761988 : Nat := 4983230072969 + 3 ^ 40 * 2761988 * 2
def baseEnd_2761988 : Nat := 315161645766765542877301

theorem tailTrace_2761988 : CollatzResearch.WordTrace tailWord_2761988 prefixEnd_2761988 315161645766765542877301 := by
  unfold tailWord_2761988
  simp only [CollatzResearch.WordTrace]
  refine ⟨50368989158898330420379309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67158652211864440560505745 50368989158898330420379309)
  ·
    refine ⟨18888370934586873907642241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50368989158898330420379309 18888370934586873907642241)
    ·
      refine ⟨14166278200940155430731681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18888370934586873907642241 14166278200940155430731681)
      ·
        refine ⟨10624708650705116573048761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14166278200940155430731681 10624708650705116573048761)
        ·
          refine ⟨7968531488028837429786571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10624708650705116573048761 7968531488028837429786571)
          ·
            refine ⟨11952797232043256144679857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7968531488028837429786571 11952797232043256144679857)
            ·
              refine ⟨8964597924032442108509893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11952797232043256144679857 8964597924032442108509893)
              ·
                refine ⟨1680862110756082895345605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8964597924032442108509893 1680862110756082895345605)
                ·
                  refine ⟨315161645766765542877301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1680862110756082895345605 315161645766765542877301)
                  ·
                    rfl

theorem cell22_2761988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2761988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2761988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2761988 prefixEnd_2761988 := by exact prefixLift 2761988
  have htrace : WordTrace (prefixWord ++ tailWord_2761988) baseStart_2761988 baseEnd_2761988 := by
    simpa [prefixWord, tailWord_2761988, baseEnd_2761988] using wordTrace_append hprefix tailTrace_2761988
  have hstable : (prefixWord ++ tailWord_2761988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2761988).length < 2 ^ (prefixWord ++ tailWord_2761988).sum := by decide
  have hdescent : baseEnd_2761988 < baseStart_2761988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2761988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762016 : List Nat := [2, 1, 1, 5, 3, 1, 1, 8]
def baseStart_2762016 : Nat := 118140960795 + 2762016 * 2 ^ 59
def prefixEnd_2762016 : Nat := 4983230072969 + 3 ^ 40 * 2762016 * 2
def baseEnd_2762016 : Nat := 105054946919168209881313

theorem tailTrace_2762016 : CollatzResearch.WordTrace tailWord_2762016 prefixEnd_2762016 105054946919168209881313 := by
  unfold tailWord_2762016
  simp only [CollatzResearch.WordTrace]
  refine ⟨50369499780847610811388951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67159333041130147748518601 50369499780847610811388951)
  ·
    refine ⟨75554249671271416217083427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50369499780847610811388951 75554249671271416217083427)
    ·
      refine ⟨113331374506907124325625141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75554249671271416217083427 113331374506907124325625141)
      ·
        refine ⟨10624816360022542905527357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113331374506907124325625141 10624816360022542905527357)
        ·
          refine ⟨3984306135008453589572759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10624816360022542905527357 3984306135008453589572759)
          ·
            refine ⟨5976459202512680384359139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984306135008453589572759 5976459202512680384359139)
            ·
              refine ⟨8964688803769020576538709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976459202512680384359139 8964688803769020576538709)
              ·
                refine ⟨105054946919168209881313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8964688803769020576538709 105054946919168209881313)
                ·
                  rfl

theorem cell22_2762016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_2762016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762016 prefixEnd_2762016 := by exact prefixLift 2762016
  have htrace : WordTrace (prefixWord ++ tailWord_2762016) baseStart_2762016 baseEnd_2762016 := by
    simpa [prefixWord, tailWord_2762016, baseEnd_2762016] using wordTrace_append hprefix tailTrace_2762016
  have hstable : (prefixWord ++ tailWord_2762016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762016).length < 2 ^ (prefixWord ++ tailWord_2762016).sum := by decide
  have hdescent : baseEnd_2762016 < baseStart_2762016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762046 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2762046 : Nat := 118140960795 + 2762046 * 2 ^ 59
def prefixEnd_2762046 : Nat := 4983230072969 + 3 ^ 40 * 2762046 * 2
def baseEnd_2762046 : Nat := 945504791885603810681725

theorem tailTrace_2762046 : CollatzResearch.WordTrace tailWord_2762046 prefixEnd_2762046 945504791885603810681725 := by
  unfold tailWord_2762046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592511718948317093296249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67160062501057691164246661 12592511718948317093296249)
  ·
    refine ⟨9444383789211237819972187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12592511718948317093296249 9444383789211237819972187)
    ·
      refine ⟨14166575683816856729958281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9444383789211237819972187 14166575683816856729958281)
      ·
        refine ⟨10624931762862642547468711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14166575683816856729958281 10624931762862642547468711)
        ·
          refine ⟨15937397644293963821203067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10624931762862642547468711 15937397644293963821203067)
          ·
            refine ⟨23906096466440945731804601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15937397644293963821203067 23906096466440945731804601)
            ·
              refine ⟨17929572349830709298853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23906096466440945731804601 17929572349830709298853451)
              ·
                refine ⟨26894358524746063948280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17929572349830709298853451 26894358524746063948280177)
                ·
                  refine ⟨20170768893559547961210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26894358524746063948280177 20170768893559547961210133)
                  ·
                    refine ⟨945504791885603810681725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20170768893559547961210133 945504791885603810681725)
                    ·
                      rfl

theorem cell22_2762046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2762046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762046 prefixEnd_2762046 := by exact prefixLift 2762046
  have htrace : WordTrace (prefixWord ++ tailWord_2762046) baseStart_2762046 baseEnd_2762046 := by
    simpa [prefixWord, tailWord_2762046, baseEnd_2762046] using wordTrace_append hprefix tailTrace_2762046
  have hstable : (prefixWord ++ tailWord_2762046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762046).length < 2 ^ (prefixWord ++ tailWord_2762046).sum := by decide
  have hdescent : baseEnd_2762046 < baseStart_2762046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762054 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2762054 : Nat := 118140960795 + 2762054 * 2 ^ 59
def prefixEnd_2762054 : Nat := 4983230072969 + 3 ^ 40 * 2762054 * 2
def baseEnd_2762054 : Nat := 945507530449094456481701

theorem tailTrace_2762054 : CollatzResearch.WordTrace tailWord_2762054 prefixEnd_2762054 945507530449094456481701 := by
  unfold tailWord_2762054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3148137047986173566020663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67160257023705036075107477 3148137047986173566020663)
  ·
    refine ⟨4722205571979260349030995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3148137047986173566020663 4722205571979260349030995)
    ·
      refine ⟨7083308357968890523546493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722205571979260349030995 7083308357968890523546493)
      ·
        refine ⟨2656240634238333946329935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7083308357968890523546493 2656240634238333946329935)
        ·
          refine ⟨3984360951357500919494903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2656240634238333946329935 3984360951357500919494903)
          ·
            refine ⟨5976541427036251379242355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984360951357500919494903 5976541427036251379242355)
            ·
              refine ⟨8964812140554377068863533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976541427036251379242355 8964812140554377068863533)
              ·
                refine ⟨3361804552707891400823825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8964812140554377068863533 3361804552707891400823825)
                ·
                  refine ⟨2521353414530918550617869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361804552707891400823825 2521353414530918550617869)
                  ·
                    refine ⟨945507530449094456481701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521353414530918550617869 945507530449094456481701)
                    ·
                      rfl

theorem cell22_2762054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2762054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762054 prefixEnd_2762054 := by exact prefixLift 2762054
  have htrace : WordTrace (prefixWord ++ tailWord_2762054) baseStart_2762054 baseEnd_2762054 := by
    simpa [prefixWord, tailWord_2762054, baseEnd_2762054] using wordTrace_append hprefix tailTrace_2762054
  have hstable : (prefixWord ++ tailWord_2762054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762054).length < 2 ^ (prefixWord ++ tailWord_2762054).sum := by decide
  have hdescent : baseEnd_2762054 < baseStart_2762054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762059 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_2762059 : Nat := 118140960795 + 2762059 * 2 ^ 59
def prefixEnd_2762059 : Nat := 4983230072969 + 3 ^ 40 * 2762059 * 2
def baseEnd_2762059 : Nat := 945509242051276110106685

theorem tailTrace_2762059 : CollatzResearch.WordTrace tailWord_2762059 prefixEnd_2762059 945509242051276110106685 := by
  unfold tailWord_2762059
  simp only [CollatzResearch.WordTrace]
  refine ⟨100740567900539439966593231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67160378600359626644395487 100740567900539439966593231)
  ·
    refine ⟨151110851850809159949889847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100740567900539439966593231 151110851850809159949889847)
    ·
      refine ⟨226666277776213739924834771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151110851850809159949889847 226666277776213739924834771)
      ·
        refine ⟨339999416664320609887252157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226666277776213739924834771 339999416664320609887252157)
        ·
          refine ⟨127499781249120228707719559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339999416664320609887252157 127499781249120228707719559)
          ·
            refine ⟨191249671873680343061579339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127499781249120228707719559 191249671873680343061579339)
            ·
              refine ⟨286874507810520514592369009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191249671873680343061579339 286874507810520514592369009)
              ·
                refine ⟨215155880857890385944276757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286874507810520514592369009 215155880857890385944276757)
                ·
                  refine ⟨10085431915213611841137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215155880857890385944276757 10085431915213611841137973)
                  ·
                    refine ⟨945509242051276110106685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085431915213611841137973 945509242051276110106685)
                    ·
                      rfl

theorem cell22_2762059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_2762059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762059 prefixEnd_2762059 := by exact prefixLift 2762059
  have htrace : WordTrace (prefixWord ++ tailWord_2762059) baseStart_2762059 baseEnd_2762059 := by
    simpa [prefixWord, tailWord_2762059, baseEnd_2762059] using wordTrace_append hprefix tailTrace_2762059
  have hstable : (prefixWord ++ tailWord_2762059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762059).length < 2 ^ (prefixWord ++ tailWord_2762059).sum := by decide
  have hdescent : baseEnd_2762059 < baseStart_2762059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762089 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 10]
def baseStart_2762089 : Nat := 118140960795 + 2762089 * 2 ^ 59
def prefixEnd_2762089 : Nat := 4983230072969 + 3 ^ 40 * 2762089 * 2
def baseEnd_2762089 : Nat := 315173170554788677285531

theorem tailTrace_2762089 : CollatzResearch.WordTrace tailWord_2762089 prefixEnd_2762089 315173170554788677285531 := by
  unfold tailWord_2762089
  simp only [CollatzResearch.WordTrace]
  refine ⟨100741662090430755090185321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67161108060287170060123547 100741662090430755090185321)
  ·
    refine ⟨75556246567823066317638991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100741662090430755090185321 75556246567823066317638991)
    ·
      refine ⟨113334369851734599476458487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75556246567823066317638991 113334369851734599476458487)
      ·
        refine ⟨170001554777601899214687731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113334369851734599476458487 170001554777601899214687731)
        ·
          refine ⟨255002332166402848822031597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170001554777601899214687731 255002332166402848822031597)
          ·
            refine ⟨95625874562401068308261849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255002332166402848822031597 95625874562401068308261849)
            ·
              refine ⟨71719405921800801231196387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95625874562401068308261849 71719405921800801231196387)
              ·
                refine ⟨107579108882701201846794581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71719405921800801231196387 107579108882701201846794581)
                ·
                  refine ⟨315173170554788677285531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107579108882701201846794581 315173170554788677285531)
                  ·
                    rfl

theorem cell22_2762089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_2762089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762089 prefixEnd_2762089 := by exact prefixLift 2762089
  have htrace : WordTrace (prefixWord ++ tailWord_2762089) baseStart_2762089 baseEnd_2762089 := by
    simpa [prefixWord, tailWord_2762089, baseEnd_2762089] using wordTrace_append hprefix tailTrace_2762089
  have hstable : (prefixWord ++ tailWord_2762089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762089).length < 2 ^ (prefixWord ++ tailWord_2762089).sum := by decide
  have hdescent : baseEnd_2762089 < baseStart_2762089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762138 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_2762138 : Nat := 118140960795 + 2762138 * 2 ^ 59
def prefixEnd_2762138 : Nat := 4983230072969 + 3 ^ 40 * 2762138 * 2
def baseEnd_2762138 : Nat := 945536285365746237381443

theorem tailTrace_2762138 : CollatzResearch.WordTrace tailWord_2762138 prefixEnd_2762138 945536285365746237381443 := by
  unfold tailWord_2762138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25185862316813309114679767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67162299511502157639146045 25185862316813309114679767)
  ·
    refine ⟨37778793475219963672019651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25185862316813309114679767 37778793475219963672019651)
    ·
      refine ⟨56668190212829945508029477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37778793475219963672019651 56668190212829945508029477)
      ·
        refine ⟨10625285664905614782755527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56668190212829945508029477 10625285664905614782755527)
        ·
          refine ⟨15937928497358422174133291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625285664905614782755527 15937928497358422174133291)
          ·
            refine ⟨23906892746037633261199937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15937928497358422174133291 23906892746037633261199937)
            ·
              refine ⟨17930169559528224945899953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23906892746037633261199937 17930169559528224945899953)
              ·
                refine ⟨13447627169646168709424965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17930169559528224945899953 13447627169646168709424965)
                ·
                  refine ⟨2521430094308656633017181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13447627169646168709424965 2521430094308656633017181)
                  ·
                    refine ⟨945536285365746237381443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521430094308656633017181 945536285365746237381443)
                    ·
                      rfl

theorem cell22_2762138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_2762138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762138 prefixEnd_2762138 := by exact prefixLift 2762138
  have htrace : WordTrace (prefixWord ++ tailWord_2762138) baseStart_2762138 baseEnd_2762138 := by
    simpa [prefixWord, tailWord_2762138, baseEnd_2762138] using wordTrace_append hprefix tailTrace_2762138
  have hstable : (prefixWord ++ tailWord_2762138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762138).length < 2 ^ (prefixWord ++ tailWord_2762138).sum := by decide
  have hdescent : baseEnd_2762138 < baseStart_2762138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762142 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2762142 : Nat := 118140960795 + 2762142 * 2 ^ 59
def prefixEnd_2762142 : Nat := 4983230072969 + 3 ^ 40 * 2762142 * 2
def baseEnd_2762142 : Nat := 945537654647491560281431

theorem tailTrace_2762142 : CollatzResearch.WordTrace tailWord_2762142 prefixEnd_2762142 945537654647491560281431 := by
  unfold tailWord_2762142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592949394904843142733085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67162396772825830094576453 12592949394904843142733085)
  ·
    refine ⟨4722356023089316178524907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12592949394904843142733085 4722356023089316178524907)
    ·
      refine ⟨7083534034633974267787361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722356023089316178524907 7083534034633974267787361)
      ·
        refine ⟨5312650525975480700840521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7083534034633974267787361 5312650525975480700840521)
        ·
          refine ⟨3984487894481610525630391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5312650525975480700840521 3984487894481610525630391)
          ·
            refine ⟨5976731841722415788445587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984487894481610525630391 5976731841722415788445587)
            ·
              refine ⟨8965097762583623682668381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976731841722415788445587 8965097762583623682668381)
              ·
                refine ⟨3361911660968858881000643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8965097762583623682668381 3361911660968858881000643)
                ·
                  refine ⟨5042867491453288321500965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361911660968858881000643 5042867491453288321500965)
                  ·
                    refine ⟨945537654647491560281431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5042867491453288321500965 945537654647491560281431)
                    ·
                      rfl

theorem cell22_2762142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2762142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762142 prefixEnd_2762142 := by exact prefixLift 2762142
  have htrace : WordTrace (prefixWord ++ tailWord_2762142) baseStart_2762142 baseEnd_2762142 := by
    simpa [prefixWord, tailWord_2762142, baseEnd_2762142] using wordTrace_append hprefix tailTrace_2762142
  have hstable : (prefixWord ++ tailWord_2762142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762142).length < 2 ^ (prefixWord ++ tailWord_2762142).sum := by decide
  have hdescent : baseEnd_2762142 < baseStart_2762142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762151 : List Nat := [1, 1, 6, 1, 1, 1, 11]
def baseStart_2762151 : Nat := 118140960795 + 2762151 * 2 ^ 59
def prefixEnd_2762151 : Nat := 4983230072969 + 3 ^ 40 * 2762151 * 2
def baseEnd_2762151 : Nat := 35020027241904390252089

theorem tailTrace_2762151 : CollatzResearch.WordTrace tailWord_2762151 prefixEnd_2762151 35020027241904390252089 := by
  unfold tailWord_2762151
  simp only [CollatzResearch.WordTrace]
  refine ⟨100743923416206139678942307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67162615610804093119294871 100743923416206139678942307)
  ·
    refine ⟨151115885124309209518413461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100743923416206139678942307 151115885124309209518413461)
    ·
      refine ⟨7083557115201994196175631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151115885124309209518413461 7083557115201994196175631)
      ·
        refine ⟨10625335672802991294263447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7083557115201994196175631 10625335672802991294263447)
        ·
          refine ⟨15938003509204486941395171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625335672802991294263447 15938003509204486941395171)
          ·
            refine ⟨23907005263806730412092757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15938003509204486941395171 23907005263806730412092757)
            ·
              refine ⟨35020027241904390252089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23907005263806730412092757 35020027241904390252089)
              ·
                rfl

theorem cell22_2762151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 11].length) (baseStart_2762151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762151 prefixEnd_2762151 := by exact prefixLift 2762151
  have htrace : WordTrace (prefixWord ++ tailWord_2762151) baseStart_2762151 baseEnd_2762151 := by
    simpa [prefixWord, tailWord_2762151, baseEnd_2762151] using wordTrace_append hprefix tailTrace_2762151
  have hstable : (prefixWord ++ tailWord_2762151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762151).length < 2 ^ (prefixWord ++ tailWord_2762151).sum := by decide
  have hdescent : baseEnd_2762151 < baseStart_2762151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762172 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_2762172 : Nat := 118140960795 + 2762172 * 2 ^ 59
def prefixEnd_2762172 : Nat := 4983230072969 + 3 ^ 40 * 2762172 * 2
def baseEnd_2762172 : Nat := 945547924260581482031339

theorem tailTrace_2762172 : CollatzResearch.WordTrace tailWord_2762172 prefixEnd_2762172 945547924260581482031339 := by
  unfold tailWord_2762172
  simp only [CollatzResearch.WordTrace]
  refine ⟨50372344674565030132728385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67163126232753373510304513 50372344674565030132728385)
  ·
    refine ⟨37779258505923772599546289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50372344674565030132728385 37779258505923772599546289)
    ·
      refine ⟨28334443879442829449659717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37779258505923772599546289 28334443879442829449659717)
      ·
        refine ⟨5312708227395530521811197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28334443879442829449659717 5312708227395530521811197)
        ·
          refine ⟨1992265585273323945679199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5312708227395530521811197 1992265585273323945679199)
          ·
            refine ⟨2988398377909985918518799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992265585273323945679199 2988398377909985918518799)
            ·
              refine ⟨4482597566864978877778199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988398377909985918518799 4482597566864978877778199)
              ·
                refine ⟨6723896350297468316667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482597566864978877778199 6723896350297468316667299)
                ·
                  refine ⟨10085844525446202475000949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723896350297468316667299 10085844525446202475000949)
                  ·
                    refine ⟨945547924260581482031339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085844525446202475000949 945547924260581482031339)
                    ·
                      rfl

theorem cell22_2762172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_2762172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762172 prefixEnd_2762172 := by exact prefixLift 2762172
  have htrace : WordTrace (prefixWord ++ tailWord_2762172) baseStart_2762172 baseEnd_2762172 := by
    simpa [prefixWord, tailWord_2762172, baseEnd_2762172] using wordTrace_append hprefix tailTrace_2762172
  have hstable : (prefixWord ++ tailWord_2762172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762172).length < 2 ^ (prefixWord ++ tailWord_2762172).sum := by decide
  have hdescent : baseEnd_2762172 < baseStart_2762172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762183 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 3, 3]
def baseStart_2762183 : Nat := 118140960795 + 2762183 * 2 ^ 59
def prefixEnd_2762183 : Nat := 4983230072969 + 3 ^ 40 * 2762183 * 2
def baseEnd_2762183 : Nat := 945551689785381120006305

theorem tailTrace_2762183 : CollatzResearch.WordTrace tailWord_2762183 prefixEnd_2762183 945551689785381120006305 := by
  unfold tailWord_2762183
  simp only [CollatzResearch.WordTrace]
  refine ⟨100745090552090209144107203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67163393701393472762738135 100745090552090209144107203)
  ·
    refine ⟨151117635828135313716160805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100745090552090209144107203 151117635828135313716160805)
    ·
      refine ⟨28334556717775371321780151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151117635828135313716160805 28334556717775371321780151)
      ·
        refine ⟨42501835076663056982670227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28334556717775371321780151 42501835076663056982670227)
        ·
          refine ⟨63752752614994585474005341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42501835076663056982670227 63752752614994585474005341)
          ·
            refine ⟨23907282230622969552752003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63752752614994585474005341 23907282230622969552752003)
            ·
              refine ⟨35860923345934454329128005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907282230622969552752003 35860923345934454329128005)
              ·
                refine ⟨6723923127362710186711501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35860923345934454329128005 6723923127362710186711501)
                ·
                  refine ⟨2521471172761016320016813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6723923127362710186711501 2521471172761016320016813)
                  ·
                    refine ⟨945551689785381120006305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521471172761016320016813 945551689785381120006305)
                    ·
                      rfl

theorem cell22_2762183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_2762183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762183 prefixEnd_2762183 := by exact prefixLift 2762183
  have htrace : WordTrace (prefixWord ++ tailWord_2762183) baseStart_2762183 baseEnd_2762183 := by
    simpa [prefixWord, tailWord_2762183, baseEnd_2762183] using wordTrace_append hprefix tailTrace_2762183
  have hstable : (prefixWord ++ tailWord_2762183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762183).length < 2 ^ (prefixWord ++ tailWord_2762183).sum := by decide
  have hdescent : baseEnd_2762183 < baseStart_2762183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762213 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 7]
def baseStart_2762213 : Nat := 118140960795 + 2762213 * 2 ^ 59
def prefixEnd_2762213 : Nat := 4983230072969 + 3 ^ 40 * 2762213 * 2
def baseEnd_2762213 : Nat := 315187319799490347252071

theorem tailTrace_2762213 : CollatzResearch.WordTrace tailWord_2762213 prefixEnd_2762213 315187319799490347252071 := by
  unfold tailWord_2762213
  simp only [CollatzResearch.WordTrace]
  refine ⟨100746184741981524267699293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67164123161321016178466195 100746184741981524267699293)
  ·
    refine ⟨37779819278243071600387235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100746184741981524267699293 37779819278243071600387235)
    ·
      refine ⟨56669728917364607400580853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37779819278243071600387235 56669728917364607400580853)
      ·
        refine ⟨5312787086002931943804455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56669728917364607400580853 5312787086002931943804455)
        ·
          refine ⟨7969180629004397915706683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312787086002931943804455 7969180629004397915706683)
          ·
            refine ⟨11953770943506596873560025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969180629004397915706683 11953770943506596873560025)
            ·
              refine ⟨8965328207629947655170019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11953770943506596873560025 8965328207629947655170019)
              ·
                refine ⟨13447992311444921482755029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965328207629947655170019 13447992311444921482755029)
                ·
                  refine ⟨315187319799490347252071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13447992311444921482755029 315187319799490347252071)
                  ·
                    rfl

theorem cell22_2762213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_2762213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762213 prefixEnd_2762213 := by exact prefixLift 2762213
  have htrace : WordTrace (prefixWord ++ tailWord_2762213) baseStart_2762213 baseEnd_2762213 := by
    simpa [prefixWord, tailWord_2762213, baseEnd_2762213] using wordTrace_append hprefix tailTrace_2762213
  have hstable : (prefixWord ++ tailWord_2762213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762213).length < 2 ^ (prefixWord ++ tailWord_2762213).sum := by decide
  have hdescent : baseEnd_2762213 < baseStart_2762213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762230 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2762230 : Nat := 118140960795 + 2762230 * 2 ^ 59
def prefixEnd_2762230 : Nat := 4983230072969 + 3 ^ 40 * 2762230 * 2
def baseEnd_2762230 : Nat := 315189259615296221360387

theorem tailTrace_2762230 : CollatzResearch.WordTrace tailWord_2762230 prefixEnd_2762230 315189259615296221360387 := by
  unfold tailWord_2762230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296675298932496010691759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67164536521946624114045429 6296675298932496010691759)
  ·
    refine ⟨9445012948398744016037639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6296675298932496010691759 9445012948398744016037639)
    ·
      refine ⟨14167519422598116024056459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445012948398744016037639 14167519422598116024056459)
      ·
        refine ⟨21251279133897174036084689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14167519422598116024056459 21251279133897174036084689)
        ·
          refine ⟨15938459350422880527063517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21251279133897174036084689 15938459350422880527063517)
          ·
            refine ⟨5976922256408580197648819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15938459350422880527063517 5976922256408580197648819)
            ·
              refine ⟨8965383384612870296473229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976922256408580197648819 8965383384612870296473229)
              ·
                refine ⟨3362018769229826361177461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8965383384612870296473229 3362018769229826361177461)
                ·
                  refine ⟨315189259615296221360387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3362018769229826361177461 315189259615296221360387)
                  ·
                    rfl

theorem cell22_2762230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2762230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762230 prefixEnd_2762230 := by exact prefixLift 2762230
  have htrace : WordTrace (prefixWord ++ tailWord_2762230) baseStart_2762230 baseEnd_2762230 := by
    simpa [prefixWord, tailWord_2762230, baseEnd_2762230] using wordTrace_append hprefix tailTrace_2762230
  have hstable : (prefixWord ++ tailWord_2762230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762230).length < 2 ^ (prefixWord ++ tailWord_2762230).sum := by decide
  have hdescent : baseEnd_2762230 < baseStart_2762230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762243 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 1, 4]
def baseStart_2762243 : Nat := 118140960795 + 2762243 * 2 ^ 59
def prefixEnd_2762243 : Nat := 4983230072969 + 3 ^ 40 * 2762243 * 2
def baseEnd_2762243 : Nat := 945572229011560963506121

theorem tailTrace_2762243 : CollatzResearch.WordTrace tailWord_2762243 prefixEnd_2762243 945572229011560963506121 := by
  unfold tailWord_2762243
  simp only [CollatzResearch.WordTrace]
  refine ⟨100747278931872839391291383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67164852621248559594194255 100747278931872839391291383)
  ·
    refine ⟨151120918397809259086937075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100747278931872839391291383 151120918397809259086937075)
    ·
      refine ⟨226681377596713888630405613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151120918397809259086937075 226681377596713888630405613)
      ·
        refine ⟨85005516598767708236402105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226681377596713888630405613 85005516598767708236402105)
        ·
          refine ⟨63754137449075781177301579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85005516598767708236402105 63754137449075781177301579)
          ·
            refine ⟨95631206173613671765952369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63754137449075781177301579 95631206173613671765952369)
            ·
              refine ⟨71723404630210253824464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95631206173613671765952369 71723404630210253824464277)
              ·
                refine ⟨3362034592041105648021763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71723404630210253824464277 3362034592041105648021763)
                ·
                  refine ⟨5043051888061658472032645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362034592041105648021763 5043051888061658472032645)
                  ·
                    refine ⟨945572229011560963506121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043051888061658472032645 945572229011560963506121)
                    ·
                      rfl

theorem cell22_2762243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_2762243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762243 prefixEnd_2762243 := by exact prefixLift 2762243
  have htrace : WordTrace (prefixWord ++ tailWord_2762243) baseStart_2762243 baseEnd_2762243 := by
    simpa [prefixWord, tailWord_2762243, baseEnd_2762243] using wordTrace_append hprefix tailTrace_2762243
  have hstable : (prefixWord ++ tailWord_2762243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762243).length < 2 ^ (prefixWord ++ tailWord_2762243).sum := by decide
  have hdescent : baseEnd_2762243 < baseStart_2762243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762369 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2762369 : Nat := 118140960795 + 2762369 * 2 ^ 59
def prefixEnd_2762369 : Nat := 4983230072969 + 3 ^ 40 * 2762369 * 2
def baseEnd_2762369 : Nat := 945615361386538634855735

theorem tailTrace_2762369 : CollatzResearch.WordTrace tailWord_2762369 prefixEnd_2762369 945615361386538634855735 := by
  unfold tailWord_2762369
  simp only [CollatzResearch.WordTrace]
  refine ⟨100751874529416362910378161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67167916352944241940252107 100751874529416362910378161)
  ·
    refine ⟨75563905897062272182783621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100751874529416362910378161 75563905897062272182783621)
    ·
      refine ⟨14168232355699176034271929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75563905897062272182783621 14168232355699176034271929)
      ·
        refine ⟨10626174266774382025703947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14168232355699176034271929 10626174266774382025703947)
        ·
          refine ⟨15939261400161573038555921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10626174266774382025703947 15939261400161573038555921)
          ·
            refine ⟨11954446050121179778916941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15939261400161573038555921 11954446050121179778916941)
            ·
              refine ⟨4482917268795442417093853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11954446050121179778916941 4482917268795442417093853)
              ·
                refine ⟨1681093975798290906410195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4482917268795442417093853 1681093975798290906410195)
                ·
                  refine ⟨2521640963697436359615293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681093975798290906410195 2521640963697436359615293)
                  ·
                    refine ⟨945615361386538634855735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521640963697436359615293 945615361386538634855735)
                    ·
                      rfl

theorem cell22_2762369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2762369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762369 prefixEnd_2762369 := by exact prefixLift 2762369
  have htrace : WordTrace (prefixWord ++ tailWord_2762369) baseStart_2762369 baseEnd_2762369 := by
    simpa [prefixWord, tailWord_2762369, baseEnd_2762369] using wordTrace_append hprefix tailTrace_2762369
  have hstable : (prefixWord ++ tailWord_2762369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762369).length < 2 ^ (prefixWord ++ tailWord_2762369).sum := by decide
  have hdescent : baseEnd_2762369 < baseStart_2762369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762386 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2762386 : Nat := 118140960795 + 2762386 * 2 ^ 59
def prefixEnd_2762386 : Nat := 4983230072969 + 3 ^ 40 * 2762386 * 2
def baseEnd_2762386 : Nat := 945621180833956257180683

theorem tailTrace_2762386 : CollatzResearch.WordTrace tailWord_2762386 prefixEnd_2762386 945621180833956257180683 := by
  unfold tailWord_2762386
  simp only [CollatzResearch.WordTrace]
  refine ⟨25188123642588693703436753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67168329713569849875831341 25188123642588693703436753)
  ·
    refine ⟨18891092731941520277577565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25188123642588693703436753 18891092731941520277577565)
    ·
      refine ⟨7084159774478070104091587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18891092731941520277577565 7084159774478070104091587)
      ·
        refine ⟨10626239661717105156137381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084159774478070104091587 10626239661717105156137381)
        ·
          refine ⟨1992419936571957216775759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10626239661717105156137381 1992419936571957216775759)
          ·
            refine ⟨2988629904857935825163639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992419936571957216775759 2988629904857935825163639)
            ·
              refine ⟨4482944857286903737745459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2988629904857935825163639 4482944857286903737745459)
              ·
                refine ⟨6724417285930355606618189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482944857286903737745459 6724417285930355606618189)
                ·
                  refine ⟨2521656482223883352481821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6724417285930355606618189 2521656482223883352481821)
                  ·
                    refine ⟨945621180833956257180683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521656482223883352481821 945621180833956257180683)
                    ·
                      rfl

theorem cell22_2762386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2762386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762386 prefixEnd_2762386 := by exact prefixLift 2762386
  have htrace : WordTrace (prefixWord ++ tailWord_2762386) baseStart_2762386 baseEnd_2762386 := by
    simpa [prefixWord, tailWord_2762386, baseEnd_2762386] using wordTrace_append hprefix tailTrace_2762386
  have hstable : (prefixWord ++ tailWord_2762386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762386).length < 2 ^ (prefixWord ++ tailWord_2762386).sum := by decide
  have hdescent : baseEnd_2762386 < baseStart_2762386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762393 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 6]
def baseStart_2762393 : Nat := 118140960795 + 2762393 * 2 ^ 59
def prefixEnd_2762393 : Nat := 4983230072969 + 3 ^ 40 * 2762393 * 2
def baseEnd_2762393 : Nat := 315207859025670190751887

theorem tailTrace_2762393 : CollatzResearch.WordTrace tailWord_2762393 prefixEnd_2762393 315207859025670190751887 := by
  unfold tailWord_2762393
  simp only [CollatzResearch.WordTrace]
  refine ⟨100752749881329415009251833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67168499920886276672834555 100752749881329415009251833)
  ·
    refine ⟨75564562410997061256938875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100752749881329415009251833 75564562410997061256938875)
    ·
      refine ⟨113346843616495591885408313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75564562410997061256938875 113346843616495591885408313)
      ·
        refine ⟨85010132712371693914056235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113346843616495591885408313 85010132712371693914056235)
        ·
          refine ⟨127515199068557540871084353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85010132712371693914056235 127515199068557540871084353)
          ·
            refine ⟨95636399301418155653313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127515199068557540871084353 95636399301418155653313265)
            ·
              refine ⟨71727299476063616739984949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95636399301418155653313265 71727299476063616739984949)
              ·
                refine ⟨6724434325880964069373589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71727299476063616739984949 6724434325880964069373589)
                ·
                  refine ⟨315207859025670190751887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6724434325880964069373589 315207859025670190751887)
                  ·
                    rfl

theorem cell22_2762393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_2762393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762393 prefixEnd_2762393 := by exact prefixLift 2762393
  have htrace : WordTrace (prefixWord ++ tailWord_2762393) baseStart_2762393 baseEnd_2762393 := by
    simpa [prefixWord, tailWord_2762393, baseEnd_2762393] using wordTrace_append hprefix tailTrace_2762393
  have hstable : (prefixWord ++ tailWord_2762393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762393).length < 2 ^ (prefixWord ++ tailWord_2762393).sum := by decide
  have hdescent : baseEnd_2762393 < baseStart_2762393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762425 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_2762425 : Nat := 118140960795 + 2762425 * 2 ^ 59
def prefixEnd_2762425 : Nat := 4983230072969 + 3 ^ 40 * 2762425 * 2
def baseEnd_2762425 : Nat := 945634531330973155455563

theorem tailTrace_2762425 : CollatzResearch.WordTrace tailWord_2762425 prefixEnd_2762425 945634531330973155455563 := by
  unfold tailWord_2762425
  simp only [CollatzResearch.WordTrace]
  refine ⟨100753917017213484474416729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67169278011475656316277819 100753917017213484474416729)
  ·
    refine ⟨75565437762910113355812547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100753917017213484474416729 75565437762910113355812547)
    ·
      refine ⟨113348156644365170033718821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75565437762910113355812547 113348156644365170033718821)
      ·
        refine ⟨21252779370818469381322279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113348156644365170033718821 21252779370818469381322279)
        ·
          refine ⟨31879169056227704071983419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21252779370818469381322279 31879169056227704071983419)
          ·
            refine ⟨47818753584341556107975129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31879169056227704071983419 47818753584341556107975129)
            ·
              refine ⟨35864065188256167080981347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47818753584341556107975129 35864065188256167080981347)
              ·
                refine ⟨53796097782384250621472021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35864065188256167080981347 53796097782384250621472021)
                ·
                  refine ⟨2521692083549261747881501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53796097782384250621472021 2521692083549261747881501)
                  ·
                    refine ⟨945634531330973155455563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521692083549261747881501 945634531330973155455563)
                    ·
                      rfl

theorem cell22_2762425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_2762425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762425 prefixEnd_2762425 := by exact prefixLift 2762425
  have htrace : WordTrace (prefixWord ++ tailWord_2762425) baseStart_2762425 baseEnd_2762425 := by
    simpa [prefixWord, tailWord_2762425, baseEnd_2762425] using wordTrace_append hprefix tailTrace_2762425
  have hstable : (prefixWord ++ tailWord_2762425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762425).length < 2 ^ (prefixWord ++ tailWord_2762425).sum := by decide
  have hdescent : baseEnd_2762425 < baseStart_2762425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762440 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_2762440 : Nat := 118140960795 + 2762440 * 2 ^ 59
def prefixEnd_2762440 : Nat := 4983230072969 + 3 ^ 40 * 2762440 * 2
def baseEnd_2762440 : Nat := 945639666137518116330517

theorem tailTrace_2762440 : CollatzResearch.WordTrace tailWord_2762440 prefixEnd_2762440 945639666137518116330517 := by
  unfold tailWord_2762440
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377232056079571018106387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67169642741439428024141849 50377232056079571018106387)
  ·
    refine ⟨75565848084119356527159581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50377232056079571018106387 75565848084119356527159581)
    ·
      refine ⟨28337193031544758697684843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75565848084119356527159581 28337193031544758697684843)
      ·
        refine ⟨42505789547317138046527265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28337193031544758697684843 42505789547317138046527265)
        ·
          refine ⟨31879342160487853534895449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42505789547317138046527265 31879342160487853534895449)
          ·
            refine ⟨23909506620365890151171587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31879342160487853534895449 23909506620365890151171587)
            ·
              refine ⟨35864259930548835226757381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23909506620365890151171587 35864259930548835226757381)
              ·
                refine ⟨6724548736977906605017009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35864259930548835226757381 6724548736977906605017009)
                ·
                  refine ⟨5043411552733429953762757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724548736977906605017009 5043411552733429953762757)
                  ·
                    refine ⟨945639666137518116330517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043411552733429953762757 945639666137518116330517)
                    ·
                      rfl

theorem cell22_2762440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_2762440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762440 prefixEnd_2762440 := by exact prefixLift 2762440
  have htrace : WordTrace (prefixWord ++ tailWord_2762440) baseStart_2762440 baseEnd_2762440 := by
    simpa [prefixWord, tailWord_2762440, baseEnd_2762440] using wordTrace_append hprefix tailTrace_2762440
  have hstable : (prefixWord ++ tailWord_2762440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762440).length < 2 ^ (prefixWord ++ tailWord_2762440).sum := by decide
  have hdescent : baseEnd_2762440 < baseStart_2762440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762444 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_2762444 : Nat := 118140960795 + 2762444 * 2 ^ 59
def prefixEnd_2762444 : Nat := 4983230072969 + 3 ^ 40 * 2762444 * 2
def baseEnd_2762444 : Nat := 315213678473087813076835

theorem tailTrace_2762444 : CollatzResearch.WordTrace tailWord_2762444 prefixEnd_2762444 315213678473087813076835 := by
  unfold tailWord_2762444
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377305002072325359679193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67169740002763100479572257 50377305002072325359679193)
  ·
    refine ⟨37782978751554244019759395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50377305002072325359679193 37782978751554244019759395)
    ·
      refine ⟨56674468127331366029639093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37782978751554244019759395 56674468127331366029639093)
      ·
        refine ⟨5313231386937315565278665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56674468127331366029639093 5313231386937315565278665)
        ·
          refine ⟨3984923540202986673958999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5313231386937315565278665 3984923540202986673958999)
          ·
            refine ⟨5977385310304480010938499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984923540202986673958999 5977385310304480010938499)
            ·
              refine ⟨8966077965456720016407749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977385310304480010938499 8966077965456720016407749)
              ·
                refine ⟨1681139618523135003076453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8966077965456720016407749 1681139618523135003076453)
                ·
                  refine ⟨315213678473087813076835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681139618523135003076453 315213678473087813076835)
                  ·
                    rfl

theorem cell22_2762444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_2762444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762444 prefixEnd_2762444 := by exact prefixLift 2762444
  have htrace : WordTrace (prefixWord ++ tailWord_2762444) baseStart_2762444 baseEnd_2762444 := by
    simpa [prefixWord, tailWord_2762444, baseEnd_2762444] using wordTrace_append hprefix tailTrace_2762444
  have hstable : (prefixWord ++ tailWord_2762444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762444).length < 2 ^ (prefixWord ++ tailWord_2762444).sum := by decide
  have hdescent : baseEnd_2762444 < baseStart_2762444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762472 : List Nat := [2, 1, 4, 1, 3, 2, 3, 6]
def baseStart_2762472 : Nat := 118140960795 + 2762472 * 2 ^ 59
def prefixEnd_2762472 : Nat := 4983230072969 + 3 ^ 40 * 2762472 * 2
def baseEnd_2762472 : Nat := 105072291154608966614491

theorem tailTrace_2762472 : CollatzResearch.WordTrace tailWord_2762472 prefixEnd_2762472 105072291154608966614491 := by
  unfold tailWord_2762472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377815624021605750688835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67170420832028807667585113 50377815624021605750688835)
  ·
    refine ⟨75566723436032408626033253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50377815624021605750688835 75566723436032408626033253)
    ·
      refine ⟨14168760644256076617381235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75566723436032408626033253 14168760644256076617381235)
      ·
        refine ⟨21253140966384114926071853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14168760644256076617381235 21253140966384114926071853)
        ·
          refine ⟨7969927862394043097276945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21253140966384114926071853 7969927862394043097276945)
          ·
            refine ⟨5977445896795532322957709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7969927862394043097276945 5977445896795532322957709)
            ·
              refine ⟨2241542211298324621109141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5977445896795532322957709 2241542211298324621109141)
              ·
                refine ⟨105072291154608966614491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2241542211298324621109141 105072291154608966614491)
                ·
                  rfl

theorem cell22_2762472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_2762472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762472 prefixEnd_2762472 := by exact prefixLift 2762472
  have htrace : WordTrace (prefixWord ++ tailWord_2762472) baseStart_2762472 baseEnd_2762472 := by
    simpa [prefixWord, tailWord_2762472, baseEnd_2762472] using wordTrace_append hprefix tailTrace_2762472
  have hstable : (prefixWord ++ tailWord_2762472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762472).length < 2 ^ (prefixWord ++ tailWord_2762472).sum := by decide
  have hdescent : baseEnd_2762472 < baseStart_2762472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762504 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2762504 : Nat := 118140960795 + 2762504 * 2 ^ 59
def prefixEnd_2762504 : Nat := 4983230072969 + 3 ^ 40 * 2762504 * 2
def baseEnd_2762504 : Nat := 945661574645443282730321

theorem tailTrace_2762504 : CollatzResearch.WordTrace tailWord_2762504 prefixEnd_2762504 945661574645443282730321 := by
  unfold tailWord_2762504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50378399191963640483271283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67171198922618187311028377 50378399191963640483271283)
  ·
    refine ⟨75567598787945460724906925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50378399191963640483271283 75567598787945460724906925)
    ·
      refine ⟨28337849545479547771840097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75567598787945460724906925 28337849545479547771840097)
      ·
        refine ⟨21253387159109660828880073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28337849545479547771840097 21253387159109660828880073)
        ·
          refine ⟨15940040369332245621660055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21253387159109660828880073 15940040369332245621660055)
          ·
            refine ⟨23910060553998368432490083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15940040369332245621660055 23910060553998368432490083)
            ·
              refine ⟨35865090830997552648735125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23910060553998368432490083 35865090830997552648735125)
              ·
                refine ⟨1681176132703010280409459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35865090830997552648735125 1681176132703010280409459)
                ·
                  refine ⟨2521764199054515420614189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681176132703010280409459 2521764199054515420614189)
                  ·
                    refine ⟨945661574645443282730321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2521764199054515420614189 945661574645443282730321)
                    ·
                      rfl

theorem cell22_2762504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2762504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762504 prefixEnd_2762504 := by exact prefixLift 2762504
  have htrace : WordTrace (prefixWord ++ tailWord_2762504) baseStart_2762504 baseEnd_2762504 := by
    simpa [prefixWord, tailWord_2762504, baseEnd_2762504] using wordTrace_append hprefix tailTrace_2762504
  have hstable : (prefixWord ++ tailWord_2762504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762504).length < 2 ^ (prefixWord ++ tailWord_2762504).sum := by decide
  have hdescent : baseEnd_2762504 < baseStart_2762504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762592 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_2762592 : Nat := 118140960795 + 2762592 * 2 ^ 59
def prefixEnd_2762592 : Nat := 4983230072969 + 3 ^ 40 * 2762592 * 2
def baseEnd_2762592 : Nat := 945691698843840386530051

theorem tailTrace_2762592 : CollatzResearch.WordTrace tailWord_2762592 prefixEnd_2762592 945691698843840386530051 := by
  unfold tailWord_2762592
  simp only [CollatzResearch.WordTrace]
  refine ⟨50380004003804235997873015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67173338671738981330497353 50380004003804235997873015)
  ·
    refine ⟨75570006005706353996809523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50380004003804235997873015 75570006005706353996809523)
    ·
      refine ⟨113355009008559530995214285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75570006005706353996809523 113355009008559530995214285)
      ·
        refine ⟨42508128378209824123205357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113355009008559530995214285 42508128378209824123205357)
        ·
          refine ⟨15940548141828684046202009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42508128378209824123205357 15940548141828684046202009)
          ·
            refine ⟨11955411106371513034651507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15940548141828684046202009 11955411106371513034651507)
            ·
              refine ⟨17933116659557269551977261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11955411106371513034651507 17933116659557269551977261)
              ·
                refine ⟨6724918747333976081991473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17933116659557269551977261 6724918747333976081991473)
                ·
                  refine ⟨5043689060500482061493605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724918747333976081991473 5043689060500482061493605)
                  ·
                    refine ⟨945691698843840386530051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043689060500482061493605 945691698843840386530051)
                    ·
                      rfl

theorem cell22_2762592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_2762592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762592 prefixEnd_2762592 := by exact prefixLift 2762592
  have htrace : WordTrace (prefixWord ++ tailWord_2762592) baseStart_2762592 baseEnd_2762592 := by
    simpa [prefixWord, tailWord_2762592, baseEnd_2762592] using wordTrace_append hprefix tailTrace_2762592
  have hstable : (prefixWord ++ tailWord_2762592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762592).length < 2 ^ (prefixWord ++ tailWord_2762592).sum := by decide
  have hdescent : baseEnd_2762592 < baseStart_2762592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762594 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2762594 : Nat := 118140960795 + 2762594 * 2 ^ 59
def prefixEnd_2762594 : Nat := 4983230072969 + 3 ^ 40 * 2762594 * 2
def baseEnd_2762594 : Nat := 945692383484713047980045

theorem tailTrace_2762594 : CollatzResearch.WordTrace tailWord_2762594 prefixEnd_2762594 945692383484713047980045 := by
  unfold tailWord_2762594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25190020238400306584329709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67173387302400817558212557 25190020238400306584329709)
  ·
    refine ⟨9446257589400114969123641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25190020238400306584329709 9446257589400114969123641)
    ·
      refine ⟨7084693192050086226842731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9446257589400114969123641 7084693192050086226842731)
      ·
        refine ⟨10627039788075129340264097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084693192050086226842731 10627039788075129340264097)
        ·
          refine ⟨7970279841056347005198073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627039788075129340264097 7970279841056347005198073)
          ·
            refine ⟨5977709880792260253898555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970279841056347005198073 5977709880792260253898555)
            ·
              refine ⟨8966564821188390380847833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977709880792260253898555 8966564821188390380847833)
              ·
                refine ⟨6724923615891292785635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966564821188390380847833 6724923615891292785635875)
                ·
                  refine ⟨10087385423836939178453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6724923615891292785635875 10087385423836939178453813)
                  ·
                    refine ⟨945692383484713047980045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10087385423836939178453813 945692383484713047980045)
                    ·
                      rfl

theorem cell22_2762594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2762594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762594 prefixEnd_2762594 := by exact prefixLift 2762594
  have htrace : WordTrace (prefixWord ++ tailWord_2762594) baseStart_2762594 baseEnd_2762594 := by
    simpa [prefixWord, tailWord_2762594, baseEnd_2762594] using wordTrace_append hprefix tailTrace_2762594
  have hstable : (prefixWord ++ tailWord_2762594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762594).length < 2 ^ (prefixWord ++ tailWord_2762594).sum := by decide
  have hdescent : baseEnd_2762594 < baseStart_2762594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762635 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 9]
def baseStart_2762635 : Nat := 118140960795 + 2762635 * 2 ^ 59
def prefixEnd_2762635 : Nat := 4983230072969 + 3 ^ 40 * 2762635 * 2
def baseEnd_2762635 : Nat := 315235472874200869234973

theorem tailTrace_2762635 : CollatzResearch.WordTrace tailWord_2762635 prefixEnd_2762635 315235472874200869234973 := by
  unfold tailWord_2762635
  simp only [CollatzResearch.WordTrace]
  refine ⟨100761576346452690339561359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67174384230968460226374239 100761576346452690339561359)
  ·
    refine ⟨151142364519679035509342039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100761576346452690339561359 151142364519679035509342039)
    ·
      refine ⟨226713546779518553264013059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151142364519679035509342039 226713546779518553264013059)
      ·
        refine ⟨340070320169277829896019589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226713546779518553264013059 340070320169277829896019589)
        ·
          refine ⟨63763185031739593105503673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340070320169277829896019589 63763185031739593105503673)
          ·
            refine ⟨47822388773804694829127755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63763185031739593105503673 47822388773804694829127755)
            ·
              refine ⟨71733583160707042243691633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47822388773804694829127755 71733583160707042243691633)
              ·
                refine ⟨53800187370530281682768725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71733583160707042243691633 53800187370530281682768725)
                ·
                  refine ⟨315235472874200869234973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53800187370530281682768725 315235472874200869234973)
                  ·
                    rfl

theorem cell22_2762635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_2762635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762635 prefixEnd_2762635 := by exact prefixLift 2762635
  have htrace : WordTrace (prefixWord ++ tailWord_2762635) baseStart_2762635 baseEnd_2762635 := by
    simpa [prefixWord, tailWord_2762635, baseEnd_2762635] using wordTrace_append hprefix tailTrace_2762635
  have hstable : (prefixWord ++ tailWord_2762635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762635).length < 2 ^ (prefixWord ++ tailWord_2762635).sum := by decide
  have hdescent : baseEnd_2762635 < baseStart_2762635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762682 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2762682 : Nat := 118140960795 + 2762682 * 2 ^ 59
def prefixEnd_2762682 : Nat := 4983230072969 + 3 ^ 40 * 2762682 * 2
def baseEnd_2762682 : Nat := 945722507683110151779775

theorem tailTrace_2762682 : CollatzResearch.WordTrace tailWord_2762682 prefixEnd_2762682 945722507683110151779775 := by
  unfold tailWord_2762682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25190822644320604341630575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67175527051521611577681533 25190822644320604341630575)
  ·
    refine ⟨37786233966480906512445863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25190822644320604341630575 37786233966480906512445863)
    ·
      refine ⟨56679350949721359768668795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37786233966480906512445863 56679350949721359768668795)
      ·
        refine ⟨85019026424582039653003193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56679350949721359768668795 85019026424582039653003193)
        ·
          refine ⟨63764269818436529739752395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85019026424582039653003193 63764269818436529739752395)
          ·
            refine ⟨95646404727654794609628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63764269818436529739752395 95646404727654794609628593)
            ·
              refine ⟨71734803545741095957221445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95646404727654794609628593 71734803545741095957221445)
              ·
                refine ⟨13450275664826455491979021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71734803545741095957221445 13450275664826455491979021)
                ·
                  refine ⟨5043853374309920809492133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13450275664826455491979021 5043853374309920809492133)
                  ·
                    refine ⟨945722507683110151779775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043853374309920809492133 945722507683110151779775)
                    ·
                      rfl

theorem cell22_2762682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2762682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762682 prefixEnd_2762682 := by exact prefixLift 2762682
  have htrace : WordTrace (prefixWord ++ tailWord_2762682) baseStart_2762682 baseEnd_2762682 := by
    simpa [prefixWord, tailWord_2762682, baseEnd_2762682] using wordTrace_append hprefix tailTrace_2762682
  have hstable : (prefixWord ++ tailWord_2762682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762682).length < 2 ^ (prefixWord ++ tailWord_2762682).sum := by decide
  have hdescent : baseEnd_2762682 < baseStart_2762682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762686 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2762686 : Nat := 118140960795 + 2762686 * 2 ^ 59
def prefixEnd_2762686 : Nat := 4983230072969 + 3 ^ 40 * 2762686 * 2
def baseEnd_2762686 : Nat := 315241292321618491559921

theorem tailTrace_2762686 : CollatzResearch.WordTrace tailWord_2762686 prefixEnd_2762686 315241292321618491559921 := by
  unfold tailWord_2762686
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595429558658490756208489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67175624312845284033111941 12595429558658490756208489)
  ·
    refine ⟨9446572168993868067156367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12595429558658490756208489 9446572168993868067156367)
    ·
      refine ⟨14169858253490802100734551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9446572168993868067156367 14169858253490802100734551)
      ·
        refine ⟨21254787380236203151101827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14169858253490802100734551 21254787380236203151101827)
        ·
          refine ⟨31882181070354304726652741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21254787380236203151101827 31882181070354304726652741)
          ·
            refine ⟨5977908950691432136247389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31882181070354304726652741 5977908950691432136247389)
            ·
              refine ⟨2241715856509287051092771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5977908950691432136247389 2241715856509287051092771)
              ·
                refine ⟨3362573784763930576639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241715856509287051092771 3362573784763930576639157)
                ·
                  refine ⟨315241292321618491559921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3362573784763930576639157 315241292321618491559921)
                  ·
                    rfl

theorem cell22_2762686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2762686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762686 prefixEnd_2762686 := by exact prefixLift 2762686
  have htrace : WordTrace (prefixWord ++ tailWord_2762686) baseStart_2762686 baseEnd_2762686 := by
    simpa [prefixWord, tailWord_2762686, baseEnd_2762686] using wordTrace_append hprefix tailTrace_2762686
  have hstable : (prefixWord ++ tailWord_2762686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762686).length < 2 ^ (prefixWord ++ tailWord_2762686).sum := by decide
  have hdescent : baseEnd_2762686 < baseStart_2762686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762699 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 1, 4]
def baseStart_2762699 : Nat := 118140960795 + 2762699 * 2 ^ 59
def prefixEnd_2762699 : Nat := 4983230072969 + 3 ^ 40 * 2762699 * 2
def baseEnd_2762699 : Nat := 945728327130527774104723

theorem tailTrace_2762699 : CollatzResearch.WordTrace tailWord_2762699 prefixEnd_2762699 945728327130527774104723 := by
  unfold tailWord_2762699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100763910618220829269891151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67175940412147219513260767 100763910618220829269891151)
  ·
    refine ⟨151145865927331243904836727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100763910618220829269891151 151145865927331243904836727)
    ·
      refine ⟨226718798890996865857255091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151145865927331243904836727 226718798890996865857255091)
      ·
        refine ⟨340078198336495298785882637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226718798890996865857255091 340078198336495298785882637)
        ·
          refine ⟨127529324376185737044705989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340078198336495298785882637 127529324376185737044705989)
          ·
            refine ⟨23911748320534825695882373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127529324376185737044705989 23911748320534825695882373)
            ·
              refine ⟨4483452810100279817977945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23911748320534825695882373 4483452810100279817977945)
              ·
                refine ⟨3362589607575209863483459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4483452810100279817977945 3362589607575209863483459)
                ·
                  refine ⟨5043884411362814795225189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362589607575209863483459 5043884411362814795225189)
                  ·
                    refine ⟨945728327130527774104723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043884411362814795225189 945728327130527774104723)
                    ·
                      rfl

theorem cell22_2762699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_2762699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762699 prefixEnd_2762699 := by exact prefixLift 2762699
  have htrace : WordTrace (prefixWord ++ tailWord_2762699) baseStart_2762699 baseEnd_2762699 := by
    simpa [prefixWord, tailWord_2762699, baseEnd_2762699] using wordTrace_append hprefix tailTrace_2762699
  have hstable : (prefixWord ++ tailWord_2762699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762699).length < 2 ^ (prefixWord ++ tailWord_2762699).sum := by decide
  have hdescent : baseEnd_2762699 < baseStart_2762699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762712 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2762712 : Nat := 118140960795 + 2762712 * 2 ^ 59
def prefixEnd_2762712 : Nat := 4983230072969 + 3 ^ 40 * 2762712 * 2
def baseEnd_2762712 : Nat := 945732777296200073529683

theorem tailTrace_2762712 : CollatzResearch.WordTrace tailWord_2762712 prefixEnd_2762712 945732777296200073529683 := by
  unfold tailWord_2762712
  simp only [CollatzResearch.WordTrace]
  refine ⟨50382192383586866245057195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67176256511449154993409593 50382192383586866245057195)
  ·
    refine ⟨75573288575380299367585793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50382192383586866245057195 75573288575380299367585793)
    ·
      refine ⟨56679966431535224525689345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75573288575380299367585793 56679966431535224525689345)
      ·
        refine ⟨42509974823651418394267009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56679966431535224525689345 42509974823651418394267009)
        ·
          refine ⟨31882481117738563795700257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42509974823651418394267009 31882481117738563795700257)
          ·
            refine ⟨23911860838303922846775193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31882481117738563795700257 23911860838303922846775193)
            ·
              refine ⟨17933895628727942135081395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23911860838303922846775193 17933895628727942135081395)
              ·
                refine ⟨26900843443091913202622093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17933895628727942135081395 26900843443091913202622093)
                ·
                  refine ⟨10087816291159467450983285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26900843443091913202622093 10087816291159467450983285)
                  ·
                    refine ⟨945732777296200073529683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10087816291159467450983285 945732777296200073529683)
                    ·
                      rfl

theorem cell22_2762712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2762712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762712 prefixEnd_2762712 := by exact prefixLift 2762712
  have htrace : WordTrace (prefixWord ++ tailWord_2762712) baseStart_2762712 baseEnd_2762712 := by
    simpa [prefixWord, tailWord_2762712, baseEnd_2762712] using wordTrace_append hprefix tailTrace_2762712
  have hstable : (prefixWord ++ tailWord_2762712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762712).length < 2 ^ (prefixWord ++ tailWord_2762712).sum := by decide
  have hdescent : baseEnd_2762712 < baseStart_2762712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762838 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2762838 : Nat := 118140960795 + 2762838 * 2 ^ 59
def prefixEnd_2762838 : Nat := 4983230072969 + 3 ^ 40 * 2762838 * 2
def baseEnd_2762838 : Nat := 315258636557059248293099

theorem tailTrace_2762838 : CollatzResearch.WordTrace tailWord_2762838 prefixEnd_2762838 315258636557059248293099 := by
  unfold tailWord_2762838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298061272794828500575073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67179320243144837339467445 6298061272794828500575073)
  ·
    refine ⟨4723545954596121375431305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6298061272794828500575073 4723545954596121375431305)
    ·
      refine ⟨3542659465947091031573479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4723545954596121375431305 3542659465947091031573479)
      ·
        refine ⟨5313989198920636547360219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542659465947091031573479 5313989198920636547360219)
        ·
          refine ⟨7970983798380954821040329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313989198920636547360219 7970983798380954821040329)
          ·
            refine ⟨5978237848785716115780247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970983798380954821040329 5978237848785716115780247)
            ·
              refine ⟨8967356773178574173670371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978237848785716115780247 8967356773178574173670371)
              ·
                refine ⟨13451035159767861260505557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8967356773178574173670371 13451035159767861260505557)
                ·
                  refine ⟨315258636557059248293099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13451035159767861260505557 315258636557059248293099)
                  ·
                    rfl

theorem cell22_2762838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2762838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762838 prefixEnd_2762838 := by exact prefixLift 2762838
  have htrace : WordTrace (prefixWord ++ tailWord_2762838) baseStart_2762838 baseEnd_2762838 := by
    simpa [prefixWord, tailWord_2762838, baseEnd_2762838] using wordTrace_append hprefix tailTrace_2762838
  have hstable : (prefixWord ++ tailWord_2762838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762838).length < 2 ^ (prefixWord ++ tailWord_2762838).sum := by decide
  have hdescent : baseEnd_2762838 < baseStart_2762838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762883 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 4]
def baseStart_2762883 : Nat := 118140960795 + 2762883 * 2 ^ 59
def prefixEnd_2762883 : Nat := 4983230072969 + 3 ^ 40 * 2762883 * 2
def baseEnd_2762883 : Nat := 315263771363604209168053

theorem tailTrace_2762883 : CollatzResearch.WordTrace tailWord_2762883 prefixEnd_2762883 315263771363604209168053 := by
  unfold tailWord_2762883
  simp only [CollatzResearch.WordTrace]
  refine ⟨100770621649554228694589303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67180414433036152463059535 100770621649554228694589303)
  ·
    refine ⟨151155932474331343041883955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100770621649554228694589303 151155932474331343041883955)
    ·
      refine ⟨226733898711497014562825933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151155932474331343041883955 226733898711497014562825933)
      ·
        refine ⟨85025212016811380461059725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226733898711497014562825933 85025212016811380461059725)
        ·
          refine ⟨31884454506304267672897397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85025212016811380461059725 31884454506304267672897397)
          ·
            refine ⟨2989167609966025094334131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31884454506304267672897397 2989167609966025094334131)
            ·
              refine ⟨4483751414949037641501197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989167609966025094334131 4483751414949037641501197)
              ·
                refine ⟨1681406780605889115562949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4483751414949037641501197 1681406780605889115562949)
                ·
                  refine ⟨315263771363604209168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681406780605889115562949 315263771363604209168053)
                  ·
                    rfl

theorem cell22_2762883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 4].length) (baseStart_2762883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762883 prefixEnd_2762883 := by exact prefixLift 2762883
  have htrace : WordTrace (prefixWord ++ tailWord_2762883) baseStart_2762883 baseEnd_2762883 := by
    simpa [prefixWord, tailWord_2762883, baseEnd_2762883] using wordTrace_append hprefix tailTrace_2762883
  have hstable : (prefixWord ++ tailWord_2762883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762883).length < 2 ^ (prefixWord ++ tailWord_2762883).sum := by decide
  have hdescent : baseEnd_2762883 < baseStart_2762883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762898 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2762898 : Nat := 118140960795 + 2762898 * 2 ^ 59
def prefixEnd_2762898 : Nat := 4983230072969 + 3 ^ 40 * 2762898 * 2
def baseEnd_2762898 : Nat := 945796448897357588379113

theorem tailTrace_2762898 : CollatzResearch.WordTrace tailWord_2762898 prefixEnd_2762898 945796448897357588379113 := by
  unfold tailWord_2762898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25192792186124971564096337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67180779162999924170923565 25192792186124971564096337)
  ·
    refine ⟨18894594139593728673072253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25192792186124971564096337 18894594139593728673072253)
    ·
      refine ⟨7085472802347648252402095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18894594139593728673072253 7085472802347648252402095)
      ·
        refine ⟨10628209203521472378603143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085472802347648252402095 10628209203521472378603143)
        ·
          refine ⟨15942313805282208567904715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10628209203521472378603143 15942313805282208567904715)
          ·
            refine ⟨23913470707923312851857073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15942313805282208567904715 23913470707923312851857073)
            ·
              refine ⟨17935103030942484638892805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23913470707923312851857073 17935103030942484638892805)
              ·
                refine ⟨3362831818301715869792401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17935103030942484638892805 3362831818301715869792401)
                ·
                  refine ⟨2522123863726286902344301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3362831818301715869792401 2522123863726286902344301)
                  ·
                    refine ⟨945796448897357588379113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522123863726286902344301 945796448897357588379113)
                    ·
                      rfl

theorem cell22_2762898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2762898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762898 prefixEnd_2762898 := by exact prefixLift 2762898
  have htrace : WordTrace (prefixWord ++ tailWord_2762898) baseStart_2762898 baseEnd_2762898 := by
    simpa [prefixWord, tailWord_2762898, baseEnd_2762898] using wordTrace_append hprefix tailTrace_2762898
  have hstable : (prefixWord ++ tailWord_2762898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762898).length < 2 ^ (prefixWord ++ tailWord_2762898).sum := by decide
  have hdescent : baseEnd_2762898 < baseStart_2762898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762900 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2762900 : Nat := 118140960795 + 2762900 * 2 ^ 59
def prefixEnd_2762900 : Nat := 4983230072969 + 3 ^ 40 * 2762900 * 2
def baseEnd_2762900 : Nat := 315265711179410083276369

theorem tailTrace_2762900 : CollatzResearch.WordTrace tailWord_2762900 prefixEnd_2762900 315265711179410083276369 := by
  unfold tailWord_2762900
  simp only [CollatzResearch.WordTrace]
  refine ⟨50385620845246320298979077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67180827793661760398638769 50385620845246320298979077)
  ·
    refine ⟨9447303908483685056058577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50385620845246320298979077 9447303908483685056058577)
    ·
      refine ⟨7085477931362763792043933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9447303908483685056058577 7085477931362763792043933)
      ·
        refine ⟨2657054224261036422016475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7085477931362763792043933 2657054224261036422016475)
        ·
          refine ⟨3985581336391554633024713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657054224261036422016475 3985581336391554633024713)
          ·
            refine ⟨2989186002293665974768535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3985581336391554633024713 2989186002293665974768535)
            ·
              refine ⟨4483779003440498962152803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989186002293665974768535 4483779003440498962152803)
              ·
                refine ⟨6725668505160748443229205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483779003440498962152803 6725668505160748443229205)
                ·
                  refine ⟨315265711179410083276369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6725668505160748443229205 315265711179410083276369)
                  ·
                    rfl

theorem cell22_2762900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2762900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762900 prefixEnd_2762900 := by exact prefixLift 2762900
  have htrace : WordTrace (prefixWord ++ tailWord_2762900) baseStart_2762900 baseEnd_2762900 := by
    simpa [prefixWord, tailWord_2762900, baseEnd_2762900] using wordTrace_append hprefix tailTrace_2762900
  have hstable : (prefixWord ++ tailWord_2762900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762900).length < 2 ^ (prefixWord ++ tailWord_2762900).sum := by decide
  have hdescent : baseEnd_2762900 < baseStart_2762900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762911 : List Nat := [1, 1, 2, 6, 1, 2, 2, 7]
def baseStart_2762911 : Nat := 118140960795 + 2762911 * 2 ^ 59
def prefixEnd_2762911 : Nat := 4983230072969 + 3 ^ 40 * 2762911 * 2
def baseEnd_2762911 : Nat := 105088988784781098644897

theorem tailTrace_2762911 : CollatzResearch.WordTrace tailWord_2762911 prefixEnd_2762911 105088988784781098644897 := by
  unfold tailWord_2762911
  simp only [CollatzResearch.WordTrace]
  refine ⟨100771642893452789476608587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67181095262301859651072391 100771642893452789476608587)
  ·
    refine ⟨151157464340179184214912881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100771642893452789476608587 151157464340179184214912881)
    ·
      refine ⟨113368098255134388161184661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151157464340179184214912881 113368098255134388161184661)
      ·
        refine ⟨5314129605709424445055531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113368098255134388161184661 5314129605709424445055531)
        ·
          refine ⟨7971194408564136667583297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314129605709424445055531 7971194408564136667583297)
          ·
            refine ⟨5978395806423102500687473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971194408564136667583297 5978395806423102500687473)
            ·
              refine ⟨4483796854817326875515605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5978395806423102500687473 4483796854817326875515605)
              ·
                refine ⟨105088988784781098644897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4483796854817326875515605 105088988784781098644897)
                ·
                  rfl

theorem cell22_2762911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 7].length) (baseStart_2762911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762911 prefixEnd_2762911 := by exact prefixLift 2762911
  have htrace : WordTrace (prefixWord ++ tailWord_2762911) baseStart_2762911 baseEnd_2762911 := by
    simpa [prefixWord, tailWord_2762911, baseEnd_2762911] using wordTrace_append hprefix tailTrace_2762911
  have hstable : (prefixWord ++ tailWord_2762911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762911).length < 2 ^ (prefixWord ++ tailWord_2762911).sum := by decide
  have hdescent : baseEnd_2762911 < baseStart_2762911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762932 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2762932 : Nat := 118140960795 + 2762932 * 2 ^ 59
def prefixEnd_2762932 : Nat := 4983230072969 + 3 ^ 40 * 2762932 * 2
def baseEnd_2762932 : Nat := 945808087792192833029009

theorem tailTrace_2762932 : CollatzResearch.WordTrace tailWord_2762932 prefixEnd_2762932 945808087792192833029009 := by
  unfold tailWord_2762932
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386204413188355031561525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67181605884251140042082033 50386204413188355031561525)
  ·
    refine ⟨4723706663736408284208893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50386204413188355031561525 4723706663736408284208893)
    ·
      refine ⟨1771389998901153106578335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4723706663736408284208893 1771389998901153106578335)
      ·
        refine ⟨2657084998351729659867503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771389998901153106578335 2657084998351729659867503)
        ·
          refine ⟨3985627497527594489801255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657084998351729659867503 3985627497527594489801255)
          ·
            refine ⟨5978441246291391734701883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985627497527594489801255 5978441246291391734701883)
            ·
              refine ⟨8967661869437087602052825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978441246291391734701883 8967661869437087602052825)
              ·
                refine ⟨6725746402077815701539619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8967661869437087602052825 6725746402077815701539619)
                ·
                  refine ⟨10088619603116723552309429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725746402077815701539619 10088619603116723552309429)
                  ·
                    refine ⟨945808087792192833029009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10088619603116723552309429 945808087792192833029009)
                    ·
                      rfl

theorem cell22_2762932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2762932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762932 prefixEnd_2762932 := by exact prefixLift 2762932
  have htrace : WordTrace (prefixWord ++ tailWord_2762932) baseStart_2762932 baseEnd_2762932 := by
    simpa [prefixWord, tailWord_2762932, baseEnd_2762932] using wordTrace_append hprefix tailTrace_2762932
  have hstable : (prefixWord ++ tailWord_2762932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762932).length < 2 ^ (prefixWord ++ tailWord_2762932).sum := by decide
  have hdescent : baseEnd_2762932 < baseStart_2762932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762943 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 1, 3]
def baseStart_2762943 : Nat := 118140960795 + 2762943 * 2 ^ 59
def prefixEnd_2762943 : Nat := 4983230072969 + 3 ^ 40 * 2762943 * 2
def baseEnd_2762943 : Nat := 945811853316992471003975

theorem tailTrace_2762943 : CollatzResearch.WordTrace tailWord_2762943 prefixEnd_2762943 945811853316992471003975 := by
  unfold tailWord_2762943
  simp only [CollatzResearch.WordTrace]
  refine ⟨100772810029336858941773483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67181873352891239294515655 100772810029336858941773483)
  ·
    refine ⟨151159215044005288412660225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100772810029336858941773483 151159215044005288412660225)
    ·
      refine ⟨113369411283003966309495169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151159215044005288412660225 113369411283003966309495169)
      ·
        refine ⟨85027058462252974732121377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113369411283003966309495169 85027058462252974732121377)
        ·
          refine ⟨63770293846689731049091033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85027058462252974732121377 63770293846689731049091033)
          ·
            refine ⟨47827720385017298286818275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63770293846689731049091033 47827720385017298286818275)
            ·
              refine ⟨71741580577525947430227413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47827720385017298286818275 71741580577525947430227413)
              ·
                refine ⟨1681443294785764392895955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71741580577525947430227413 1681443294785764392895955)
                ·
                  refine ⟨2522164942178646589343933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681443294785764392895955 2522164942178646589343933)
                  ·
                    refine ⟨945811853316992471003975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522164942178646589343933 945811853316992471003975)
                    ·
                      rfl

theorem cell22_2762943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_2762943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762943 prefixEnd_2762943 := by exact prefixLift 2762943
  have htrace : WordTrace (prefixWord ++ tailWord_2762943) baseStart_2762943 baseEnd_2762943 := by
    simpa [prefixWord, tailWord_2762943, baseEnd_2762943] using wordTrace_append hprefix tailTrace_2762943
  have hstable : (prefixWord ++ tailWord_2762943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762943).length < 2 ^ (prefixWord ++ tailWord_2762943).sum := by decide
  have hdescent : baseEnd_2762943 < baseStart_2762943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762973 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2762973 : Nat := 118140960795 + 2762973 * 2 ^ 59
def prefixEnd_2762973 : Nat := 4983230072969 + 3 ^ 40 * 2762973 * 2
def baseEnd_2762973 : Nat := 315274040976694130917961

theorem tailTrace_2762973 : CollatzResearch.WordTrace tailWord_2762973 prefixEnd_2762973 315274040976694130917961 := by
  unfold tailWord_2762973
  simp only [CollatzResearch.WordTrace]
  refine ⟨100773904219228174065365573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67182602812818782710243715 100773904219228174065365573)
  ·
    refine ⟨18895107041105282637256045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100773904219228174065365573 18895107041105282637256045)
    ·
      refine ⟨7085665140414480988971017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18895107041105282637256045 7085665140414480988971017)
      ·
        refine ⟨5314248855310860741728263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7085665140414480988971017 5314248855310860741728263)
        ·
          refine ⟨7971373282966291112592395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314248855310860741728263 7971373282966291112592395)
          ·
            refine ⟨11957059924449436668888593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971373282966291112592395 11957059924449436668888593)
            ·
              refine ⟨8967794943337077501666445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957059924449436668888593 8967794943337077501666445)
              ·
                refine ⟨3362923103751404063124917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8967794943337077501666445 3362923103751404063124917)
                ·
                  refine ⟨315274040976694130917961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3362923103751404063124917 315274040976694130917961)
                  ·
                    rfl

theorem cell22_2762973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2762973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762973 prefixEnd_2762973 := by exact prefixLift 2762973
  have htrace : WordTrace (prefixWord ++ tailWord_2762973) baseStart_2762973 baseEnd_2762973 := by
    simpa [prefixWord, tailWord_2762973, baseEnd_2762973] using wordTrace_append hprefix tailTrace_2762973
  have hstable : (prefixWord ++ tailWord_2762973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762973).length < 2 ^ (prefixWord ++ tailWord_2762973).sum := by decide
  have hdescent : baseEnd_2762973 < baseStart_2762973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2762986 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2762986 : Nat := 118140960795 + 2762986 * 2 ^ 59
def prefixEnd_2762986 : Nat := 4983230072969 + 3 ^ 40 * 2762986 * 2
def baseEnd_2762986 : Nat := 945826573095754692178843

theorem tailTrace_2762986 : CollatzResearch.WordTrace tailWord_2762986 prefixEnd_2762986 945826573095754692178843 := by
  unfold tailWord_2762986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193594592045269321397203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67182918912120718190392541 25193594592045269321397203)
  ·
    refine ⟨37790391888067903982095805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193594592045269321397203 37790391888067903982095805)
    ·
      refine ⟨14171396958025463993285927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37790391888067903982095805 14171396958025463993285927)
      ·
        refine ⟨21257095437038195989928891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14171396958025463993285927 21257095437038195989928891)
        ·
          refine ⟨31885643155557293984893337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21257095437038195989928891 31885643155557293984893337)
          ·
            refine ⟨23914232366667970488670003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31885643155557293984893337 23914232366667970488670003)
            ·
              refine ⟨35871348550001955733005005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23914232366667970488670003 35871348550001955733005005)
              ·
                refine ⟨13451755706250733399876877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35871348550001955733005005 13451755706250733399876877)
                ·
                  refine ⟨5044408389844025024953829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13451755706250733399876877 5044408389844025024953829)
                  ·
                    refine ⟨945826573095754692178843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044408389844025024953829 945826573095754692178843)
                    ·
                      rfl

theorem cell22_2762986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2762986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2762986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2762986 prefixEnd_2762986 := by exact prefixLift 2762986
  have htrace : WordTrace (prefixWord ++ tailWord_2762986) baseStart_2762986 baseEnd_2762986 := by
    simpa [prefixWord, tailWord_2762986, baseEnd_2762986] using wordTrace_append hprefix tailTrace_2762986
  have hstable : (prefixWord ++ tailWord_2762986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2762986).length < 2 ^ (prefixWord ++ tailWord_2762986).sum := by decide
  have hdescent : baseEnd_2762986 < baseStart_2762986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2762986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763018 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_2763018 : Nat := 118140960795 + 2763018 * 2 ^ 59
def prefixEnd_2763018 : Nat := 4983230072969 + 3 ^ 40 * 2763018 * 2
def baseEnd_2763018 : Nat := 315279175783239091792915

theorem tailTrace_2763018 : CollatzResearch.WordTrace tailWord_2763018 prefixEnd_2763018 315279175783239091792915 := by
  unfold tailWord_2763018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193886376016286687688427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67183697002710097833835805 25193886376016286687688427)
  ·
    refine ⟨37790829564024430031532641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193886376016286687688427 37790829564024430031532641)
    ·
      refine ⟨28343122173018322523649481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37790829564024430031532641 28343122173018322523649481)
      ·
        refine ⟨21257341629763741892737111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28343122173018322523649481 21257341629763741892737111)
        ·
          refine ⟨31886012444645612839105667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21257341629763741892737111 31886012444645612839105667)
          ·
            refine ⟨47829018666968419258658501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31886012444645612839105667 47829018666968419258658501)
            ·
              refine ⟨8967941000056578610998469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47829018666968419258658501 8967941000056578610998469)
              ·
                refine ⟨1681488937510608489562213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8967941000056578610998469 1681488937510608489562213)
                ·
                  refine ⟨315279175783239091792915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681488937510608489562213 315279175783239091792915)
                  ·
                    rfl

theorem cell22_2763018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_2763018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763018 prefixEnd_2763018 := by exact prefixLift 2763018
  have htrace : WordTrace (prefixWord ++ tailWord_2763018) baseStart_2763018 baseEnd_2763018 := by
    simpa [prefixWord, tailWord_2763018, baseEnd_2763018] using wordTrace_append hprefix tailTrace_2763018
  have hstable : (prefixWord ++ tailWord_2763018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763018).length < 2 ^ (prefixWord ++ tailWord_2763018).sum := by decide
  have hdescent : baseEnd_2763018 < baseStart_2763018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763031 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2763031 : Nat := 118140960795 + 2763031 * 2 ^ 59
def prefixEnd_2763031 : Nat := 4983230072969 + 3 ^ 40 * 2763031 * 2
def baseEnd_2763031 : Nat := 945841977515389574803705

theorem tailTrace_2763031 : CollatzResearch.WordTrace tailWord_2763031 prefixEnd_2763031 945841977515389574803705 := by
  unfold tailWord_2763031
  simp only [CollatzResearch.WordTrace]
  refine ⟨100776019653018049970976947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67184013102012033313984631 100776019653018049970976947)
  ·
    refine ⟨151164029479527074956465421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100776019653018049970976947 151164029479527074956465421)
    ·
      refine ⟨56686511054822653108674533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151164029479527074956465421 56686511054822653108674533)
      ·
        refine ⟨10628720822779247457876475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56686511054822653108674533 10628720822779247457876475)
        ·
          refine ⟨15943081234168871186814713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10628720822779247457876475 15943081234168871186814713)
          ·
            refine ⟨11957310925626653390111035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15943081234168871186814713 11957310925626653390111035)
            ·
              refine ⟨17935966388439980085166553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11957310925626653390111035 17935966388439980085166553)
              ·
                refine ⟨13451974791329985063874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17935966388439980085166553 13451974791329985063874915)
                ·
                  refine ⟨20177962186994977595812373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13451974791329985063874915 20177962186994977595812373)
                  ·
                    refine ⟨945841977515389574803705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20177962186994977595812373 945841977515389574803705)
                    ·
                      rfl

theorem cell22_2763031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2763031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763031 prefixEnd_2763031 := by exact prefixLift 2763031
  have htrace : WordTrace (prefixWord ++ tailWord_2763031) baseStart_2763031 baseEnd_2763031 := by
    simpa [prefixWord, tailWord_2763031, baseEnd_2763031] using wordTrace_append hprefix tailTrace_2763031
  have hstable : (prefixWord ++ tailWord_2763031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763031).length < 2 ^ (prefixWord ++ tailWord_2763031).sum := by decide
  have hdescent : baseEnd_2763031 < baseStart_2763031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763125 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 5]
def baseStart_2763125 : Nat := 118140960795 + 2763125 * 2 ^ 59
def prefixEnd_2763125 : Nat := 4983230072969 + 3 ^ 40 * 2763125 * 2
def baseEnd_2763125 : Nat := 315291385212134887651139

theorem tailTrace_2763125 : CollatzResearch.WordTrace tailWord_2763125 prefixEnd_2763125 315291385212134887651139 := by
  unfold tailWord_2763125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100779448114677504024898829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67186298743118336016599219 100779448114677504024898829)
  ·
    refine ⟨37792293043004064009337061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100779448114677504024898829 37792293043004064009337061)
    ·
      refine ⟨7086054945563262001750699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37792293043004064009337061 7086054945563262001750699)
      ·
        refine ⟨10629082418344893002626049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086054945563262001750699 10629082418344893002626049)
        ·
          refine ⟨7971811813758669751969537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10629082418344893002626049 7971811813758669751969537)
          ·
            refine ⟨5978858860319002313977153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971811813758669751969537 5978858860319002313977153)
            ·
              refine ⟨4484144145239251735482865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5978858860319002313977153 4484144145239251735482865)
              ·
                refine ⟨3363108108929438801612149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4484144145239251735482865 3363108108929438801612149)
                ·
                  refine ⟨315291385212134887651139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363108108929438801612149 315291385212134887651139)
                  ·
                    rfl

theorem cell22_2763125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_2763125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763125 prefixEnd_2763125 := by exact prefixLift 2763125
  have htrace : WordTrace (prefixWord ++ tailWord_2763125) baseStart_2763125 baseEnd_2763125 := by
    simpa [prefixWord, tailWord_2763125, baseEnd_2763125] using wordTrace_append hprefix tailTrace_2763125
  have hstable : (prefixWord ++ tailWord_2763125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763125).length < 2 ^ (prefixWord ++ tailWord_2763125).sum := by decide
  have hdescent : baseEnd_2763125 < baseStart_2763125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763168 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_2763168 : Nat := 118140960795 + 2763168 * 2 ^ 59
def prefixEnd_2763168 : Nat := 4983230072969 + 3 ^ 40 * 2763168 * 2
def baseEnd_2763168 : Nat := 945888875415166884128285

theorem tailTrace_2763168 : CollatzResearch.WordTrace tailWord_2763168 prefixEnd_2763168 945888875415166884128285 := by
  unfold tailWord_2763168
  simp only [CollatzResearch.WordTrace]
  refine ⟨50390508226760861184357079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67187344302347814912476105 50390508226760861184357079)
  ·
    refine ⟨75585762340141291776535619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50390508226760861184357079 75585762340141291776535619)
    ·
      refine ⟨113378643510211937664803429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75585762340141291776535619 113378643510211937664803429)
      ·
        refine ⟨21258495658164738312150643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113378643510211937664803429 21258495658164738312150643)
        ·
          refine ⟨31887743487247107468225965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21258495658164738312150643 31887743487247107468225965)
          ·
            refine ⟨11957903807717665300584737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31887743487247107468225965 11957903807717665300584737)
            ·
              refine ⟨8968427855788248975438553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957903807717665300584737 8968427855788248975438553)
              ·
                refine ⟨6726320891841186731578915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8968427855788248975438553 6726320891841186731578915)
                ·
                  refine ⟨10089481337761780097368373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6726320891841186731578915 10089481337761780097368373)
                  ·
                    refine ⟨945888875415166884128285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10089481337761780097368373 945888875415166884128285)
                    ·
                      rfl

theorem cell22_2763168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_2763168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763168 prefixEnd_2763168 := by exact prefixLift 2763168
  have htrace : WordTrace (prefixWord ++ tailWord_2763168) baseStart_2763168 baseEnd_2763168 := by
    simpa [prefixWord, tailWord_2763168, baseEnd_2763168] using wordTrace_append hprefix tailTrace_2763168
  have hstable : (prefixWord ++ tailWord_2763168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763168).length < 2 ^ (prefixWord ++ tailWord_2763168).sum := by decide
  have hdescent : baseEnd_2763168 < baseStart_2763168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763185 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_2763185 : Nat := 118140960795 + 2763185 * 2 ^ 59
def prefixEnd_2763185 : Nat := 4983230072969 + 3 ^ 40 * 2763185 * 2
def baseEnd_2763185 : Nat := 945894694862584506453233

theorem tailTrace_2763185 : CollatzResearch.WordTrace tailWord_2763185 prefixEnd_2763185 945894694862584506453233 := by
  unfold tailWord_2763185
  simp only [CollatzResearch.WordTrace]
  refine ⟨100781636494460134272083009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67187757662973422848055339 100781636494460134272083009)
  ·
    refine ⟨75586227370845100704062257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100781636494460134272083009 75586227370845100704062257)
    ·
      refine ⟨56689670528133825528046693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75586227370845100704062257 56689670528133825528046693)
      ·
        refine ⟨10629313224025092286508755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56689670528133825528046693 10629313224025092286508755)
        ·
          refine ⟨15943969836037638429763133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10629313224025092286508755 15943969836037638429763133)
          ·
            refine ⟨5978988688514114411161175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15943969836037638429763133 5978988688514114411161175)
            ·
              refine ⟨8968483032771171616741763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978988688514114411161175 8968483032771171616741763)
              ·
                refine ⟨13452724549156757425112645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968483032771171616741763 13452724549156757425112645)
                ·
                  refine ⟨2522385852966892017208621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13452724549156757425112645 2522385852966892017208621)
                  ·
                    refine ⟨945894694862584506453233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522385852966892017208621 945894694862584506453233)
                    ·
                      rfl

theorem cell22_2763185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_2763185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763185 prefixEnd_2763185 := by exact prefixLift 2763185
  have htrace : WordTrace (prefixWord ++ tailWord_2763185) baseStart_2763185 baseEnd_2763185 := by
    simpa [prefixWord, tailWord_2763185, baseEnd_2763185] using wordTrace_append hprefix tailTrace_2763185
  have hstable : (prefixWord ++ tailWord_2763185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763185).length < 2 ^ (prefixWord ++ tailWord_2763185).sum := by decide
  have hdescent : baseEnd_2763185 < baseStart_2763185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763234 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2763234 : Nat := 118140960795 + 2763234 * 2 ^ 59
def prefixEnd_2763234 : Nat := 4983230072969 + 3 ^ 40 * 2763234 * 2
def baseEnd_2763234 : Nat := 945911468563964711978083

theorem tailTrace_2763234 : CollatzResearch.WordTrace tailWord_2763234 prefixEnd_2763234 945911468563964711978083 := by
  unfold tailWord_2763234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25195855917820653910154189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67188949114188410427077837 25195855917820653910154189)
  ·
    refine ⟨9448445969182745216307821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25195855917820653910154189 9448445969182745216307821)
    ·
      refine ⟨3543167238443529456115433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9448445969182745216307821 3543167238443529456115433)
      ·
        refine ⟨2657375428832647092086575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543167238443529456115433 2657375428832647092086575)
        ·
          refine ⟨3986063143248970638129863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657375428832647092086575 3986063143248970638129863)
          ·
            refine ⟨5979094714873455957194795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986063143248970638129863 5979094714873455957194795)
            ·
              refine ⟨8968642072310183935792193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979094714873455957194795 8968642072310183935792193)
              ·
                refine ⟨6726481554232637951844145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8968642072310183935792193 6726481554232637951844145)
                ·
                  refine ⟨5044861165674478463883109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6726481554232637951844145 5044861165674478463883109)
                  ·
                    refine ⟨945911468563964711978083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044861165674478463883109 945911468563964711978083)
                    ·
                      rfl

theorem cell22_2763234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2763234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763234 prefixEnd_2763234 := by exact prefixLift 2763234
  have htrace : WordTrace (prefixWord ++ tailWord_2763234) baseStart_2763234 baseEnd_2763234 := by
    simpa [prefixWord, tailWord_2763234, baseEnd_2763234] using wordTrace_append hprefix tailTrace_2763234
  have hstable : (prefixWord ++ tailWord_2763234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763234).length < 2 ^ (prefixWord ++ tailWord_2763234).sum := by decide
  have hdescent : baseEnd_2763234 < baseStart_2763234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763243 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 5]
def baseStart_2763243 : Nat := 118140960795 + 2763243 * 2 ^ 59
def prefixEnd_2763243 : Nat := 4983230072969 + 3 ^ 40 * 2763243 * 2
def baseEnd_2763243 : Nat := 315304849815963896167685

theorem tailTrace_2763243 : CollatzResearch.WordTrace tailWord_2763243 prefixEnd_2763243 315304849815963896167685 := by
  unfold tailWord_2763243
  simp only [CollatzResearch.WordTrace]
  refine ⟨100783751928250010177694383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67189167952166673451796255 100783751928250010177694383)
  ·
    refine ⟨151175627892375015266541575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100783751928250010177694383 151175627892375015266541575)
    ·
      refine ⟨226763441838562522899812363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151175627892375015266541575 226763441838562522899812363)
      ·
        refine ⟨340145162757843784349718545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226763441838562522899812363 340145162757843784349718545)
        ·
          refine ⟨255108872068382838262288909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340145162757843784349718545 255108872068382838262288909)
          ·
            refine ⟨95665827025643564348358341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255108872068382838262288909 95665827025643564348358341)
            ·
              refine ⟨17937342567308168315317189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95665827025643564348358341 17937342567308168315317189)
              ·
                refine ⟨3363251731370281559121973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17937342567308168315317189 3363251731370281559121973)
                ·
                  refine ⟨315304849815963896167685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363251731370281559121973 315304849815963896167685)
                  ·
                    rfl

theorem cell22_2763243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].length) (baseStart_2763243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763243 prefixEnd_2763243 := by exact prefixLift 2763243
  have htrace : WordTrace (prefixWord ++ tailWord_2763243) baseStart_2763243 baseEnd_2763243 := by
    simpa [prefixWord, tailWord_2763243, baseEnd_2763243] using wordTrace_append hprefix tailTrace_2763243
  have hstable : (prefixWord ++ tailWord_2763243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763243).length < 2 ^ (prefixWord ++ tailWord_2763243).sum := by decide
  have hdescent : baseEnd_2763243 < baseStart_2763243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763253 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2763253 : Nat := 118140960795 + 2763253 * 2 ^ 59
def prefixEnd_2763253 : Nat := 4983230072969 + 3 ^ 40 * 2763253 * 2
def baseEnd_2763253 : Nat := 945917972652254995753025

theorem tailTrace_2763253 : CollatzResearch.WordTrace tailWord_2763253 prefixEnd_2763253 945917972652254995753025 := by
  unfold tailWord_2763253
  simp only [CollatzResearch.WordTrace]
  refine ⟨100784116658213781885558413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67189411105475854590372275 100784116658213781885558413)
  ·
    refine ⟨37794043746830168207084405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100784116658213781885558413 37794043746830168207084405)
    ·
      refine ⟨3543191601265328269414163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37794043746830168207084405 3543191601265328269414163)
      ·
        refine ⟨5314787401897992404121245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543191601265328269414163 5314787401897992404121245)
        ·
          refine ⟨1993045275711747151545467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5314787401897992404121245 1993045275711747151545467)
          ·
            refine ⟨2989567913567620727318201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993045275711747151545467 2989567913567620727318201)
            ·
              refine ⟨2242175935175715545488651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989567913567620727318201 2242175935175715545488651)
              ·
                refine ⟨3363263902763573318232977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242175935175715545488651 3363263902763573318232977)
                ·
                  refine ⟨2522447927072679988674733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363263902763573318232977 2522447927072679988674733)
                  ·
                    refine ⟨945917972652254995753025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522447927072679988674733 945917972652254995753025)
                    ·
                      rfl

theorem cell22_2763253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2763253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763253 prefixEnd_2763253 := by exact prefixLift 2763253
  have htrace : WordTrace (prefixWord ++ tailWord_2763253) baseStart_2763253 baseEnd_2763253 := by
    simpa [prefixWord, tailWord_2763253, baseEnd_2763253] using wordTrace_append hprefix tailTrace_2763253
  have hstable : (prefixWord ++ tailWord_2763253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763253).length < 2 ^ (prefixWord ++ tailWord_2763253).sum := by decide
  have hdescent : baseEnd_2763253 < baseStart_2763253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763290 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_2763290 : Nat := 118140960795 + 2763290 * 2 ^ 59
def prefixEnd_2763290 : Nat := 4983230072969 + 3 ^ 40 * 2763290 * 2
def baseEnd_2763290 : Nat := 945930638508399232577911

theorem tailTrace_2763290 : CollatzResearch.WordTrace tailWord_2763290 prefixEnd_2763290 945930638508399232577911 := by
  unfold tailWord_2763290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25196366539769934301163831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67190310772719824803103549 25196366539769934301163831)
  ·
    refine ⟨37794549809654901451745747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25196366539769934301163831 37794549809654901451745747)
    ·
      refine ⟨56691824714482352177618621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37794549809654901451745747 56691824714482352177618621)
      ·
        refine ⟨21259434267930882066606983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56691824714482352177618621 21259434267930882066606983)
        ·
          refine ⟨31889151401896323099910475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21259434267930882066606983 31889151401896323099910475)
          ·
            refine ⟨47833727102844484649865713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31889151401896323099910475 47833727102844484649865713)
            ·
              refine ⟨35875295327133363487399285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47833727102844484649865713 35875295327133363487399285)
              ·
                refine ⟨3363308936918752826943683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35875295327133363487399285 3363308936918752826943683)
                ·
                  refine ⟨5044963405378129240415525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363308936918752826943683 5044963405378129240415525)
                  ·
                    refine ⟨945930638508399232577911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044963405378129240415525 945930638508399232577911)
                    ·
                      rfl

theorem cell22_2763290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_2763290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763290 prefixEnd_2763290 := by exact prefixLift 2763290
  have htrace : WordTrace (prefixWord ++ tailWord_2763290) baseStart_2763290 baseEnd_2763290 := by
    simpa [prefixWord, tailWord_2763290, baseEnd_2763290] using wordTrace_append hprefix tailTrace_2763290
  have hstable : (prefixWord ++ tailWord_2763290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763290).length < 2 ^ (prefixWord ++ tailWord_2763290).sum := by decide
  have hdescent : baseEnd_2763290 < baseStart_2763290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763320 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_2763320 : Nat := 118140960795 + 2763320 * 2 ^ 59
def prefixEnd_2763320 : Nat := 4983230072969 + 3 ^ 40 * 2763320 * 2
def baseEnd_2763320 : Nat := 945940908121489154327819

theorem tailTrace_2763320 : CollatzResearch.WordTrace tailWord_2763320 prefixEnd_2763320 945940908121489154327819 := by
  unfold tailWord_2763320
  simp only [CollatzResearch.WordTrace]
  refine ⟨50393280174485526164123707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67191040232647368218831609 50393280174485526164123707)
  ·
    refine ⟨75589920261728289246185561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50393280174485526164123707 75589920261728289246185561)
    ·
      refine ⟨56692440196296216934639171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75589920261728289246185561 56692440196296216934639171)
      ·
        refine ⟨85038660294444325401958757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56692440196296216934639171 85038660294444325401958757)
        ·
          refine ⟨15944748805208311012867267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85038660294444325401958757 15944748805208311012867267)
          ·
            refine ⟨23917123207812466519300901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15944748805208311012867267 23917123207812466519300901)
            ·
              refine ⟨4484460601464837472368919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23917123207812466519300901 4484460601464837472368919)
              ·
                refine ⟨6726690902197256208553379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484460601464837472368919 6726690902197256208553379)
                ·
                  refine ⟨10090036353295884312830069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6726690902197256208553379 10090036353295884312830069)
                  ·
                    refine ⟨945940908121489154327819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10090036353295884312830069 945940908121489154327819)
                    ·
                      rfl

theorem cell22_2763320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_2763320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763320 prefixEnd_2763320 := by exact prefixLift 2763320
  have htrace : WordTrace (prefixWord ++ tailWord_2763320) baseStart_2763320 baseEnd_2763320 := by
    simpa [prefixWord, tailWord_2763320, baseEnd_2763320] using wordTrace_append hprefix tailTrace_2763320
  have hstable : (prefixWord ++ tailWord_2763320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763320).length < 2 ^ (prefixWord ++ tailWord_2763320).sum := by decide
  have hdescent : baseEnd_2763320 < baseStart_2763320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763335 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2763335 : Nat := 118140960795 + 2763335 * 2 ^ 59
def prefixEnd_2763335 : Nat := 4983230072969 + 3 ^ 40 * 2763335 * 2
def baseEnd_2763335 : Nat := 945946042928034115202773

theorem tailTrace_2763335 : CollatzResearch.WordTrace tailWord_2763335 prefixEnd_2763335 945946042928034115202773 := by
  unfold tailWord_2763335
  simp only [CollatzResearch.WordTrace]
  refine ⟨100787107443916709890043459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67191404962611139926695639 100787107443916709890043459)
  ·
    refine ⟨151180661165875064835065189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100787107443916709890043459 151180661165875064835065189)
    ·
      refine ⟨28346373968601574656574723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151180661165875064835065189 28346373968601574656574723)
      ·
        refine ⟨42519560952902361984862085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28346373968601574656574723 42519560952902361984862085)
        ·
          refine ⟨7972417678669192872161641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42519560952902361984862085 7972417678669192872161641)
          ·
            refine ⟨5979313259001894654121231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972417678669192872161641 5979313259001894654121231)
            ·
              refine ⟨8968969888502841981181847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979313259001894654121231 8968969888502841981181847)
              ·
                refine ⟨13453454832754262971772771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968969888502841981181847 13453454832754262971772771)
                ·
                  refine ⟨20180182249131394457659157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13453454832754262971772771 20180182249131394457659157)
                  ·
                    refine ⟨945946042928034115202773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20180182249131394457659157 945946042928034115202773)
                    ·
                      rfl

theorem cell22_2763335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2763335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763335 prefixEnd_2763335 := by exact prefixLift 2763335
  have htrace : WordTrace (prefixWord ++ tailWord_2763335) baseStart_2763335 baseEnd_2763335 := by
    simpa [prefixWord, tailWord_2763335, baseEnd_2763335] using wordTrace_append hprefix tailTrace_2763335
  have hstable : (prefixWord ++ tailWord_2763335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763335).length < 2 ^ (prefixWord ++ tailWord_2763335).sum := by decide
  have hdescent : baseEnd_2763335 < baseStart_2763335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763341 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_2763341 : Nat := 118140960795 + 2763341 * 2 ^ 59
def prefixEnd_2763341 : Nat := 4983230072969 + 3 ^ 40 * 2763341 * 2
def baseEnd_2763341 : Nat := 945948096850652099552755

theorem tailTrace_2763341 : CollatzResearch.WordTrace tailWord_2763341 prefixEnd_2763341 945948096850652099552755 := by
  unfold tailWord_2763341
  simp only [CollatzResearch.WordTrace]
  refine ⟨100787326281894972914761877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67191550854596648609841251 100787326281894972914761877)
  ·
    refine ⟨4724405919463826855379463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100787326281894972914761877 4724405919463826855379463)
    ·
      refine ⟨7086608879195740283069195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4724405919463826855379463 7086608879195740283069195)
      ·
        refine ⟨10629913318793610424603793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086608879195740283069195 10629913318793610424603793)
        ·
          refine ⟨7972434989095207818452845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10629913318793610424603793 7972434989095207818452845)
          ·
            refine ⟨2989663120910702931919817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7972434989095207818452845 2989663120910702931919817)
            ·
              refine ⟨2242247340683027198939863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989663120910702931919817 2242247340683027198939863)
              ·
                refine ⟨3363371011024540798409795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242247340683027198939863 3363371011024540798409795)
                ·
                  refine ⟨5045056516536811197614693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363371011024540798409795 5045056516536811197614693)
                  ·
                    refine ⟨945948096850652099552755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045056516536811197614693 945948096850652099552755)
                    ·
                      rfl

theorem cell22_2763341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_2763341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763341 prefixEnd_2763341 := by exact prefixLift 2763341
  have htrace : WordTrace (prefixWord ++ tailWord_2763341) baseStart_2763341 baseEnd_2763341 := by
    simpa [prefixWord, tailWord_2763341, baseEnd_2763341] using wordTrace_append hprefix tailTrace_2763341
  have hstable : (prefixWord ++ tailWord_2763341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763341).length < 2 ^ (prefixWord ++ tailWord_2763341).sum := by decide
  have hdescent : baseEnd_2763341 < baseStart_2763341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763412 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2763412 : Nat := 118140960795 + 2763412 * 2 ^ 59
def prefixEnd_2763412 : Nat := 4983230072969 + 3 ^ 40 * 2763412 * 2
def baseEnd_2763412 : Nat := 315324133867210527009179

theorem tailTrace_2763412 : CollatzResearch.WordTrace tailWord_2763412 prefixEnd_2763412 315324133867210527009179 := by
  unfold tailWord_2763412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50394957932318876020298245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67193277243091834693730993 50394957932318876020298245)
  ·
    refine ⟨9449054612309789253805921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50394957932318876020298245 9449054612309789253805921)
    ·
      refine ⟨7086790959232341940354441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9449054612309789253805921 7086790959232341940354441)
      ·
        refine ⟨5315093219424256455265831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7086790959232341940354441 5315093219424256455265831)
        ·
          refine ⟨7972639829136384682898747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315093219424256455265831 7972639829136384682898747)
          ·
            refine ⟨11958959743704577024348121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972639829136384682898747 11958959743704577024348121)
            ·
              refine ⟨8969219807778432768261091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11958959743704577024348121 8969219807778432768261091)
              ·
                refine ⟨13453829711667649152391637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8969219807778432768261091 13453829711667649152391637)
                ·
                  refine ⟨315324133867210527009179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13453829711667649152391637 315324133867210527009179)
                  ·
                    rfl

theorem cell22_2763412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2763412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763412 prefixEnd_2763412 := by exact prefixLift 2763412
  have htrace : WordTrace (prefixWord ++ tailWord_2763412) baseStart_2763412 baseEnd_2763412 := by
    simpa [prefixWord, tailWord_2763412, baseEnd_2763412] using wordTrace_append hprefix tailTrace_2763412
  have hstable : (prefixWord ++ tailWord_2763412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763412).length < 2 ^ (prefixWord ++ tailWord_2763412).sum := by decide
  have hdescent : baseEnd_2763412 < baseStart_2763412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763416 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_2763416 : Nat := 118140960795 + 2763416 * 2 ^ 59
def prefixEnd_2763416 : Nat := 4983230072969 + 3 ^ 40 * 2763416 * 2
def baseEnd_2763416 : Nat := 945973770883376903927525

theorem tailTrace_2763416 : CollatzResearch.WordTrace tailWord_2763416 prefixEnd_2763416 945973770883376903927525 := by
  unfold tailWord_2763416
  simp only [CollatzResearch.WordTrace]
  refine ⟨50395030878311630361871051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67193374504415507149161401 50395030878311630361871051)
  ·
    refine ⟨75592546317467445542806577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50395030878311630361871051 75592546317467445542806577)
    ·
      refine ⟨56694409738100584157104933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75592546317467445542806577 56694409738100584157104933)
      ·
        refine ⟨10630201825893859529457175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56694409738100584157104933 10630201825893859529457175)
        ·
          refine ⟨15945302738840789294185763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10630201825893859529457175 15945302738840789294185763)
          ·
            refine ⟨23917954108261183941278645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15945302738840789294185763 23917954108261183941278645)
            ·
              refine ⟨2242308197649485994494873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23917954108261183941278645 2242308197649485994494873)
              ·
                refine ⟨1681731148237114495871155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242308197649485994494873 1681731148237114495871155)
                ·
                  refine ⟨2522596722355671743806733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681731148237114495871155 2522596722355671743806733)
                  ·
                    refine ⟨945973770883376903927525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522596722355671743806733 945973770883376903927525)
                    ·
                      rfl

theorem cell22_2763416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_2763416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763416 prefixEnd_2763416 := by exact prefixLift 2763416
  have htrace : WordTrace (prefixWord ++ tailWord_2763416) baseStart_2763416 baseEnd_2763416 := by
    simpa [prefixWord, tailWord_2763416, baseEnd_2763416] using wordTrace_append hprefix tailTrace_2763416
  have hstable : (prefixWord ++ tailWord_2763416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763416).length < 2 ^ (prefixWord ++ tailWord_2763416).sum := by decide
  have hdescent : baseEnd_2763416 < baseStart_2763416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763455 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2763455 : Nat := 118140960795 + 2763455 * 2 ^ 59
def prefixEnd_2763455 : Nat := 4983230072969 + 3 ^ 40 * 2763455 * 2
def baseEnd_2763455 : Nat := 945987121380393802202405

theorem tailTrace_2763455 : CollatzResearch.WordTrace tailWord_2763455 prefixEnd_2763455 945987121380393802202405 := by
  unfold tailWord_2763455
  simp only [CollatzResearch.WordTrace]
  refine ⟨100791484203481970384411819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67194322802321313589607879 100791484203481970384411819)
  ·
    refine ⟨151187226305222955576617729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100791484203481970384411819 151187226305222955576617729)
    ·
      refine ⟨113390419728917216682463297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151187226305222955576617729 113390419728917216682463297)
      ·
        refine ⟨85042814796687912511847473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113390419728917216682463297 85042814796687912511847473)
        ·
          refine ⟨63782111097515934383885605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85042814796687912511847473 63782111097515934383885605)
          ·
            refine ⟨11959145830784237696978551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63782111097515934383885605 11959145830784237696978551)
            ·
              refine ⟨17938718746176356545467827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959145830784237696978551 17938718746176356545467827)
              ·
                refine ⟨26908078119264534818201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17938718746176356545467827 26908078119264534818201741)
                ·
                  refine ⟨10090529294724200556825653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26908078119264534818201741 10090529294724200556825653)
                  ·
                    refine ⟨945987121380393802202405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10090529294724200556825653 945987121380393802202405)
                    ·
                      rfl

theorem cell22_2763455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2763455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763455 prefixEnd_2763455 := by exact prefixLift 2763455
  have htrace : WordTrace (prefixWord ++ tailWord_2763455) baseStart_2763455 baseEnd_2763455 := by
    simpa [prefixWord, tailWord_2763455, baseEnd_2763455] using wordTrace_append hprefix tailTrace_2763455
  have hstable : (prefixWord ++ tailWord_2763455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763455).length < 2 ^ (prefixWord ++ tailWord_2763455).sum := by decide
  have hdescent : baseEnd_2763455 < baseStart_2763455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763489 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2763489 : Nat := 118140960795 + 2763489 * 2 ^ 59
def prefixEnd_2763489 : Nat := 4983230072969 + 3 ^ 40 * 2763489 * 2
def baseEnd_2763489 : Nat := 945998760275229046852301

theorem tailTrace_2763489 : CollatzResearch.WordTrace tailWord_2763489 prefixEnd_2763489 945998760275229046852301 := by
  unfold tailWord_2763489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100792724285358794191149521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67195149523572529460766347 100792724285358794191149521)
  ·
    refine ⟨75594543214019095643362141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100792724285358794191149521 75594543214019095643362141)
    ·
      refine ⟨28347953705257160866260803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75594543214019095643362141 28347953705257160866260803)
      ·
        refine ⟨42521930557885741299391205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28347953705257160866260803 42521930557885741299391205)
        ·
          refine ⟨7972861979603576493635851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42521930557885741299391205 7972861979603576493635851)
          ·
            refine ⟨11959292969405364740453777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972861979603576493635851 11959292969405364740453777)
            ·
              refine ⟨8969469727054023555340333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11959292969405364740453777 8969469727054023555340333)
              ·
                refine ⟨3363551147645258833252625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8969469727054023555340333 3363551147645258833252625)
                ·
                  refine ⟨2522663360733944124939469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363551147645258833252625 2522663360733944124939469)
                  ·
                    refine ⟨945998760275229046852301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522663360733944124939469 945998760275229046852301)
                    ·
                      rfl

theorem cell22_2763489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2763489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763489 prefixEnd_2763489 := by exact prefixLift 2763489
  have htrace : WordTrace (prefixWord ++ tailWord_2763489) baseStart_2763489 baseEnd_2763489 := by
    simpa [prefixWord, tailWord_2763489, baseEnd_2763489] using wordTrace_append hprefix tailTrace_2763489
  have hstable : (prefixWord ++ tailWord_2763489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763489).length < 2 ^ (prefixWord ++ tailWord_2763489).sum := by decide
  have hdescent : baseEnd_2763489 < baseStart_2763489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763517 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2763517 : Nat := 118140960795 + 2763517 * 2 ^ 59
def prefixEnd_2763517 : Nat := 4983230072969 + 3 ^ 40 * 2763517 * 2
def baseEnd_2763517 : Nat := 946008345247446307152215

theorem tailTrace_2763517 : CollatzResearch.WordTrace tailWord_2763517 prefixEnd_2763517 946008345247446307152215 := by
  unfold tailWord_2763517
  simp only [CollatzResearch.WordTrace]
  refine ⟨100793745529257354973168805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67195830352838236648779203 100793745529257354973168805)
  ·
    refine ⟨18898827286735754057469151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100793745529257354973168805 18898827286735754057469151)
    ·
      refine ⟨28348240930103631086203727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18898827286735754057469151 28348240930103631086203727)
      ·
        refine ⟨42522361395155446629305591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28348240930103631086203727 42522361395155446629305591)
        ·
          refine ⟨63783542092733169943958387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42522361395155446629305591 63783542092733169943958387)
          ·
            refine ⟨95675313139099754915937581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63783542092733169943958387 95675313139099754915937581)
            ·
              refine ⟨35878242427162408093476593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95675313139099754915937581 35878242427162408093476593)
              ·
                refine ⟨26908681820371806070107445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35878242427162408093476593 26908681820371806070107445)
                ·
                  refine ⟨2522688920659856819072573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26908681820371806070107445 2522688920659856819072573)
                  ·
                    refine ⟨946008345247446307152215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522688920659856819072573 946008345247446307152215)
                    ·
                      rfl

theorem cell22_2763517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2763517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763517 prefixEnd_2763517 := by exact prefixLift 2763517
  have htrace : WordTrace (prefixWord ++ tailWord_2763517) baseStart_2763517 baseEnd_2763517 := by
    simpa [prefixWord, tailWord_2763517, baseEnd_2763517] using wordTrace_append hprefix tailTrace_2763517
  have hstable : (prefixWord ++ tailWord_2763517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763517).length < 2 ^ (prefixWord ++ tailWord_2763517).sum := by decide
  have hdescent : baseEnd_2763517 < baseStart_2763517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763545 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2763545 : Nat := 118140960795 + 2763545 * 2 ^ 59
def prefixEnd_2763545 : Nat := 4983230072969 + 3 ^ 40 * 2763545 * 2
def baseEnd_2763545 : Nat := 946017930219663567452129

theorem tailTrace_2763545 : CollatzResearch.WordTrace tailWord_2763545 prefixEnd_2763545 946017930219663567452129 := by
  unfold tailWord_2763545
  simp only [CollatzResearch.WordTrace]
  refine ⟨100794766773155915755188089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67196511182103943836792059 100794766773155915755188089)
  ·
    refine ⟨75596075079866936816391067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100794766773155915755188089 75596075079866936816391067)
    ·
      refine ⟨113394112619800405224586601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75596075079866936816391067 113394112619800405224586601)
      ·
        refine ⟨85045584464850303918439951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113394112619800405224586601 85045584464850303918439951)
        ·
          refine ⟨127568376697275455877659927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85045584464850303918439951 127568376697275455877659927)
          ·
            refine ⟨191352565045913183816489891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127568376697275455877659927 191352565045913183816489891)
            ·
              refine ⟨287028847568869775724734837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191352565045913183816489891 287028847568869775724734837)
              ·
                refine ⟨26908954459581541474193891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287028847568869775724734837 26908954459581541474193891)
                ·
                  refine ⟨40363431689372312211290837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26908954459581541474193891 40363431689372312211290837)
                  ·
                    refine ⟨946017930219663567452129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40363431689372312211290837 946017930219663567452129)
                    ·
                      rfl

theorem cell22_2763545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2763545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763545 prefixEnd_2763545 := by exact prefixLift 2763545
  have htrace : WordTrace (prefixWord ++ tailWord_2763545) baseStart_2763545 baseEnd_2763545 := by
    simpa [prefixWord, tailWord_2763545, baseEnd_2763545] using wordTrace_append hprefix tailTrace_2763545
  have hstable : (prefixWord ++ tailWord_2763545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763545).length < 2 ^ (prefixWord ++ tailWord_2763545).sum := by decide
  have hdescent : baseEnd_2763545 < baseStart_2763545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763585 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2763585 : Nat := 118140960795 + 2763585 * 2 ^ 59
def prefixEnd_2763585 : Nat := 4983230072969 + 3 ^ 40 * 2763585 * 2
def baseEnd_2763585 : Nat := 946031623037116796452007

theorem tailTrace_2763585 : CollatzResearch.WordTrace tailWord_2763585 prefixEnd_2763585 946031623037116796452007 := by
  unfold tailWord_2763585
  simp only [CollatzResearch.WordTrace]
  refine ⟨100796225693011002586644209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67197483795340668391096139 100796225693011002586644209)
  ·
    refine ⟨75597169269758251939983157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100796225693011002586644209 75597169269758251939983157)
    ·
      refine ⟨7087234619039836119373421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75597169269758251939983157 7087234619039836119373421)
      ·
        refine ⟨2657712982139938544765033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7087234619039836119373421 2657712982139938544765033)
        ·
          refine ⟨1993284736604953908573775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657712982139938544765033 1993284736604953908573775)
          ·
            refine ⟨2989927104907430862860663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993284736604953908573775 2989927104907430862860663)
            ·
              refine ⟨4484890657361146294290995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989927104907430862860663 4484890657361146294290995)
              ·
                refine ⟨6727335986041719441436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484890657361146294290995 6727335986041719441436493)
                ·
                  refine ⟨2522750994765644790538685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6727335986041719441436493 2522750994765644790538685)
                  ·
                    refine ⟨946031623037116796452007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522750994765644790538685 946031623037116796452007)
                    ·
                      rfl

theorem cell22_2763585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2763585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763585 prefixEnd_2763585 := by exact prefixLift 2763585
  have htrace : WordTrace (prefixWord ++ tailWord_2763585) baseStart_2763585 baseEnd_2763585 := by
    simpa [prefixWord, tailWord_2763585, baseEnd_2763585] using wordTrace_append hprefix tailTrace_2763585
  have hstable : (prefixWord ++ tailWord_2763585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763585).length < 2 ^ (prefixWord ++ tailWord_2763585).sum := by decide
  have hdescent : baseEnd_2763585 < baseStart_2763585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763624 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2763624 : Nat := 118140960795 + 2763624 * 2 ^ 59
def prefixEnd_2763624 : Nat := 4983230072969 + 3 ^ 40 * 2763624 * 2
def baseEnd_2763624 : Nat := 946044973534133694726887

theorem tailTrace_2763624 : CollatzResearch.WordTrace tailWord_2763624 prefixEnd_2763624 946044973534133694726887 := by
  unfold tailWord_2763624
  simp only [CollatzResearch.WordTrace]
  refine ⟨50398824069934856123656963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67198432093246474831542617 50398824069934856123656963)
  ·
    refine ⟨75598236104902284185485445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50398824069934856123656963 75598236104902284185485445)
    ·
      refine ⟨14174669269669178284778521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75598236104902284185485445 14174669269669178284778521)
      ·
        refine ⟨10631001952251883713583891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14174669269669178284778521 10631001952251883713583891)
        ·
          refine ⟨15946502928377825570375837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631001952251883713583891 15946502928377825570375837)
          ·
            refine ⟨5979938598141684588890939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15946502928377825570375837 5979938598141684588890939)
            ·
              refine ⟨8969907897212526883336409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979938598141684588890939 8969907897212526883336409)
              ·
                refine ⟨6727430922909395162502307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969907897212526883336409 6727430922909395162502307)
                ·
                  refine ⟨10091146384364092743753461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727430922909395162502307 10091146384364092743753461)
                  ·
                    refine ⟨946044973534133694726887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10091146384364092743753461 946044973534133694726887)
                    ·
                      rfl

theorem cell22_2763624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2763624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763624 prefixEnd_2763624 := by exact prefixLift 2763624
  have htrace : WordTrace (prefixWord ++ tailWord_2763624) baseStart_2763624 baseEnd_2763624 := by
    simpa [prefixWord, tailWord_2763624, baseEnd_2763624] using wordTrace_append hprefix tailTrace_2763624
  have hstable : (prefixWord ++ tailWord_2763624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763624).length < 2 ^ (prefixWord ++ tailWord_2763624).sum := by decide
  have hdescent : baseEnd_2763624 < baseStart_2763624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763637 : List Nat := [1, 3, 4, 1, 1, 12]
def baseStart_2763637 : Nat := 118140960795 + 2763637 * 2 ^ 59
def prefixEnd_2763637 : Nat := 4983230072969 + 3 ^ 40 * 2763637 * 2
def baseEnd_2763637 : Nat := 11679622514812419680887

theorem tailTrace_2763637 : CollatzResearch.WordTrace tailWord_2763637 prefixEnd_2763637 11679622514812419680887 := by
  unfold tailWord_2763637
  simp only [CollatzResearch.WordTrace]
  refine ⟨100798122288822615467537165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67198748192548410311691443 100798122288822615467537165)
  ·
    refine ⟨37799295858308480800326437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100798122288822615467537165 37799295858308480800326437)
    ·
      refine ⟨7087367973432840150061207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37799295858308480800326437 7087367973432840150061207)
      ·
        refine ⟨10631051960149260225091811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087367973432840150061207 10631051960149260225091811)
        ·
          refine ⟨15946577940223890337637717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631051960149260225091811 15946577940223890337637717)
          ·
            refine ⟨11679622514812419680887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15946577940223890337637717 11679622514812419680887)
            ·
              rfl

theorem cell22_2763637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 12].length) (baseStart_2763637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763637 prefixEnd_2763637 := by exact prefixLift 2763637
  have htrace : WordTrace (prefixWord ++ tailWord_2763637) baseStart_2763637 baseEnd_2763637 := by
    simpa [prefixWord, tailWord_2763637, baseEnd_2763637] using wordTrace_append hprefix tailTrace_2763637
  have hstable : (prefixWord ++ tailWord_2763637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763637).length < 2 ^ (prefixWord ++ tailWord_2763637).sum := by decide
  have hdescent : baseEnd_2763637 < baseStart_2763637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763641 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_2763641 : Nat := 118140960795 + 2763641 * 2 ^ 59
def prefixEnd_2763641 : Nat := 4983230072969 + 3 ^ 40 * 2763641 * 2
def baseEnd_2763641 : Nat := 946050792981551317051835

theorem tailTrace_2763641 : CollatzResearch.WordTrace tailWord_2763641 prefixEnd_2763641 946050792981551317051835 := by
  unfold tailWord_2763641
  simp only [CollatzResearch.WordTrace]
  refine ⟨100798268180808124150682777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67198845453872082767121851 100798268180808124150682777)
  ·
    refine ⟨75598701135606093113012083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100798268180808124150682777 75598701135606093113012083)
    ·
      refine ⟨113398051703409139669518125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75598701135606093113012083 113398051703409139669518125)
      ·
        refine ⟨42524269388778427376069297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113398051703409139669518125 42524269388778427376069297)
        ·
          refine ⟨31893202041583820532051973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42524269388778427376069297 31893202041583820532051973)
          ·
            refine ⟨5979975382796966349759745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31893202041583820532051973 5979975382796966349759745)
            ·
              refine ⟨4484981537097724762319809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5979975382796966349759745 4484981537097724762319809)
              ·
                refine ⟨3363736152823293571739857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4484981537097724762319809 3363736152823293571739857)
                ·
                  refine ⟨2522802114617470178804893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3363736152823293571739857 2522802114617470178804893)
                  ·
                    refine ⟨946050792981551317051835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522802114617470178804893 946050792981551317051835)
                    ·
                      rfl

theorem cell22_2763641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_2763641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763641 prefixEnd_2763641 := by exact prefixLift 2763641
  have htrace : WordTrace (prefixWord ++ tailWord_2763641) baseStart_2763641 baseEnd_2763641 := by
    simpa [prefixWord, tailWord_2763641, baseEnd_2763641] using wordTrace_append hprefix tailTrace_2763641
  have hstable : (prefixWord ++ tailWord_2763641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763641).length < 2 ^ (prefixWord ++ tailWord_2763641).sum := by decide
  have hdescent : baseEnd_2763641 < baseStart_2763641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763652 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2763652 : Nat := 118140960795 + 2763652 * 2 ^ 59
def prefixEnd_2763652 : Nat := 4983230072969 + 3 ^ 40 * 2763652 * 2
def baseEnd_2763652 : Nat := 946054558506350955026801

theorem tailTrace_2763652 : CollatzResearch.WordTrace tailWord_2763652 prefixEnd_2763652 946054558506350955026801 := by
  unfold tailWord_2763652
  simp only [CollatzResearch.WordTrace]
  refine ⟨50399334691884136514666605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67199112922512182019555473 50399334691884136514666605)
  ·
    refine ⟨18899750509456551192999977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50399334691884136514666605 18899750509456551192999977)
    ·
      refine ⟨14174812882092413394749983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18899750509456551192999977 14174812882092413394749983)
      ·
        refine ⟨21262219323138620092124975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14174812882092413394749983 21262219323138620092124975)
        ·
          refine ⟨31893328984707930138187463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21262219323138620092124975 31893328984707930138187463)
          ·
            refine ⟨47839993477061895207281195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31893328984707930138187463 47839993477061895207281195)
            ·
              refine ⟨71759990215592842810921793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47839993477061895207281195 71759990215592842810921793)
              ·
                refine ⟨53819992661694632108191345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71759990215592842810921793 53819992661694632108191345)
                ·
                  refine ⟨40364994496270974081143509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53819992661694632108191345 40364994496270974081143509)
                  ·
                    refine ⟨946054558506350955026801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40364994496270974081143509 946054558506350955026801)
                    ·
                      rfl

theorem cell22_2763652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2763652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763652 prefixEnd_2763652 := by exact prefixLift 2763652
  have htrace : WordTrace (prefixWord ++ tailWord_2763652) baseStart_2763652 baseEnd_2763652 := by
    simpa [prefixWord, tailWord_2763652, baseEnd_2763652] using wordTrace_append hprefix tailTrace_2763652
  have hstable : (prefixWord ++ tailWord_2763652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763652).length < 2 ^ (prefixWord ++ tailWord_2763652).sum := by decide
  have hdescent : baseEnd_2763652 < baseStart_2763652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763669 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_2763669 : Nat := 118140960795 + 2763669 * 2 ^ 59
def prefixEnd_2763669 : Nat := 4983230072969 + 3 ^ 40 * 2763669 * 2
def baseEnd_2763669 : Nat := 946060377953768577351749

theorem tailTrace_2763669 : CollatzResearch.WordTrace tailWord_2763669 prefixEnd_2763669 946060377953768577351749 := by
  unfold tailWord_2763669
  simp only [CollatzResearch.WordTrace]
  refine ⟨100799289424706684932702061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67199526283137789955134707 100799289424706684932702061)
  ·
    refine ⟨37799733534265006849763273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100799289424706684932702061 37799733534265006849763273)
    ·
      refine ⟨28349800150698755137322455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37799733534265006849763273 28349800150698755137322455)
      ·
        refine ⟨42524700226048132705983683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28349800150698755137322455 42524700226048132705983683)
        ·
          refine ⟨63787050339072199058975525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42524700226048132705983683 63787050339072199058975525)
          ·
            refine ⟨11960071938576037323557911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63787050339072199058975525 11960071938576037323557911)
            ·
              refine ⟨17940107907864055985336867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960071938576037323557911 17940107907864055985336867)
              ·
                refine ⟨26910161861796083978005301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17940107907864055985336867 26910161861796083978005301)
                ·
                  refine ⟨2522827674543382872937997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26910161861796083978005301 2522827674543382872937997)
                  ·
                    refine ⟨946060377953768577351749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522827674543382872937997 946060377953768577351749)
                    ·
                      rfl

theorem cell22_2763669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_2763669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763669 prefixEnd_2763669 := by exact prefixLift 2763669
  have htrace : WordTrace (prefixWord ++ tailWord_2763669) baseStart_2763669 baseEnd_2763669 := by
    simpa [prefixWord, tailWord_2763669, baseEnd_2763669] using wordTrace_append hprefix tailTrace_2763669
  have hstable : (prefixWord ++ tailWord_2763669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763669).length < 2 ^ (prefixWord ++ tailWord_2763669).sum := by decide
  have hdescent : baseEnd_2763669 < baseStart_2763669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763761 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 6]
def baseStart_2763761 : Nat := 118140960795 + 2763761 * 2 ^ 59
def prefixEnd_2763761 : Nat := 4983230072969 + 3 ^ 40 * 2763761 * 2
def baseEnd_2763761 : Nat := 315363957144637001350489

theorem tailTrace_2763761 : CollatzResearch.WordTrace tailWord_2763761 prefixEnd_2763761 315363957144637001350489 := by
  unfold tailWord_2763761
  simp only [CollatzResearch.WordTrace]
  refine ⟨100802644940373384645051137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67201763293582256430034091 100802644940373384645051137)
  ·
    refine ⟨75601983705280038483788353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100802644940373384645051137 75601983705280038483788353)
    ·
      refine ⟨56701487778960028862841265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75601983705280038483788353 56701487778960028862841265)
      ·
        refine ⟨42526115834220021647130949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56701487778960028862841265 42526115834220021647130949)
        ·
          refine ⟨7973646718916254058837053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42526115834220021647130949 7973646718916254058837053)
          ·
            refine ⟨2990117519593595272063895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7973646718916254058837053 2990117519593595272063895)
            ·
              refine ⟨4485176279390392908095843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990117519593595272063895 4485176279390392908095843)
              ·
                refine ⟨6727764419085589362143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485176279390392908095843 6727764419085589362143765)
                ·
                  refine ⟨315363957144637001350489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6727764419085589362143765 315363957144637001350489)
                  ·
                    rfl

theorem cell22_2763761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_2763761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763761 prefixEnd_2763761 := by exact prefixLift 2763761
  have htrace : WordTrace (prefixWord ++ tailWord_2763761) baseStart_2763761 baseEnd_2763761 := by
    simpa [prefixWord, tailWord_2763761, baseEnd_2763761] using wordTrace_append hprefix tailTrace_2763761
  have hstable : (prefixWord ++ tailWord_2763761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763761).length < 2 ^ (prefixWord ++ tailWord_2763761).sum := by decide
  have hdescent : baseEnd_2763761 < baseStart_2763761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763838 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2763838 : Nat := 118140960795 + 2763838 * 2 ^ 59
def prefixEnd_2763838 : Nat := 4983230072969 + 3 ^ 40 * 2763838 * 2
def baseEnd_2763838 : Nat := 946118230107508469876231

theorem tailTrace_2763838 : CollatzResearch.WordTrace tailWord_2763838 prefixEnd_2763838 946118230107508469876231 := by
  unfold tailWord_2763838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600681670136803349450521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67203635574062951197069445 12600681670136803349450521)
  ·
    refine ⟨9450511252602602512087891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600681670136803349450521 9450511252602602512087891)
    ·
      refine ⟨14175766878903903768131837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450511252602602512087891 14175766878903903768131837)
      ·
        refine ⟨5315912579588963913049439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14175766878903903768131837 5315912579588963913049439)
        ·
          refine ⟨7973868869383445869574159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315912579588963913049439 7973868869383445869574159)
          ·
            refine ⟨11960803304075168804361239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973868869383445869574159 11960803304075168804361239)
            ·
              refine ⟨17941204956112753206541859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960803304075168804361239 17941204956112753206541859)
              ·
                refine ⟨26911807434169129809812789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17941204956112753206541859 26911807434169129809812789)
                ·
                  refine ⟨2522981946953355919669949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26911807434169129809812789 2522981946953355919669949)
                  ·
                    refine ⟨946118230107508469876231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522981946953355919669949 946118230107508469876231)
                    ·
                      rfl

theorem cell22_2763838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2763838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763838 prefixEnd_2763838 := by exact prefixLift 2763838
  have htrace : WordTrace (prefixWord ++ tailWord_2763838) baseStart_2763838 baseEnd_2763838 := by
    simpa [prefixWord, tailWord_2763838, baseEnd_2763838] using wordTrace_append hprefix tailTrace_2763838
  have hstable : (prefixWord ++ tailWord_2763838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763838).length < 2 ^ (prefixWord ++ tailWord_2763838).sum := by decide
  have hdescent : baseEnd_2763838 < baseStart_2763838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763913 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 4]
def baseStart_2763913 : Nat := 118140960795 + 2763913 * 2 ^ 59
def prefixEnd_2763913 : Nat := 4983230072969 + 3 ^ 40 * 2763913 * 2
def baseEnd_2763913 : Nat := 315381301380077758083667

theorem tailTrace_2763913 : CollatzResearch.WordTrace tailWord_2763913 prefixEnd_2763913 315381301380077758083667 := by
  unfold tailWord_2763913
  simp only [CollatzResearch.WordTrace]
  refine ⟨100808188835822714604584393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67205459223881809736389595 100808188835822714604584393)
  ·
    refine ⟨75606141626867035953438295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100808188835822714604584393 75606141626867035953438295)
    ·
      refine ⟨113409212440300553930157443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75606141626867035953438295 113409212440300553930157443)
      ·
        refine ⟨170113818660450830895236165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113409212440300553930157443 170113818660450830895236165)
        ·
          refine ⟨31896340998834530792856781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170113818660450830895236165 31896340998834530792856781)
          ·
            refine ⟨11961127874562949047321293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31896340998834530792856781 11961127874562949047321293)
            ·
              refine ⟨4485422952961105892745485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11961127874562949047321293 4485422952961105892745485)
              ·
                refine ⟨1682033607360414709779557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4485422952961105892745485 1682033607360414709779557)
                ·
                  refine ⟨315381301380077758083667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682033607360414709779557 315381301380077758083667)
                  ·
                    rfl

theorem cell22_2763913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_2763913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763913 prefixEnd_2763913 := by exact prefixLift 2763913
  have htrace : WordTrace (prefixWord ++ tailWord_2763913) baseStart_2763913 baseEnd_2763913 := by
    simpa [prefixWord, tailWord_2763913, baseEnd_2763913] using wordTrace_append hprefix tailTrace_2763913
  have hstable : (prefixWord ++ tailWord_2763913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763913).length < 2 ^ (prefixWord ++ tailWord_2763913).sum := by decide
  have hdescent : baseEnd_2763913 < baseStart_2763913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763928 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_2763928 : Nat := 118140960795 + 2763928 * 2 ^ 59
def prefixEnd_2763928 : Nat := 4983230072969 + 3 ^ 40 * 2763928 * 2
def baseEnd_2763928 : Nat := 946149038946778235125955

theorem tailTrace_2763928 : CollatzResearch.WordTrace tailWord_2763928 prefixEnd_2763928 946149038946778235125955 := by
  unfold tailWord_2763928
  simp only [CollatzResearch.WordTrace]
  refine ⟨50404367965384186083190219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67205823953845581444253625 50404367965384186083190219)
  ·
    refine ⟨75606551948076279124785329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50404367965384186083190219 75606551948076279124785329)
    ·
      refine ⟨56704913961057209343588997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75606551948076279124785329 56704913961057209343588997)
      ·
        refine ⟨10632171367698226751922937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56704913961057209343588997 10632171367698226751922937)
        ·
          refine ⟨7974128525773670063942203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10632171367698226751922937 7974128525773670063942203)
          ·
            refine ⟨11961192788660505095913305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974128525773670063942203 11961192788660505095913305)
            ·
              refine ⟨8970894591495378821934979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11961192788660505095913305 8970894591495378821934979)
              ·
                refine ⟨13456341887243068232902469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970894591495378821934979 13456341887243068232902469)
                ·
                  refine ⟨2523064103858075293669213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13456341887243068232902469 2523064103858075293669213)
                  ·
                    refine ⟨946149038946778235125955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523064103858075293669213 946149038946778235125955)
                    ·
                      rfl

theorem cell22_2763928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_2763928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763928 prefixEnd_2763928 := by exact prefixLift 2763928
  have htrace : WordTrace (prefixWord ++ tailWord_2763928) baseStart_2763928 baseEnd_2763928 := by
    simpa [prefixWord, tailWord_2763928, baseEnd_2763928] using wordTrace_append hprefix tailTrace_2763928
  have hstable : (prefixWord ++ tailWord_2763928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763928).length < 2 ^ (prefixWord ++ tailWord_2763928).sum := by decide
  have hdescent : baseEnd_2763928 < baseStart_2763928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763941 : List Nat := [1, 3, 1, 2, 1, 5, 2, 7]
def baseStart_2763941 : Nat := 118140960795 + 2763941 * 2 ^ 59
def prefixEnd_2763941 : Nat := 4983230072969 + 3 ^ 40 * 2763941 * 2
def baseEnd_2763941 : Nat := 105128165456938948283435

theorem tailTrace_2763941 : CollatzResearch.WordTrace tailWord_2763941 prefixEnd_2763941 105128165456938948283435 := by
  unfold tailWord_2763941
  simp only [CollatzResearch.WordTrace]
  refine ⟨100809210079721275386603677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67206140053147516924402451 100809210079721275386603677)
  ·
    refine ⟨37803453779895478269976379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100809210079721275386603677 37803453779895478269976379)
    ·
      refine ⟨56705180669843217404964569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37803453779895478269976379 56705180669843217404964569)
      ·
        refine ⟨42528885502382413053723427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56705180669843217404964569 42528885502382413053723427)
        ·
          refine ⟨63793328253573619580585141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42528885502382413053723427 63793328253573619580585141)
          ·
            refine ⟨5980624523772526835679857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63793328253573619580585141 5980624523772526835679857)
            ·
              refine ⟨4485468392829395126759893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5980624523772526835679857 4485468392829395126759893)
              ·
                refine ⟨105128165456938948283435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4485468392829395126759893 105128165456938948283435)
                ·
                  rfl

theorem cell22_2763941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 7].length) (baseStart_2763941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763941 prefixEnd_2763941 := by exact prefixLift 2763941
  have htrace : WordTrace (prefixWord ++ tailWord_2763941) baseStart_2763941 baseEnd_2763941 := by
    simpa [prefixWord, tailWord_2763941, baseEnd_2763941] using wordTrace_append hprefix tailTrace_2763941
  have hstable : (prefixWord ++ tailWord_2763941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763941).length < 2 ^ (prefixWord ++ tailWord_2763941).sum := by decide
  have hdescent : baseEnd_2763941 < baseStart_2763941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2763981 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2763981 : Nat := 118140960795 + 2763981 * 2 ^ 59
def prefixEnd_2763981 : Nat := 4983230072969 + 3 ^ 40 * 2763981 * 2
def baseEnd_2763981 : Nat := 315389060643301254516931

theorem tailTrace_2763981 : CollatzResearch.WordTrace tailWord_2763981 prefixEnd_2763981 315389060643301254516931 := by
  unfold tailWord_2763981
  simp only [CollatzResearch.WordTrace]
  refine ⟨100810668999576362218059797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67207112666384241478706531 100810668999576362218059797)
  ·
    refine ⟨4725500109355141978971553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100810668999576362218059797 4725500109355141978971553)
    ·
      refine ⟨3544125082016356484228665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725500109355141978971553 3544125082016356484228665)
      ·
        refine ⟨2658093811512267363171499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3544125082016356484228665 2658093811512267363171499)
        ·
          refine ⟨3987140717268401044757249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658093811512267363171499 3987140717268401044757249)
          ·
            refine ⟨2990355537951300783567937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3987140717268401044757249 2990355537951300783567937)
            ·
              refine ⟨2242766653463475587675953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990355537951300783567937 2242766653463475587675953)
              ·
                refine ⟨1682074990097606690756965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242766653463475587675953 1682074990097606690756965)
                ·
                  refine ⟨315389060643301254516931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682074990097606690756965 315389060643301254516931)
                  ·
                    rfl

theorem cell22_2763981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2763981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2763981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2763981 prefixEnd_2763981 := by exact prefixLift 2763981
  have htrace : WordTrace (prefixWord ++ tailWord_2763981) baseStart_2763981 baseEnd_2763981 := by
    simpa [prefixWord, tailWord_2763981, baseEnd_2763981] using wordTrace_append hprefix tailTrace_2763981
  have hstable : (prefixWord ++ tailWord_2763981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2763981).length < 2 ^ (prefixWord ++ tailWord_2763981).sum := by decide
  have hdescent : baseEnd_2763981 < baseStart_2763981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2763981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764001 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2764001 : Nat := 118140960795 + 2764001 * 2 ^ 59
def prefixEnd_2764001 : Nat := 4983230072969 + 3 ^ 40 * 2764001 * 2
def baseEnd_2764001 : Nat := 946174028338630378050731

theorem tailTrace_2764001 : CollatzResearch.WordTrace tailWord_2764001 prefixEnd_2764001 946174028338630378050731 := by
  unfold tailWord_2764001
  simp only [CollatzResearch.WordTrace]
  refine ⟨100811398459503905633787857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67207598973002603755858571 100811398459503905633787857)
  ·
    refine ⟨75608548844627929225340893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100811398459503905633787857 75608548844627929225340893)
    ·
      refine ⟨28353205816735473459502835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75608548844627929225340893 28353205816735473459502835)
      ·
        refine ⟨42529808725103210189254253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28353205816735473459502835 42529808725103210189254253)
        ·
          refine ⟨15948678271913703820970345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42529808725103210189254253 15948678271913703820970345)
          ·
            refine ⟨11961508703935277865727759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15948678271913703820970345 11961508703935277865727759)
            ·
              refine ⟨17942263055902916798591639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11961508703935277865727759 17942263055902916798591639)
              ·
                refine ⟨26913394583854375197887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17942263055902916798591639 26913394583854375197887459)
                ·
                  refine ⟨40370091875781562796831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26913394583854375197887459 40370091875781562796831189)
                  ·
                    refine ⟨946174028338630378050731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40370091875781562796831189 946174028338630378050731)
                    ·
                      rfl

theorem cell22_2764001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2764001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764001 prefixEnd_2764001 := by exact prefixLift 2764001
  have htrace : WordTrace (prefixWord ++ tailWord_2764001) baseStart_2764001 baseEnd_2764001 := by
    simpa [prefixWord, tailWord_2764001, baseEnd_2764001] using wordTrace_append hprefix tailTrace_2764001
  have hstable : (prefixWord ++ tailWord_2764001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764001).length < 2 ^ (prefixWord ++ tailWord_2764001).sum := by decide
  have hdescent : baseEnd_2764001 < baseStart_2764001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764082 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_2764082 : Nat := 118140960795 + 2764082 * 2 ^ 59
def prefixEnd_2764082 : Nat := 4983230072969 + 3 ^ 40 * 2764082 * 2
def baseEnd_2764082 : Nat := 315400585431324388925161

theorem tailTrace_2764082 : CollatzResearch.WordTrace tailWord_2764082 prefixEnd_2764082 315400585431324388925161 := by
  unfold tailWord_2764082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25203588193052614116871625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67209568514806970978324333 25203588193052614116871625)
  ·
    refine ⟨18902691144789460587653719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25203588193052614116871625 18902691144789460587653719)
    ·
      refine ⟨28354036717184190881480579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18902691144789460587653719 28354036717184190881480579)
      ·
        refine ⟨42531055075776286322220869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28354036717184190881480579 42531055075776286322220869)
        ·
          refine ⟨7974572826708053685416413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42531055075776286322220869 7974572826708053685416413)
          ·
            refine ⟨2990464810015520132031155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7974572826708053685416413 2990464810015520132031155)
            ·
              refine ⟨4485697215023280198046733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990464810015520132031155 4485697215023280198046733)
              ·
                refine ⟨1682136455633730074267525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4485697215023280198046733 1682136455633730074267525)
                ·
                  refine ⟨315400585431324388925161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682136455633730074267525 315400585431324388925161)
                  ·
                    rfl

theorem cell22_2764082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_2764082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764082 prefixEnd_2764082 := by exact prefixLift 2764082
  have htrace : WordTrace (prefixWord ++ tailWord_2764082) baseStart_2764082 baseEnd_2764082 := by
    simpa [prefixWord, tailWord_2764082, baseEnd_2764082] using wordTrace_append hprefix tailTrace_2764082
  have hstable : (prefixWord ++ tailWord_2764082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764082).length < 2 ^ (prefixWord ++ tailWord_2764082).sum := by decide
  have hdescent : baseEnd_2764082 < baseStart_2764082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764118 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2764118 : Nat := 118140960795 + 2764118 * 2 ^ 59
def prefixEnd_2764118 : Nat := 4983230072969 + 3 ^ 40 * 2764118 * 2
def baseEnd_2764118 : Nat := 946214079829681072875373

theorem tailTrace_2764118 : CollatzResearch.WordTrace tailWord_2764118 prefixEnd_2764118 946214079829681072875373 := by
  unfold tailWord_2764118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300979112505002163487313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67210443866720023077198005 6300979112505002163487313)
  ·
    refine ⟨4725734334378751622615485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6300979112505002163487313 4725734334378751622615485)
    ·
      refine ⟨1772150375392031858480807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4725734334378751622615485 1772150375392031858480807)
      ·
        refine ⟨2658225563088047787721211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772150375392031858480807 2658225563088047787721211)
        ·
          refine ⟨3987338344632071681581817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658225563088047787721211 3987338344632071681581817)
          ·
            refine ⟨2990503758474053761186363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3987338344632071681581817 2990503758474053761186363)
            ·
              refine ⟨4485755637711080641779545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990503758474053761186363 4485755637711080641779545)
              ·
                refine ⟨3364316728283310481334659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485755637711080641779545 3364316728283310481334659)
                ·
                  refine ⟨5046475092424965722001989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364316728283310481334659 5046475092424965722001989)
                  ·
                    refine ⟨946214079829681072875373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5046475092424965722001989 946214079829681072875373)
                    ·
                      rfl

theorem cell22_2764118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2764118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764118 prefixEnd_2764118 := by exact prefixLift 2764118
  have htrace : WordTrace (prefixWord ++ tailWord_2764118) baseStart_2764118 baseEnd_2764118 := by
    simpa [prefixWord, tailWord_2764118, baseEnd_2764118] using wordTrace_append hprefix tailTrace_2764118
  have hstable : (prefixWord ++ tailWord_2764118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764118).length < 2 ^ (prefixWord ++ tailWord_2764118).sum := by decide
  have hdescent : baseEnd_2764118 < baseStart_2764118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764215 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 4, 3]
def baseStart_2764215 : Nat := 118140960795 + 2764215 * 2 ^ 59
def prefixEnd_2764215 : Nat := 4983230072969 + 3 ^ 40 * 2764215 * 2
def baseEnd_2764215 : Nat := 946247284912005153200075

theorem tailTrace_2764215 : CollatzResearch.WordTrace tailWord_2764215 prefixEnd_2764215 946247284912005153200075 := by
  unfold tailWord_2764215
  simp only [CollatzResearch.WordTrace]
  refine ⟨100819203680728620182078099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67212802453819080121385399 100819203680728620182078099)
  ·
    refine ⟨151228805521092930273117149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100819203680728620182078099 151228805521092930273117149)
    ·
      refine ⟨56710802070409848852418931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151228805521092930273117149 56710802070409848852418931)
      ·
        refine ⟨85066203105614773278628397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56710802070409848852418931 85066203105614773278628397)
        ·
          refine ⟨31899826164605539979485649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85066203105614773278628397 31899826164605539979485649)
          ·
            refine ⟨23924869623454154984614237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31899826164605539979485649 23924869623454154984614237)
            ·
              refine ⟨8971826108795308119230339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23924869623454154984614237 8971826108795308119230339)
              ·
                refine ⟨13457739163192962178845509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8971826108795308119230339 13457739163192962178845509)
                ·
                  refine ⟨2523326093098680408533533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13457739163192962178845509 2523326093098680408533533)
                  ·
                    refine ⟨946247284912005153200075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523326093098680408533533 946247284912005153200075)
                    ·
                      rfl

theorem cell22_2764215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_2764215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764215 prefixEnd_2764215 := by exact prefixLift 2764215
  have htrace : WordTrace (prefixWord ++ tailWord_2764215) baseStart_2764215 baseEnd_2764215 := by
    simpa [prefixWord, tailWord_2764215, baseEnd_2764215] using wordTrace_append hprefix tailTrace_2764215
  have hstable : (prefixWord ++ tailWord_2764215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764215).length < 2 ^ (prefixWord ++ tailWord_2764215).sum := by decide
  have hdescent : baseEnd_2764215 < baseStart_2764215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764260 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2764260 : Nat := 118140960795 + 2764260 * 2 ^ 59
def prefixEnd_2764260 : Nat := 4983230072969 + 3 ^ 40 * 2764260 * 2
def baseEnd_2764260 : Nat := 946262689331640035824937

theorem tailTrace_2764260 : CollatzResearch.WordTrace tailWord_2764260 prefixEnd_2764260 946262689331640035824937 := by
  unfold tailWord_2764260
  simp only [CollatzResearch.WordTrace]
  refine ⟨50410422482782796433733117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67213896643710395244977489 50410422482782796433733117)
  ·
    refine ⟨18903908431043548662649919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50410422482782796433733117 18903908431043548662649919)
    ·
      refine ⟨28355862646565322993974879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18903908431043548662649919 28355862646565322993974879)
      ·
        refine ⟨42533793969847984490962319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28355862646565322993974879 42533793969847984490962319)
        ·
          refine ⟨63800690954771976736443479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42533793969847984490962319 63800690954771976736443479)
          ·
            refine ⟨95701036432157965104665219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63800690954771976736443479 95701036432157965104665219)
            ·
              refine ⟨143551554648236947656997829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95701036432157965104665219 143551554648236947656997829)
              ·
                refine ⟨26915916496544427685687093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143551554648236947656997829 26915916496544427685687093)
                ·
                  refine ⟨2523367171551040095533165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26915916496544427685687093 2523367171551040095533165)
                  ·
                    refine ⟨946262689331640035824937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523367171551040095533165 946262689331640035824937)
                    ·
                      rfl

theorem cell22_2764260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2764260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764260 prefixEnd_2764260 := by exact prefixLift 2764260
  have htrace : WordTrace (prefixWord ++ tailWord_2764260) baseStart_2764260 baseEnd_2764260 := by
    simpa [prefixWord, tailWord_2764260, baseEnd_2764260] using wordTrace_append hprefix tailTrace_2764260
  have hstable : (prefixWord ++ tailWord_2764260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764260).length < 2 ^ (prefixWord ++ tailWord_2764260).sum := by decide
  have hdescent : baseEnd_2764260 < baseStart_2764260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764425 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 7]
def baseStart_2764425 : Nat := 118140960795 + 2764425 * 2 ^ 59
def prefixEnd_2764425 : Nat := 4983230072969 + 3 ^ 40 * 2764425 * 2
def baseEnd_2764425 : Nat := 315439724067878201816477

theorem tailTrace_2764425 : CollatzResearch.WordTrace tailWord_2764425 prefixEnd_2764425 315439724067878201816477 := by
  unfold tailWord_2764425
  simp only [CollatzResearch.WordTrace]
  refine ⟨100826863009967826047222729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67217908673311884031481819 100826863009967826047222729)
  ·
    refine ⟨75620147257475869535417047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100826863009967826047222729 75620147257475869535417047)
    ·
      refine ⟨113430220886213804303125571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75620147257475869535417047 113430220886213804303125571)
      ·
        refine ⟨170145331329320706454688357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113430220886213804303125571 170145331329320706454688357)
        ·
          refine ⟨31902249624247632460254067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170145331329320706454688357 31902249624247632460254067)
          ·
            refine ⟨47853374436371448690381101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31902249624247632460254067 47853374436371448690381101)
            ·
              refine ⟨17945015413639293258892913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47853374436371448690381101 17945015413639293258892913)
              ·
                refine ⟨13458761560229469944169685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17945015413639293258892913 13458761560229469944169685)
                ·
                  refine ⟨315439724067878201816477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13458761560229469944169685 315439724067878201816477)
                  ·
                    rfl

theorem cell22_2764425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_2764425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764425 prefixEnd_2764425 := by exact prefixLift 2764425
  have htrace : WordTrace (prefixWord ++ tailWord_2764425) baseStart_2764425 baseEnd_2764425 := by
    simpa [prefixWord, tailWord_2764425, baseEnd_2764425] using wordTrace_append hprefix tailTrace_2764425
  have hstable : (prefixWord ++ tailWord_2764425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764425).length < 2 ^ (prefixWord ++ tailWord_2764425).sum := by decide
  have hdescent : baseEnd_2764425 < baseStart_2764425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764446 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2764446 : Nat := 118140960795 + 2764446 * 2 ^ 59
def prefixEnd_2764446 : Nat := 4983230072969 + 3 ^ 40 * 2764446 * 2
def baseEnd_2764446 : Nat := 946326360932797550674367

theorem tailTrace_2764446 : CollatzResearch.WordTrace tailWord_2764446 prefixEnd_2764446 946326360932797550674367 := by
  unfold tailWord_2764446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603453617861468329217149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67218419295261164422491461 12603453617861468329217149)
  ·
    refine ⟨4726295106698050623456431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12603453617861468329217149 4726295106698050623456431)
    ·
      refine ⟨7089442660047075935184647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726295106698050623456431 7089442660047075935184647)
      ·
        refine ⟨10634163990070613902776971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089442660047075935184647 10634163990070613902776971)
        ·
          refine ⟨15951245985105920854165457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10634163990070613902776971 15951245985105920854165457)
          ·
            refine ⟨11963434488829440640624093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15951245985105920854165457 11963434488829440640624093)
            ·
              refine ⟨4486287933311040240234035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11963434488829440640624093 4486287933311040240234035)
              ·
                refine ⟨6729431899966560360351053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486287933311040240234035 6729431899966560360351053)
                ·
                  refine ⟨2523536962487460135131645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6729431899966560360351053 2523536962487460135131645)
                  ·
                    refine ⟨946326360932797550674367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523536962487460135131645 946326360932797550674367)
                    ·
                      rfl

theorem cell22_2764446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2764446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764446 prefixEnd_2764446 := by exact prefixLift 2764446
  have htrace : WordTrace (prefixWord ++ tailWord_2764446) baseStart_2764446 baseEnd_2764446 := by
    simpa [prefixWord, tailWord_2764446, baseEnd_2764446] using wordTrace_append hprefix tailTrace_2764446
  have hstable : (prefixWord ++ tailWord_2764446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764446).length < 2 ^ (prefixWord ++ tailWord_2764446).sum := by decide
  have hdescent : baseEnd_2764446 < baseStart_2764446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764504 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_2764504 : Nat := 118140960795 + 2764504 * 2 ^ 59
def prefixEnd_2764504 : Nat := 4983230072969 + 3 ^ 40 * 2764504 * 2
def baseEnd_2764504 : Nat := 315448738506034910908063

theorem tailTrace_2764504 : CollatzResearch.WordTrace tailWord_2764504 prefixEnd_2764504 315448738506034910908063 := by
  unfold tailWord_2764504
  simp only [CollatzResearch.WordTrace]
  refine ⟨50414872188340811269674283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67219829584454415026232377 50414872188340811269674283)
  ·
    refine ⟨75622308282511216904511425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50414872188340811269674283 75622308282511216904511425)
    ·
      refine ⟨56716731211883412678383569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75622308282511216904511425 56716731211883412678383569)
      ·
        refine ⟨42537548408912559508787677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56716731211883412678383569 42537548408912559508787677)
        ·
          refine ⟨15951580653342209815795379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42537548408912559508787677 15951580653342209815795379)
          ·
            refine ⟨23927370980013314723693069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15951580653342209815795379 23927370980013314723693069)
            ·
              refine ⟨8972764117504993021384901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23927370980013314723693069 8972764117504993021384901)
              ·
                refine ⟨1682393272032186191509669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8972764117504993021384901 1682393272032186191509669)
                ·
                  refine ⟨315448738506034910908063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682393272032186191509669 315448738506034910908063)
                  ·
                    rfl

theorem cell22_2764504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_2764504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764504 prefixEnd_2764504 := by exact prefixLift 2764504
  have htrace : WordTrace (prefixWord ++ tailWord_2764504) baseStart_2764504 baseEnd_2764504 := by
    simpa [prefixWord, tailWord_2764504, baseEnd_2764504] using wordTrace_append hprefix tailTrace_2764504
  have hstable : (prefixWord ++ tailWord_2764504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764504).length < 2 ^ (prefixWord ++ tailWord_2764504).sum := by decide
  have hdescent : baseEnd_2764504 < baseStart_2764504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764517 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2764517 : Nat := 118140960795 + 2764517 * 2 ^ 59
def prefixEnd_2764517 : Nat := 4983230072969 + 3 ^ 40 * 2764517 * 2
def baseEnd_2764517 : Nat := 946350665683777032149149

theorem tailTrace_2764517 : CollatzResearch.WordTrace tailWord_2764517 prefixEnd_2764517 946350665683777032149149 := by
  unfold tailWord_2764517
  simp only [CollatzResearch.WordTrace]
  refine ⟨100830218525634525759571805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67220145683756350506381203 100830218525634525759571805)
  ·
    refine ⟨37811331947112947159839427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100830218525634525759571805 37811331947112947159839427)
    ·
      refine ⟨56716997920669420739759141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37811331947112947159839427 56716997920669420739759141)
      ·
        refine ⟨10634437110125516388704839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56716997920669420739759141 10634437110125516388704839)
        ·
          refine ⟨15951655665188274583057259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10634437110125516388704839 15951655665188274583057259)
          ·
            refine ⟨23927483497782411874585889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15951655665188274583057259 23927483497782411874585889)
            ·
              refine ⟨17945612623336808905939417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23927483497782411874585889 17945612623336808905939417)
              ·
                refine ⟨13459209467502606679454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17945612623336808905939417 13459209467502606679454563)
                ·
                  refine ⟨20188814201253910019181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13459209467502606679454563 20188814201253910019181845)
                  ·
                    refine ⟨946350665683777032149149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20188814201253910019181845 946350665683777032149149)
                    ·
                      rfl

theorem cell22_2764517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2764517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764517 prefixEnd_2764517 := by exact prefixLift 2764517
  have htrace : WordTrace (prefixWord ++ tailWord_2764517) baseStart_2764517 baseEnd_2764517 := by
    simpa [prefixWord, tailWord_2764517, baseEnd_2764517] using wordTrace_append hprefix tailTrace_2764517
  have hstable : (prefixWord ++ tailWord_2764517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764517).length < 2 ^ (prefixWord ++ tailWord_2764517).sum := by decide
  have hdescent : baseEnd_2764517 < baseStart_2764517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764534 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2764534 : Nat := 118140960795 + 2764534 * 2 ^ 59
def prefixEnd_2764534 : Nat := 4983230072969 + 3 ^ 40 * 2764534 * 2
def baseEnd_2764534 : Nat := 946356485131194654474097

theorem tailTrace_2764534 : CollatzResearch.WordTrace tailWord_2764534 prefixEnd_2764534 946356485131194654474097 := by
  unfold tailWord_2764534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301927410410808603933791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67220559044381958441960437 6301927410410808603933791)
  ·
    refine ⟨9452891115616212905900687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6301927410410808603933791 9452891115616212905900687)
    ·
      refine ⟨14179336673424319358851031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9452891115616212905900687 14179336673424319358851031)
      ·
        refine ⟨21269005010136479038276547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14179336673424319358851031 21269005010136479038276547)
        ·
          refine ⟨31903507515204718557414821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21269005010136479038276547 31903507515204718557414821)
          ·
            refine ⟨5981907659100884729515279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31903507515204718557414821 5981907659100884729515279)
            ·
              refine ⟨8972861488651327094272919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5981907659100884729515279 8972861488651327094272919)
              ·
                refine ⟨13459292232976990641409379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8972861488651327094272919 13459292232976990641409379)
                ·
                  refine ⟨20188938349465485962114069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13459292232976990641409379 20188938349465485962114069)
                  ·
                    refine ⟨946356485131194654474097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20188938349465485962114069 946356485131194654474097)
                    ·
                      rfl

theorem cell22_2764534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2764534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764534 prefixEnd_2764534 := by exact prefixLift 2764534
  have htrace : WordTrace (prefixWord ++ tailWord_2764534) baseStart_2764534 baseEnd_2764534 := by
    simpa [prefixWord, tailWord_2764534, baseEnd_2764534] using wordTrace_append hprefix tailTrace_2764534
  have hstable : (prefixWord ++ tailWord_2764534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764534).length < 2 ^ (prefixWord ++ tailWord_2764534).sum := by decide
  have hdescent : baseEnd_2764534 < baseStart_2764534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764628 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2764628 : Nat := 118140960795 + 2764628 * 2 ^ 59
def prefixEnd_2764628 : Nat := 4983230072969 + 3 ^ 40 * 2764628 * 2
def baseEnd_2764628 : Nat := 315462887750736580874603

theorem tailTrace_2764628 : CollatzResearch.WordTrace tailWord_2764628 prefixEnd_2764628 315462887750736580874603 := by
  unfold tailWord_2764628
  simp only [CollatzResearch.WordTrace]
  refine ⟨50417133514116195858431269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67222844685488261144575025 50417133514116195858431269)
  ·
    refine ⟨9453212533896786723455863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50417133514116195858431269 9453212533896786723455863)
    ·
      refine ⟨14179818800845180085183795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9453212533896786723455863 14179818800845180085183795)
      ·
        refine ⟨21269728201267770127775693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14179818800845180085183795 21269728201267770127775693)
        ·
          refine ⟨7976148075475413797915885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21269728201267770127775693 7976148075475413797915885)
          ·
            refine ⟨2991055528303280174218457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7976148075475413797915885 2991055528303280174218457)
            ·
              refine ⟨2243291646227460130663843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991055528303280174218457 2243291646227460130663843)
              ·
                refine ⟨3364937469341190195995765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243291646227460130663843 3364937469341190195995765)
                ·
                  refine ⟨315462887750736580874603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364937469341190195995765 315462887750736580874603)
                  ·
                    rfl

theorem cell22_2764628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2764628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764628 prefixEnd_2764628 := by exact prefixLift 2764628
  have htrace : WordTrace (prefixWord ++ tailWord_2764628) baseStart_2764628 baseEnd_2764628 := by
    simpa [prefixWord, tailWord_2764628, baseEnd_2764628] using wordTrace_append hprefix tailTrace_2764628
  have hstable : (prefixWord ++ tailWord_2764628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764628).length < 2 ^ (prefixWord ++ tailWord_2764628).sum := by decide
  have hdescent : baseEnd_2764628 < baseStart_2764628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764701 : List Nat := [1, 4, 2, 1, 2, 3, 3, 6]
def baseStart_2764701 : Nat := 118140960795 + 2764701 * 2 ^ 59
def prefixEnd_2764701 : Nat := 4983230072969 + 3 ^ 40 * 2764701 * 2
def baseEnd_2764701 : Nat := 105157072516006876172065

theorem tailTrace_2764701 : CollatzResearch.WordTrace tailWord_2764701 prefixEnd_2764701 105157072516006876172065 := by
  unfold tailWord_2764701
  simp only [CollatzResearch.WordTrace]
  refine ⟨100836929556967925184269957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67224619704645283456179971 100836929556967925184269957)
  ·
    refine ⟨18906924291931485972050617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100836929556967925184269957 18906924291931485972050617)
    ·
      refine ⟨14180193218948614479037963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18906924291931485972050617 14180193218948614479037963)
      ·
        refine ⟨21270289828422921718556945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14180193218948614479037963 21270289828422921718556945)
        ·
          refine ⟨15952717371317191288917709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21270289828422921718556945 15952717371317191288917709)
          ·
            refine ⟨5982269014243946733344141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15952717371317191288917709 5982269014243946733344141)
            ·
              refine ⟨2243350880341480025004053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5982269014243946733344141 2243350880341480025004053)
              ·
                refine ⟨105157072516006876172065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2243350880341480025004053 105157072516006876172065)
                ·
                  rfl

theorem cell22_2764701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 6].length) (baseStart_2764701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764701 prefixEnd_2764701 := by exact prefixLift 2764701
  have htrace : WordTrace (prefixWord ++ tailWord_2764701) baseStart_2764701 baseEnd_2764701 := by
    simpa [prefixWord, tailWord_2764701, baseEnd_2764701] using wordTrace_append hprefix tailTrace_2764701
  have hstable : (prefixWord ++ tailWord_2764701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764701).length < 2 ^ (prefixWord ++ tailWord_2764701).sum := by decide
  have hdescent : baseEnd_2764701 < baseStart_2764701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764703 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 2, 4]
def baseStart_2764703 : Nat := 118140960795 + 2764703 * 2 ^ 59
def prefixEnd_2764703 : Nat := 4983230072969 + 3 ^ 40 * 2764703 * 2
def baseEnd_2764703 : Nat := 946414337284934546998579

theorem tailTrace_2764703 : CollatzResearch.WordTrace tailWord_2764703 prefixEnd_2764703 946414337284934546998579 := by
  unfold tailWord_2764703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100837002502960679525842763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67224668335307119683895175 100837002502960679525842763)
  ·
    refine ⟨151255503754441019288764145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100837002502960679525842763 151255503754441019288764145)
    ·
      refine ⟨113441627815830764466573109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151255503754441019288764145 113441627815830764466573109)
      ·
        refine ⟨10635152607734134168741229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113441627815830764466573109 10635152607734134168741229)
        ·
          refine ⟨3988182227900300313277961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10635152607734134168741229 3988182227900300313277961)
          ·
            refine ⟨2991136670925225234958471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988182227900300313277961 2991136670925225234958471)
            ·
              refine ⟨4486705006387837852437707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991136670925225234958471 4486705006387837852437707)
              ·
                refine ⟨6730057509581756778656561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486705006387837852437707 6730057509581756778656561)
                ·
                  refine ⟨5047543132186317583992421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6730057509581756778656561 5047543132186317583992421)
                  ·
                    refine ⟨946414337284934546998579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047543132186317583992421 946414337284934546998579)
                    ·
                      rfl

theorem cell22_2764703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_2764703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764703 prefixEnd_2764703 := by exact prefixLift 2764703
  have htrace : WordTrace (prefixWord ++ tailWord_2764703) baseStart_2764703 baseEnd_2764703 := by
    simpa [prefixWord, tailWord_2764703, baseEnd_2764703] using wordTrace_append hprefix tailTrace_2764703
  have hstable : (prefixWord ++ tailWord_2764703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764703).length < 2 ^ (prefixWord ++ tailWord_2764703).sum := by decide
  have hdescent : baseEnd_2764703 < baseStart_2764703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764729 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 7]
def baseStart_2764729 : Nat := 118140960795 + 2764729 * 2 ^ 59
def prefixEnd_2764729 : Nat := 4983230072969 + 3 ^ 40 * 2764729 * 2
def baseEnd_2764729 : Nat := 315474412538759715282833

theorem tailTrace_2764729 : CollatzResearch.WordTrace tailWord_2764729 prefixEnd_2764729 315474412538759715282833 := by
  unfold tailWord_2764729
  simp only [CollatzResearch.WordTrace]
  refine ⟨100837950800866485966289241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67225300533910990644192827 100837950800866485966289241)
  ·
    refine ⟨75628463100649864474716931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100837950800866485966289241 75628463100649864474716931)
    ·
      refine ⟨113442694650974796712075397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75628463100649864474716931 113442694650974796712075397)
      ·
        refine ⟨21270505247057774383514137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113442694650974796712075397 21270505247057774383514137)
        ·
          refine ⟨15952878935293330787635603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21270505247057774383514137 15952878935293330787635603)
          ·
            refine ⟨23929318402939996181453405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15952878935293330787635603 23929318402939996181453405)
            ·
              refine ⟨8973494401102498568045027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23929318402939996181453405 8973494401102498568045027)
              ·
                refine ⟨13460241601653747852067541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8973494401102498568045027 13460241601653747852067541)
                ·
                  refine ⟨315474412538759715282833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13460241601653747852067541 315474412538759715282833)
                  ·
                    rfl

theorem cell22_2764729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_2764729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764729 prefixEnd_2764729 := by exact prefixLift 2764729
  have htrace : WordTrace (prefixWord ++ tailWord_2764729) baseStart_2764729 baseEnd_2764729 := by
    simpa [prefixWord, tailWord_2764729, baseEnd_2764729] using wordTrace_append hprefix tailTrace_2764729
  have hstable : (prefixWord ++ tailWord_2764729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764729).length < 2 ^ (prefixWord ++ tailWord_2764729).sum := by decide
  have hdescent : baseEnd_2764729 < baseStart_2764729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764733 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2764733 : Nat := 118140960795 + 2764733 * 2 ^ 59
def prefixEnd_2764733 : Nat := 4983230072969 + 3 ^ 40 * 2764733 * 2
def baseEnd_2764733 : Nat := 946424606898024468748487

theorem tailTrace_2764733 : CollatzResearch.WordTrace tailWord_2764733 prefixEnd_2764733 946424606898024468748487 := by
  unfold tailWord_2764733
  simp only [CollatzResearch.WordTrace]
  refine ⟨100838096692851994649434853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67225397795234663099623235 100838096692851994649434853)
  ·
    refine ⟨18907143129909748996769035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100838096692851994649434853 18907143129909748996769035)
    ·
      refine ⟨28360714694864623495153553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18907143129909748996769035 28360714694864623495153553)
      ·
        refine ⟨21270536021148467621365165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28360714694864623495153553 21270536021148467621365165)
        ·
          refine ⟨7976451007930675358011937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21270536021148467621365165 7976451007930675358011937)
          ·
            refine ⟨5982338255948006518508953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7976451007930675358011937 5982338255948006518508953)
            ·
              refine ⟨4486753691961004888881715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982338255948006518508953 4486753691961004888881715)
              ·
                refine ⟨6730130537941507333322573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486753691961004888881715 6730130537941507333322573)
                ·
                  refine ⟨2523798951728065249995965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6730130537941507333322573 2523798951728065249995965)
                  ·
                    refine ⟨946424606898024468748487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523798951728065249995965 946424606898024468748487)
                    ·
                      rfl

theorem cell22_2764733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2764733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764733 prefixEnd_2764733 := by exact prefixLift 2764733
  have htrace : WordTrace (prefixWord ++ tailWord_2764733) baseStart_2764733 baseEnd_2764733 := by
    simpa [prefixWord, tailWord_2764733, baseEnd_2764733] using wordTrace_append hprefix tailTrace_2764733
  have hstable : (prefixWord ++ tailWord_2764733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764733).length < 2 ^ (prefixWord ++ tailWord_2764733).sum := by decide
  have hdescent : baseEnd_2764733 < baseStart_2764733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764810 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2764810 : Nat := 118140960795 + 2764810 * 2 ^ 59
def prefixEnd_2764810 : Nat := 4983230072969 + 3 ^ 40 * 2764810 * 2
def baseEnd_2764810 : Nat := 946450965571621934573251

theorem tailTrace_2764810 : CollatzResearch.WordTrace tailWord_2764810 prefixEnd_2764810 946450965571621934573251 := by
  unfold tailWord_2764810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210226278393259199996971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67227270075715357866658589 25210226278393259199996971)
  ·
    refine ⟨37815339417589888799995457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25210226278393259199996971 37815339417589888799995457)
    ·
      refine ⟨28361504563192416599996593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37815339417589888799995457 28361504563192416599996593)
      ·
        refine ⟨21271128422394312449997445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28361504563192416599996593 21271128422394312449997445)
        ·
          refine ⟨3988336579198933584374521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21271128422394312449997445 3988336579198933584374521)
          ·
            refine ⟨2991252434399200188280891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3988336579198933584374521 2991252434399200188280891)
            ·
              refine ⟨4486878651598800282421337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2991252434399200188280891 4486878651598800282421337)
              ·
                refine ⟨3365158988699100211816003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4486878651598800282421337 3365158988699100211816003)
                ·
                  refine ⟨5047738483048650317724005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365158988699100211816003 5047738483048650317724005)
                  ·
                    refine ⟨946450965571621934573251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5047738483048650317724005 946450965571621934573251)
                    ·
                      rfl

theorem cell22_2764810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2764810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764810 prefixEnd_2764810 := by exact prefixLift 2764810
  have htrace : WordTrace (prefixWord ++ tailWord_2764810) baseStart_2764810 baseEnd_2764810 := by
    simpa [prefixWord, tailWord_2764810, baseEnd_2764810] using wordTrace_append hprefix tailTrace_2764810
  have hstable : (prefixWord ++ tailWord_2764810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764810).length < 2 ^ (prefixWord ++ tailWord_2764810).sum := by decide
  have hdescent : baseEnd_2764810 < baseStart_2764810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764819 : List Nat := [1, 1, 1, 2, 1, 4, 4, 8]
def baseStart_2764819 : Nat := 118140960795 + 2764819 * 2 ^ 59
def prefixEnd_2764819 : Nat := 4983230072969 + 3 ^ 40 * 2764819 * 2
def baseEnd_2764819 : Nat := 105161560717283212344247

theorem tailTrace_2764819 : CollatzResearch.WordTrace tailWord_2764819 prefixEnd_2764819 105161560717283212344247 := by
  unfold tailWord_2764819
  simp only [CollatzResearch.WordTrace]
  refine ⟨100841233370540431337065511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67227488913693620891377007 100841233370540431337065511)
  ·
    refine ⟨151261850055810647005598267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100841233370540431337065511 151261850055810647005598267)
    ·
      refine ⟨226892775083715970508397401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151261850055810647005598267 226892775083715970508397401)
      ·
        refine ⟨170169581312786977881298051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226892775083715970508397401 170169581312786977881298051)
        ·
          refine ⟨255254371969180466821947077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170169581312786977881298051 255254371969180466821947077)
          ·
            refine ⟨47860194744221337529115077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255254371969180466821947077 47860194744221337529115077)
            ·
              refine ⟨8973786514541500786709077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47860194744221337529115077 8973786514541500786709077)
              ·
                refine ⟨105161560717283212344247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8973786514541500786709077 105161560717283212344247)
                ·
                  rfl

theorem cell22_2764819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_2764819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764819 prefixEnd_2764819 := by exact prefixLift 2764819
  have htrace : WordTrace (prefixWord ++ tailWord_2764819) baseStart_2764819 baseEnd_2764819 := by
    simpa [prefixWord, tailWord_2764819, baseEnd_2764819] using wordTrace_append hprefix tailTrace_2764819
  have hstable : (prefixWord ++ tailWord_2764819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764819).length < 2 ^ (prefixWord ++ tailWord_2764819).sum := by decide
  have hdescent : baseEnd_2764819 < baseStart_2764819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764823 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_2764823 : Nat := 118140960795 + 2764823 * 2 ^ 59
def prefixEnd_2764823 : Nat := 4983230072969 + 3 ^ 40 * 2764823 * 2
def baseEnd_2764823 : Nat := 946455415737294233998211

theorem tailTrace_2764823 : CollatzResearch.WordTrace tailWord_2764823 prefixEnd_2764823 946455415737294233998211 := by
  unfold tailWord_2764823
  simp only [CollatzResearch.WordTrace]
  refine ⟨100841379262525940020211123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67227586175017293346807415 100841379262525940020211123)
  ·
    refine ⟨151262068893788910030316685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100841379262525940020211123 151262068893788910030316685)
    ·
      refine ⟨56723275835170841261368757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151262068893788910030316685 56723275835170841261368757)
      ·
        refine ⟨5317807109547266368253321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56723275835170841261368757 5317807109547266368253321)
        ·
          refine ⟨3988355332160449776189991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317807109547266368253321 3988355332160449776189991)
          ·
            refine ⟨5982532998240674664284987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988355332160449776189991 5982532998240674664284987)
            ·
              refine ⟨8973799497361011996427481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982532998240674664284987 8973799497361011996427481)
              ·
                refine ⟨6730349623020758997320611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8973799497361011996427481 6730349623020758997320611)
                ·
                  refine ⟨10095524434531138495980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6730349623020758997320611 10095524434531138495980917)
                  ·
                    refine ⟨946455415737294233998211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10095524434531138495980917 946455415737294233998211)
                    ·
                      rfl

theorem cell22_2764823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_2764823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764823 prefixEnd_2764823 := by exact prefixLift 2764823
  have htrace : WordTrace (prefixWord ++ tailWord_2764823) baseStart_2764823 baseEnd_2764823 := by
    simpa [prefixWord, tailWord_2764823, baseEnd_2764823] using wordTrace_append hprefix tailTrace_2764823
  have hstable : (prefixWord ++ tailWord_2764823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764823).length < 2 ^ (prefixWord ++ tailWord_2764823).sum := by decide
  have hdescent : baseEnd_2764823 < baseStart_2764823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764836 : List Nat := [2, 3, 1, 4, 2, 10]
def baseStart_2764836 : Nat := 118140960795 + 2764836 * 2 ^ 59
def prefixEnd_2764836 : Nat := 4983230072969 + 3 ^ 40 * 2764836 * 2
def baseEnd_2764836 : Nat := 11684689702505759671891

theorem tailTrace_2764836 : CollatzResearch.WordTrace tailWord_2764836 prefixEnd_2764836 11684689702505759671891 := by
  unfold tailWord_2764836
  simp only [CollatzResearch.WordTrace]
  refine ⟨50420926705739421620217181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67227902274319228826956241 50420926705739421620217181)
  ·
    refine ⟨18907847514652283107581443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50420926705739421620217181 18907847514652283107581443)
    ·
      refine ⟨28361771271978424661372165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18907847514652283107581443 28361771271978424661372165)
      ·
        refine ⟨5317832113495954624007281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28361771271978424661372165 5317832113495954624007281)
        ·
          refine ⟨3988374085121965968005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317832113495954624007281 3988374085121965968005461)
          ·
            refine ⟨11684689702505759671891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3988374085121965968005461 11684689702505759671891)
            ·
              rfl

theorem cell22_2764836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 10].length) (baseStart_2764836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764836 prefixEnd_2764836 := by exact prefixLift 2764836
  have htrace : WordTrace (prefixWord ++ tailWord_2764836) baseStart_2764836 baseEnd_2764836 := by
    simpa [prefixWord, tailWord_2764836, baseEnd_2764836] using wordTrace_append hprefix tailTrace_2764836
  have hstable : (prefixWord ++ tailWord_2764836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764836).length < 2 ^ (prefixWord ++ tailWord_2764836).sum := by decide
  have hdescent : baseEnd_2764836 < baseStart_2764836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764842 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_2764842 : Nat := 118140960795 + 2764842 * 2 ^ 59
def prefixEnd_2764842 : Nat := 4983230072969 + 3 ^ 40 * 2764842 * 2
def baseEnd_2764842 : Nat := 315487306608528172591051

theorem tailTrace_2764842 : CollatzResearch.WordTrace tailWord_2764842 prefixEnd_2764842 315487306608528172591051 := by
  unfold tailWord_2764842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25210518062364276566288195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67228048166304737510101853 25210518062364276566288195)
  ·
    refine ⟨37815777093546414849432293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25210518062364276566288195 37815777093546414849432293)
    ·
      refine ⟨7090458205039952784268555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37815777093546414849432293 7090458205039952784268555)
      ·
        refine ⟨10635687307559929176402833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090458205039952784268555 10635687307559929176402833)
        ·
          refine ⟨7976765480669946882302125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10635687307559929176402833 7976765480669946882302125)
          ·
            refine ⟨2991287055251230080863297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7976765480669946882302125 2991287055251230080863297)
            ·
              refine ⟨2243465291438422560647473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991287055251230080863297 2243465291438422560647473)
              ·
                refine ⟨1682598968578816920485605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2243465291438422560647473 1682598968578816920485605)
                ·
                  refine ⟨315487306608528172591051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682598968578816920485605 315487306608528172591051)
                  ·
                    rfl

theorem cell22_2764842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_2764842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764842 prefixEnd_2764842 := by exact prefixLift 2764842
  have htrace : WordTrace (prefixWord ++ tailWord_2764842) baseStart_2764842 baseEnd_2764842 := by
    simpa [prefixWord, tailWord_2764842, baseEnd_2764842] using wordTrace_append hprefix tailTrace_2764842
  have hstable : (prefixWord ++ tailWord_2764842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764842).length < 2 ^ (prefixWord ++ tailWord_2764842).sum := by decide
  have hdescent : baseEnd_2764842 < baseStart_2764842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764870 : List Nat := [6, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2764870 : Nat := 118140960795 + 2764870 * 2 ^ 59
def prefixEnd_2764870 : Nat := 4983230072969 + 3 ^ 40 * 2764870 * 2
def baseEnd_2764870 : Nat := 105163500533089086452563

theorem tailTrace_2764870 : CollatzResearch.WordTrace tailWord_2764870 prefixEnd_2764870 105163500533089086452563 := by
  unfold tailWord_2764870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151346671667364595224127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67228728995570444698114709 3151346671667364595224127)
  ·
    refine ⟨4727020007501046892836191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151346671667364595224127 4727020007501046892836191)
    ·
      refine ⟨7090530011251570339254287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727020007501046892836191 7090530011251570339254287)
      ·
        refine ⟨10635795016877355508881431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090530011251570339254287 10635795016877355508881431)
        ·
          refine ⟨15953692525316033263322147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10635795016877355508881431 15953692525316033263322147)
          ·
            refine ⟨23930538787974049894983221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15953692525316033263322147 23930538787974049894983221)
            ·
              refine ⟨2243488011372567177654677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23930538787974049894983221 2243488011372567177654677)
              ·
                refine ⟨105163500533089086452563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2243488011372567177654677 105163500533089086452563)
                ·
                  rfl

theorem cell22_2764870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2764870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764870 prefixEnd_2764870 := by exact prefixLift 2764870
  have htrace : WordTrace (prefixWord ++ tailWord_2764870) baseStart_2764870 baseEnd_2764870 := by
    simpa [prefixWord, tailWord_2764870, baseEnd_2764870] using wordTrace_append hprefix tailTrace_2764870
  have hstable : (prefixWord ++ tailWord_2764870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764870).length < 2 ^ (prefixWord ++ tailWord_2764870).sum := by decide
  have hdescent : baseEnd_2764870 < baseStart_2764870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764885 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2764885 : Nat := 118140960795 + 2764885 * 2 ^ 59
def prefixEnd_2764885 : Nat := 4983230072969 + 3 ^ 40 * 2764885 * 2
def baseEnd_2764885 : Nat := 946476639604346738948021

theorem tailTrace_2764885 : CollatzResearch.WordTrace tailWord_2764885 prefixEnd_2764885 946476639604346738948021 := by
  unfold tailWord_2764885
  simp only [CollatzResearch.WordTrace]
  refine ⟨100843640588301324608968109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67229093725534216405978739 100843640588301324608968109)
  ·
    refine ⟨37816365220612996728363041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100843640588301324608968109 37816365220612996728363041)
    ·
      refine ⟨28362273915459747546272281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37816365220612996728363041 28362273915459747546272281)
      ·
        refine ⟨21271705436594810659704211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28362273915459747546272281 21271705436594810659704211)
        ·
          refine ⟨31907558154892215989556317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21271705436594810659704211 31907558154892215989556317)
          ·
            refine ⟨11965334308084580996083619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31907558154892215989556317 11965334308084580996083619)
            ·
              refine ⟨17948001462126871494125429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965334308084580996083619 17948001462126871494125429)
              ·
                refine ⟨1682625137074394202574259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17948001462126871494125429 1682625137074394202574259)
                ·
                  refine ⟨2523937705611591303861389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682625137074394202574259 2523937705611591303861389)
                  ·
                    refine ⟨946476639604346738948021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2523937705611591303861389 946476639604346738948021)
                    ·
                      rfl

theorem cell22_2764885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2764885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764885 prefixEnd_2764885 := by exact prefixLift 2764885
  have htrace : WordTrace (prefixWord ++ tailWord_2764885) baseStart_2764885 baseEnd_2764885 := by
    simpa [prefixWord, tailWord_2764885, baseEnd_2764885] using wordTrace_append hprefix tailTrace_2764885
  have hstable : (prefixWord ++ tailWord_2764885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764885).length < 2 ^ (prefixWord ++ tailWord_2764885).sum := by decide
  have hdescent : baseEnd_2764885 < baseStart_2764885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764896 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_2764896 : Nat := 118140960795 + 2764896 * 2 ^ 59
def prefixEnd_2764896 : Nat := 4983230072969 + 3 ^ 40 * 2764896 * 2
def baseEnd_2764896 : Nat := 946480405129146376922987

theorem tailTrace_2764896 : CollatzResearch.WordTrace tailWord_2764896 prefixEnd_2764896 946480405129146376922987 := by
  unfold tailWord_2764896
  simp only [CollatzResearch.WordTrace]
  refine ⟨50422020895630736743809271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67229361194174315658412361 50422020895630736743809271)
  ·
    refine ⟨75633031343446105115713907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50422020895630736743809271 75633031343446105115713907)
    ·
      refine ⟨113449547015169157673570861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75633031343446105115713907 113449547015169157673570861)
      ·
        refine ⟨42543580130688434127589073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113449547015169157673570861 42543580130688434127589073)
        ·
          refine ⟨31907685098016325595691805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42543580130688434127589073 31907685098016325595691805)
          ·
            refine ⟨11965381911756122098384427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31907685098016325595691805 11965381911756122098384427)
            ·
              refine ⟨17948072867634183147576641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11965381911756122098384427 17948072867634183147576641)
              ·
                refine ⟨13461054650725637360682481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17948072867634183147576641 13461054650725637360682481)
                ·
                  refine ⟨10095790988044228020511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13461054650725637360682481 10095790988044228020511861)
                  ·
                    refine ⟨946480405129146376922987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10095790988044228020511861 946480405129146376922987)
                    ·
                      rfl

theorem cell22_2764896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_2764896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764896 prefixEnd_2764896 := by exact prefixLift 2764896
  have htrace : WordTrace (prefixWord ++ tailWord_2764896) baseStart_2764896 baseEnd_2764896 := by
    simpa [prefixWord, tailWord_2764896, baseEnd_2764896] using wordTrace_append hprefix tailTrace_2764896
  have hstable : (prefixWord ++ tailWord_2764896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764896).length < 2 ^ (prefixWord ++ tailWord_2764896).sum := by decide
  have hdescent : baseEnd_2764896 < baseStart_2764896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2764986 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2764986 : Nat := 118140960795 + 2764986 * 2 ^ 59
def prefixEnd_2764986 : Nat := 4983230072969 + 3 ^ 40 * 2764986 * 2
def baseEnd_2764986 : Nat := 946511213968416142172711

theorem tailTrace_2764986 : CollatzResearch.WordTrace tailWord_2764986 prefixEnd_2764986 946511213968416142172711 := by
  unfold tailWord_2764986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25211831090233854714598703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67231549573956945905596541 25211831090233854714598703)
  ·
    refine ⟨37817746635350782071898055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25211831090233854714598703 37817746635350782071898055)
    ·
      refine ⟨56726619953026173107847083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37817746635350782071898055 56726619953026173107847083)
      ·
        refine ⟨85089929929539259661770625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56726619953026173107847083 85089929929539259661770625)
        ·
          refine ⟨63817447447154444746327969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85089929929539259661770625 63817447447154444746327969)
          ·
            refine ⟨47863085585365833559745977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63817447447154444746327969 47863085585365833559745977)
            ·
              refine ⟨35897314189024375169809483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47863085585365833559745977 35897314189024375169809483)
              ·
                refine ⟨53845971283536562754714225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35897314189024375169809483 53845971283536562754714225)
                ·
                  refine ⟨40384478462652422066035669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53845971283536562754714225 40384478462652422066035669)
                  ·
                    refine ⟨946511213968416142172711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40384478462652422066035669 946511213968416142172711)
                    ·
                      rfl

theorem cell22_2764986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2764986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2764986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2764986 prefixEnd_2764986 := by exact prefixLift 2764986
  have htrace : WordTrace (prefixWord ++ tailWord_2764986) baseStart_2764986 baseEnd_2764986 := by
    simpa [prefixWord, tailWord_2764986, baseEnd_2764986] using wordTrace_append hprefix tailTrace_2764986
  have hstable : (prefixWord ++ tailWord_2764986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2764986).length < 2 ^ (prefixWord ++ tailWord_2764986).sum := by decide
  have hdescent : baseEnd_2764986 < baseStart_2764986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2764986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765037 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2765037 : Nat := 118140960795 + 2765037 * 2 ^ 59
def prefixEnd_2765037 : Nat := 4983230072969 + 3 ^ 40 * 2765037 * 2
def baseEnd_2765037 : Nat := 946528672310669009147555

theorem tailTrace_2765037 : CollatzResearch.WordTrace tailWord_2765037 prefixEnd_2765037 946528672310669009147555 := by
  unfold tailWord_2765037
  simp only [CollatzResearch.WordTrace]
  refine ⟨100849184483750654568501365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67232789655833769712334243 100849184483750654568501365)
  ·
    refine ⟨9454611045351623865797003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100849184483750654568501365 9454611045351623865797003)
    ·
      refine ⟨14181916568027435798695505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454611045351623865797003 14181916568027435798695505)
      ·
        refine ⟨10636437426020576849021629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14181916568027435798695505 10636437426020576849021629)
        ·
          refine ⟨3988664034757716318383111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10636437426020576849021629 3988664034757716318383111)
          ·
            refine ⟨5982996052136574477574667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988664034757716318383111 5982996052136574477574667)
            ·
              refine ⟨8974494078204861716362001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5982996052136574477574667 8974494078204861716362001)
              ·
                refine ⟨6730870558653646287271501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8974494078204861716362001 6730870558653646287271501)
                ·
                  refine ⟨2524076459495117357726813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6730870558653646287271501 2524076459495117357726813)
                  ·
                    refine ⟨946528672310669009147555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524076459495117357726813 946528672310669009147555)
                    ·
                      rfl

theorem cell22_2765037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2765037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765037 prefixEnd_2765037 := by exact prefixLift 2765037
  have htrace : WordTrace (prefixWord ++ tailWord_2765037) baseStart_2765037 baseEnd_2765037 := by
    simpa [prefixWord, tailWord_2765037, baseEnd_2765037] using wordTrace_append hprefix tailTrace_2765037
  have hstable : (prefixWord ++ tailWord_2765037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765037).length < 2 ^ (prefixWord ++ tailWord_2765037).sum := by decide
  have hdescent : baseEnd_2765037 < baseStart_2765037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765054 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2765054 : Nat := 118140960795 + 2765054 * 2 ^ 59
def prefixEnd_2765054 : Nat := 4983230072969 + 3 ^ 40 * 2765054 * 2
def baseEnd_2765054 : Nat := 946534491758086631472503

theorem tailTrace_2765054 : CollatzResearch.WordTrace tailWord_2765054 prefixEnd_2765054 946534491758086631472503 := by
  unfold tailWord_2765054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606225565586133308983777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67233203016459377647913477 12606225565586133308983777)
  ·
    refine ⟨9454669174189599981737833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12606225565586133308983777 9454669174189599981737833)
    ·
      refine ⟨7091001880642199986303375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9454669174189599981737833 7091001880642199986303375)
      ·
        refine ⟨10636502820963299979455063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091001880642199986303375 10636502820963299979455063)
        ·
          refine ⟨15954754231444949969182595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10636502820963299979455063 15954754231444949969182595)
          ·
            refine ⟨23932131347167424953773893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15954754231444949969182595 23932131347167424953773893)
            ·
              refine ⟨4487274627593892178832605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23932131347167424953773893 4487274627593892178832605)
              ·
                refine ⟨1682727985347709567062227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4487274627593892178832605 1682727985347709567062227)
                ·
                  refine ⟨2524091978021564350593341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682727985347709567062227 2524091978021564350593341)
                  ·
                    refine ⟨946534491758086631472503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524091978021564350593341 946534491758086631472503)
                    ·
                      rfl

theorem cell22_2765054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2765054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765054 prefixEnd_2765054 := by exact prefixLift 2765054
  have htrace : WordTrace (prefixWord ++ tailWord_2765054) baseStart_2765054 baseEnd_2765054 := by
    simpa [prefixWord, tailWord_2765054, baseEnd_2765054] using wordTrace_append hprefix tailTrace_2765054
  have hstable : (prefixWord ++ tailWord_2765054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765054).length < 2 ^ (prefixWord ++ tailWord_2765054).sum := by decide
  have hdescent : baseEnd_2765054 < baseStart_2765054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765140 : List Nat := [2, 4, 1, 1, 2, 3, 2, 7]
def baseStart_2765140 : Nat := 118140960795 + 2765140 * 2 ^ 59
def prefixEnd_2765140 : Nat := 4983230072969 + 3 ^ 40 * 2765140 * 2
def baseEnd_2765140 : Nat := 105173770146179008202471

theorem tailTrace_2765140 : CollatzResearch.WordTrace tailWord_2765140 prefixEnd_2765140 105173770146179008202471 := by
  unfold tailWord_2765140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50426470601188751579750437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67235294134918335439667249 50426470601188751579750437)
  ·
    refine ⟨9454963237722890921203207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50426470601188751579750437 9454963237722890921203207)
    ·
      refine ⟨14182444856584336381804811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9454963237722890921203207 14182444856584336381804811)
      ·
        refine ⟨21273667284876504572707217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14182444856584336381804811 21273667284876504572707217)
        ·
          refine ⟨15955250463657378429530413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21273667284876504572707217 15955250463657378429530413)
          ·
            refine ⟨5983218923871516911073905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15955250463657378429530413 5983218923871516911073905)
            ·
              refine ⟨4487414192903637683305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983218923871516911073905 4487414192903637683305429)
              ·
                refine ⟨105173770146179008202471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4487414192903637683305429 105173770146179008202471)
                ·
                  rfl

theorem cell22_2765140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_2765140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765140 prefixEnd_2765140 := by exact prefixLift 2765140
  have htrace : WordTrace (prefixWord ++ tailWord_2765140) baseStart_2765140 baseEnd_2765140 := by
    simpa [prefixWord, tailWord_2765140, baseEnd_2765140] using wordTrace_append hprefix tailTrace_2765140
  have hstable : (prefixWord ++ tailWord_2765140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765140).length < 2 ^ (prefixWord ++ tailWord_2765140).sum := by decide
  have hdescent : baseEnd_2765140 < baseStart_2765140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765155 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 5, 3]
def baseStart_2765155 : Nat := 118140960795 + 2765155 * 2 ^ 59
def prefixEnd_2765155 : Nat := 4983230072969 + 3 ^ 40 * 2765155 * 2
def baseEnd_2765155 : Nat := 946569066122156034697193

theorem tailTrace_2765155 : CollatzResearch.WordTrace tailWord_2765155 prefixEnd_2765155 946569066122156034697193 := by
  unfold tailWord_2765155
  simp only [CollatzResearch.WordTrace]
  refine ⟨100853488297323160721296919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67235658864882107147531279 100853488297323160721296919)
  ·
    refine ⟨151280232445984741081945379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100853488297323160721296919 151280232445984741081945379)
    ·
      refine ⟨226920348668977111622918069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151280232445984741081945379 226920348668977111622918069)
      ·
        refine ⟨21273782687716604214648569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226920348668977111622918069 21273782687716604214648569)
        ·
          refine ⟨15955337015787453160986427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21273782687716604214648569 15955337015787453160986427)
          ·
            refine ⟨23933005523681179741479641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15955337015787453160986427 23933005523681179741479641)
            ·
              refine ⟨17949754142760884806109731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23933005523681179741479641 17949754142760884806109731)
              ·
                refine ⟨26924631214141327209164597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17949754142760884806109731 26924631214141327209164597)
                ·
                  refine ⟨2524184176325749425859181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26924631214141327209164597 2524184176325749425859181)
                  ·
                    refine ⟨946569066122156034697193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524184176325749425859181 946569066122156034697193)
                    ·
                      rfl

theorem cell22_2765155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].length) (baseStart_2765155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765155 prefixEnd_2765155 := by exact prefixLift 2765155
  have htrace : WordTrace (prefixWord ++ tailWord_2765155) baseStart_2765155 baseEnd_2765155 := by
    simpa [prefixWord, tailWord_2765155, baseEnd_2765155] using wordTrace_append hprefix tailTrace_2765155
  have hstable : (prefixWord ++ tailWord_2765155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765155).length < 2 ^ (prefixWord ++ tailWord_2765155).sum := by decide
  have hdescent : baseEnd_2765155 < baseStart_2765155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765183 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2765183 : Nat := 118140960795 + 2765183 * 2 ^ 59
def prefixEnd_2765183 : Nat := 4983230072969 + 3 ^ 40 * 2765183 * 2
def baseEnd_2765183 : Nat := 946578651094373294997107

theorem tailTrace_2765183 : CollatzResearch.WordTrace tailWord_2765183 prefixEnd_2765183 946578651094373294997107 := by
  unfold tailWord_2765183
  simp only [CollatzResearch.WordTrace]
  refine ⟨100854509541221721503316203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67236339694147814335544135 100854509541221721503316203)
  ·
    refine ⟨151281764311832582254974305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100854509541221721503316203 151281764311832582254974305)
    ·
      refine ⟨113461323233874436691230729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151281764311832582254974305 113461323233874436691230729)
      ·
        refine ⟨85095992425405827518423047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113461323233874436691230729 85095992425405827518423047)
        ·
          refine ⟨127643988638108741277634571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85095992425405827518423047 127643988638108741277634571)
          ·
            refine ⟨191465982957163111916451857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127643988638108741277634571 191465982957163111916451857)
            ·
              refine ⟨143599487217872333937338893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191465982957163111916451857 143599487217872333937338893)
              ·
                refine ⟨53849807706702125226502085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143599487217872333937338893 53849807706702125226502085)
                ·
                  refine ⟨10096838945006648479969141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53849807706702125226502085 10096838945006648479969141)
                  ·
                    refine ⟨946578651094373294997107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10096838945006648479969141 946578651094373294997107)
                    ·
                      rfl

theorem cell22_2765183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2765183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765183 prefixEnd_2765183 := by exact prefixLift 2765183
  have htrace : WordTrace (prefixWord ++ tailWord_2765183) baseStart_2765183 baseEnd_2765183 := by
    simpa [prefixWord, tailWord_2765183, baseEnd_2765183] using wordTrace_append hprefix tailTrace_2765183
  have hstable : (prefixWord ++ tailWord_2765183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765183).length < 2 ^ (prefixWord ++ tailWord_2765183).sum := by decide
  have hdescent : baseEnd_2765183 < baseStart_2765183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765215 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_2765215 : Nat := 118140960795 + 2765215 * 2 ^ 59
def prefixEnd_2765215 : Nat := 4983230072969 + 3 ^ 40 * 2765215 * 2
def baseEnd_2765215 : Nat := 946589605348335878197009

theorem tailTrace_2765215 : CollatzResearch.WordTrace tailWord_2765215 prefixEnd_2765215 946589605348335878197009 := by
  unfold tailWord_2765215
  simp only [CollatzResearch.WordTrace]
  refine ⟨100855676677105790968481099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67237117784737193978987399 100855676677105790968481099)
  ·
    refine ⟨151283515015658686452721649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100855676677105790968481099 151283515015658686452721649)
    ·
      refine ⟨113462636261744014839541237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151283515015658686452721649 113462636261744014839541237)
      ·
        refine ⟨10637122149538501391206991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113462636261744014839541237 10637122149538501391206991)
        ·
          refine ⟨15955683224307752086810487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637122149538501391206991 15955683224307752086810487)
          ·
            refine ⟨23933524836461628130215731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15955683224307752086810487 23933524836461628130215731)
            ·
              refine ⟨35900287254692442195323597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23933524836461628130215731 35900287254692442195323597)
              ·
                refine ⟨13462607720509665823246349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35900287254692442195323597 13462607720509665823246349)
                ·
                  refine ⟨5048477895191124683717381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13462607720509665823246349 5048477895191124683717381)
                  ·
                    refine ⟨946589605348335878197009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048477895191124683717381 946589605348335878197009)
                    ·
                      rfl

theorem cell22_2765215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_2765215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765215 prefixEnd_2765215 := by exact prefixLift 2765215
  have htrace : WordTrace (prefixWord ++ tailWord_2765215) baseStart_2765215 baseEnd_2765215 := by
    simpa [prefixWord, tailWord_2765215, baseEnd_2765215] using wordTrace_append hprefix tailTrace_2765215
  have hstable : (prefixWord ++ tailWord_2765215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765215).length < 2 ^ (prefixWord ++ tailWord_2765215).sum := by decide
  have hdescent : baseEnd_2765215 < baseStart_2765215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765243 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_2765243 : Nat := 118140960795 + 2765243 * 2 ^ 59
def prefixEnd_2765243 : Nat := 4983230072969 + 3 ^ 40 * 2765243 * 2
def baseEnd_2765243 : Nat := 946599190320553138496923

theorem tailTrace_2765243 : CollatzResearch.WordTrace tailWord_2765243 prefixEnd_2765243 946599190320553138496923 := by
  unfold tailWord_2765243
  simp only [CollatzResearch.WordTrace]
  refine ⟨100856697921004351750500383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67237798614002901167000255 100856697921004351750500383)
  ·
    refine ⟨151285046881506527625750575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100856697921004351750500383 151285046881506527625750575)
    ·
      refine ⟨226927570322259791438625863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151285046881506527625750575 226927570322259791438625863)
      ·
        refine ⟨340391355483389687157938795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226927570322259791438625863 340391355483389687157938795)
        ·
          refine ⟨510587033225084530736908193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340391355483389687157938795 510587033225084530736908193)
          ·
            refine ⟨382940274918813398052681145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510587033225084530736908193 382940274918813398052681145)
            ·
              refine ⟨287205206189110048539510859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382940274918813398052681145 287205206189110048539510859)
              ·
                refine ⟨430807809283665072809266289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287205206189110048539510859 430807809283665072809266289)
                ·
                  refine ⟨323105856962748804606949717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430807809283665072809266289 323105856962748804606949717)
                  ·
                    refine ⟨946599190320553138496923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 323105856962748804606949717 946599190320553138496923)
                    ·
                      rfl

theorem cell22_2765243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_2765243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765243 prefixEnd_2765243 := by exact prefixLift 2765243
  have htrace : WordTrace (prefixWord ++ tailWord_2765243) baseStart_2765243 baseEnd_2765243 := by
    simpa [prefixWord, tailWord_2765243, baseEnd_2765243] using wordTrace_append hprefix tailTrace_2765243
  have hstable : (prefixWord ++ tailWord_2765243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765243).length < 2 ^ (prefixWord ++ tailWord_2765243).sum := by decide
  have hdescent : baseEnd_2765243 < baseStart_2765243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765266 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2765266 : Nat := 118140960795 + 2765266 * 2 ^ 59
def prefixEnd_2765266 : Nat := 4983230072969 + 3 ^ 40 * 2765266 * 2
def baseEnd_2765266 : Nat := 946607063690588745171853

theorem tailTrace_2765266 : CollatzResearch.WordTrace tailWord_2765266 prefixEnd_2765266 946607063690588745171853 := by
  unfold tailWord_2765266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214384199980256669646913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67238357866614017785725101 25214384199980256669646913)
  ·
    refine ⟨18910788149985192502235185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25214384199980256669646913 18910788149985192502235185)
    ·
      refine ⟨14183091112488894376676389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18910788149985192502235185 14183091112488894376676389)
      ·
        refine ⟨2659329583591667695626823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14183091112488894376676389 2659329583591667695626823)
        ·
          refine ⟨3988994375387501543440235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659329583591667695626823 3988994375387501543440235)
          ·
            refine ⟨5983491563081252315160353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988994375387501543440235 5983491563081252315160353)
            ·
              refine ⟨4487618672310939236370265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983491563081252315160353 4487618672310939236370265)
              ·
                refine ⟨3365714004233204427277699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487618672310939236370265 3365714004233204427277699)
                ·
                  refine ⟨5048571006349806640916549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3365714004233204427277699 5048571006349806640916549)
                  ·
                    refine ⟨946607063690588745171853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048571006349806640916549 946607063690588745171853)
                    ·
                      rfl

theorem cell22_2765266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2765266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765266 prefixEnd_2765266 := by exact prefixLift 2765266
  have htrace : WordTrace (prefixWord ++ tailWord_2765266) baseStart_2765266 baseEnd_2765266 := by
    simpa [prefixWord, tailWord_2765266, baseEnd_2765266] using wordTrace_append hprefix tailTrace_2765266
  have hstable : (prefixWord ++ tailWord_2765266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765266).length < 2 ^ (prefixWord ++ tailWord_2765266).sum := by decide
  have hdescent : baseEnd_2765266 < baseStart_2765266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765277 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2765277 : Nat := 118140960795 + 2765277 * 2 ^ 59
def prefixEnd_2765277 : Nat := 4983230072969 + 3 ^ 40 * 2765277 * 2
def baseEnd_2765277 : Nat := 946610829215388383146819

theorem tailTrace_2765277 : CollatzResearch.WordTrace tailWord_2765277 prefixEnd_2765277 946610829215388383146819 := by
  unfold tailWord_2765277
  simp only [CollatzResearch.WordTrace]
  refine ⟨100857938002881175557238085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67238625335254117038158723 100857938002881175557238085)
  ·
    refine ⟨18910863375540220416982141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100857938002881175557238085 18910863375540220416982141)
    ·
      refine ⟨7091573765827582656368303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18910863375540220416982141 7091573765827582656368303)
      ·
        refine ⟨10637360648741373984552455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091573765827582656368303 10637360648741373984552455)
        ·
          refine ⟨15956040973112060976828683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637360648741373984552455 15956040973112060976828683)
          ·
            refine ⟨23934061459668091465243025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15956040973112060976828683 23934061459668091465243025)
            ·
              refine ⟨17950546094751068598932269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23934061459668091465243025 17950546094751068598932269)
              ·
                refine ⟨6731454785531650724599601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17950546094751068598932269 6731454785531650724599601)
                ·
                  refine ⟨5048591089148738043449701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6731454785531650724599601 5048591089148738043449701)
                  ·
                    refine ⟨946610829215388383146819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048591089148738043449701 946610829215388383146819)
                    ·
                      rfl

theorem cell22_2765277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2765277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765277 prefixEnd_2765277 := by exact prefixLift 2765277
  have htrace : WordTrace (prefixWord ++ tailWord_2765277) baseStart_2765277 baseEnd_2765277 := by
    simpa [prefixWord, tailWord_2765277, baseEnd_2765277] using wordTrace_append hprefix tailTrace_2765277
  have hstable : (prefixWord ++ tailWord_2765277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765277).length < 2 ^ (prefixWord ++ tailWord_2765277).sum := by decide
  have hdescent : baseEnd_2765277 < baseStart_2765277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765354 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_2765354 : Nat := 118140960795 + 2765354 * 2 ^ 59
def prefixEnd_2765354 : Nat := 4983230072969 + 3 ^ 40 * 2765354 * 2
def baseEnd_2765354 : Nat := 315545729296328616323861

theorem tailTrace_2765354 : CollatzResearch.WordTrace tailWord_2765354 prefixEnd_2765354 315545729296328616323861 := by
  unfold tailWord_2765354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25215186605900554426947779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67240497615734811805194077 25215186605900554426947779)
  ·
    refine ⟨37822779908850831640421669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25215186605900554426947779 37822779908850831640421669)
    ·
      refine ⟨7091771232909530932579063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37822779908850831640421669 7091771232909530932579063)
      ·
        refine ⟨10637656849364296398868595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091771232909530932579063 10637656849364296398868595)
        ·
          refine ⟨15956485274046444598302893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10637656849364296398868595 15956485274046444598302893)
          ·
            refine ⟨5983681977767416724363585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15956485274046444598302893 5983681977767416724363585)
            ·
              refine ⟨4487761483325562543272689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983681977767416724363585 4487761483325562543272689)
              ·
                refine ⟨3365821112494171907454517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4487761483325562543272689 3365821112494171907454517)
                ·
                  refine ⟨315545729296328616323861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3365821112494171907454517 315545729296328616323861)
                  ·
                    rfl

theorem cell22_2765354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_2765354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765354 prefixEnd_2765354 := by exact prefixLift 2765354
  have htrace : WordTrace (prefixWord ++ tailWord_2765354) baseStart_2765354 baseEnd_2765354 := by
    simpa [prefixWord, tailWord_2765354, baseEnd_2765354] using wordTrace_append hprefix tailTrace_2765354
  have hstable : (prefixWord ++ tailWord_2765354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765354).length < 2 ^ (prefixWord ++ tailWord_2765354).sum := by decide
  have hdescent : baseEnd_2765354 < baseStart_2765354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765358 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2765358 : Nat := 118140960795 + 2765358 * 2 ^ 59
def prefixEnd_2765358 : Nat := 4983230072969 + 3 ^ 40 * 2765358 * 2
def baseEnd_2765358 : Nat := 946638557170731171871571

theorem tailTrace_2765358 : CollatzResearch.WordTrace tailWord_2765358 prefixEnd_2765358 946638557170731171871571 := by
  unfold tailWord_2765358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12607611539448465798867091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67240594877058484260624485 12607611539448465798867091)
  ·
    refine ⟨18911417309172698698300637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12607611539448465798867091 18911417309172698698300637)
    ·
      refine ⟨7091781490939762011862739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18911417309172698698300637 7091781490939762011862739)
      ·
        refine ⟨10637672236409643017794109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091781490939762011862739 10637672236409643017794109)
        ·
          refine ⟨3989127088653616131672791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10637672236409643017794109 3989127088653616131672791)
          ·
            refine ⟨5983690632980424197509187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989127088653616131672791 5983690632980424197509187)
            ·
              refine ⟨8975535949470636296263781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5983690632980424197509187 8975535949470636296263781)
              ·
                refine ⟨1682912990525744305549459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8975535949470636296263781 1682912990525744305549459)
                ·
                  refine ⟨2524369485788616458324189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1682912990525744305549459 2524369485788616458324189)
                  ·
                    refine ⟨946638557170731171871571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524369485788616458324189 946638557170731171871571)
                    ·
                      rfl

theorem cell22_2765358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2765358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765358 prefixEnd_2765358 := by exact prefixLift 2765358
  have htrace : WordTrace (prefixWord ++ tailWord_2765358) baseStart_2765358 baseEnd_2765358 := by
    simpa [prefixWord, tailWord_2765358, baseEnd_2765358] using wordTrace_append hprefix tailTrace_2765358
  have hstable : (prefixWord ++ tailWord_2765358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765358).length < 2 ^ (prefixWord ++ tailWord_2765358).sum := by decide
  have hdescent : baseEnd_2765358 < baseStart_2765358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765397 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2765397 : Nat := 118140960795 + 2765397 * 2 ^ 59
def prefixEnd_2765397 : Nat := 4983230072969 + 3 ^ 40 * 2765397 * 2
def baseEnd_2765397 : Nat := 946651907667748070146451

theorem tailTrace_2765397 : CollatzResearch.WordTrace tailWord_2765397 prefixEnd_2765397 946651907667748070146451 := by
  unfold tailWord_2765397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100862314762446436051606445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67241543174964290701070963 100862314762446436051606445)
  ·
    refine ⟨37823368035917413519352417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100862314762446436051606445 37823368035917413519352417)
    ·
      refine ⟨28367526026938060139514313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37823368035917413519352417 28367526026938060139514313)
      ·
        refine ⟨21275644520203545104635735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28367526026938060139514313 21275644520203545104635735)
        ·
          refine ⟨31913466780305317656953603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21275644520203545104635735 31913466780305317656953603)
          ·
            refine ⟨47870200170457976485430405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31913466780305317656953603 47870200170457976485430405)
            ·
              refine ⟨8975662531960870591018201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47870200170457976485430405 8975662531960870591018201)
              ·
                refine ⟨6731746898970652943263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8975662531960870591018201 6731746898970652943263651)
                ·
                  refine ⟨10097620348455979414895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6731746898970652943263651 10097620348455979414895477)
                  ·
                    refine ⟨946651907667748070146451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10097620348455979414895477 946651907667748070146451)
                    ·
                      rfl

theorem cell22_2765397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2765397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765397 prefixEnd_2765397 := by exact prefixLift 2765397
  have htrace : WordTrace (prefixWord ++ tailWord_2765397) baseStart_2765397 baseEnd_2765397 := by
    simpa [prefixWord, tailWord_2765397, baseEnd_2765397] using wordTrace_append hprefix tailTrace_2765397
  have hstable : (prefixWord ++ tailWord_2765397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765397).length < 2 ^ (prefixWord ++ tailWord_2765397).sum := by decide
  have hdescent : baseEnd_2765397 < baseStart_2765397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765399 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 4]
def baseStart_2765399 : Nat := 118140960795 + 2765399 * 2 ^ 59
def prefixEnd_2765399 : Nat := 4983230072969 + 3 ^ 40 * 2765399 * 2
def baseEnd_2765399 : Nat := 315550864102873577198815

theorem tailTrace_2765399 : CollatzResearch.WordTrace tailWord_2765399 prefixEnd_2765399 315550864102873577198815 := by
  unfold tailWord_2765399
  simp only [CollatzResearch.WordTrace]
  refine ⟨100862387708439190393179251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67241591805626126928786167 100862387708439190393179251)
  ·
    refine ⟨151293581562658785589768877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100862387708439190393179251 151293581562658785589768877)
    ·
      refine ⟨56735093085997044596163329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151293581562658785589768877 56735093085997044596163329)
      ·
        refine ⟨42551319814497783447122497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56735093085997044596163329 42551319814497783447122497)
        ·
          refine ⟨31913489860873337585341873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42551319814497783447122497 31913489860873337585341873)
          ·
            refine ⟨23935117395655003189006405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31913489860873337585341873 23935117395655003189006405)
            ·
              refine ⟨4487834511685313097938701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23935117395655003189006405 4487834511685313097938701)
              ·
                refine ⟨1682937941881992411727013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4487834511685313097938701 1682937941881992411727013)
                ·
                  refine ⟨315550864102873577198815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682937941881992411727013 315550864102873577198815)
                  ·
                    rfl

theorem cell22_2765399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 4].length) (baseStart_2765399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765399 prefixEnd_2765399 := by exact prefixLift 2765399
  have htrace : WordTrace (prefixWord ++ tailWord_2765399) baseStart_2765399 baseEnd_2765399 := by
    simpa [prefixWord, tailWord_2765399, baseEnd_2765399] using wordTrace_append hprefix tailTrace_2765399
  have hstable : (prefixWord ++ tailWord_2765399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765399).length < 2 ^ (prefixWord ++ tailWord_2765399).sum := by decide
  have hdescent : baseEnd_2765399 < baseStart_2765399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765412 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2765412 : Nat := 118140960795 + 2765412 * 2 ^ 59
def prefixEnd_2765412 : Nat := 4983230072969 + 3 ^ 40 * 2765412 * 2
def baseEnd_2765412 : Nat := 946657042474293031021405

theorem tailTrace_2765412 : CollatzResearch.WordTrace tailWord_2765412 prefixEnd_2765412 946657042474293031021405 := by
  unfold tailWord_2765412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50431430928696046806701245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67241907904928062408934993 50431430928696046806701245)
  ·
    refine ⟨18911786598261017552512967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50431430928696046806701245 18911786598261017552512967)
    ·
      refine ⟨28367679897391526328769451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18911786598261017552512967 28367679897391526328769451)
      ·
        refine ⟨42551519846087289493154177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28367679897391526328769451 42551519846087289493154177)
        ·
          refine ⟨31913639884565467119865633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42551519846087289493154177 31913639884565467119865633)
          ·
            refine ⟨23935229913424100339899225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31913639884565467119865633 23935229913424100339899225)
            ·
              refine ⟨17951422435068075254924419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23935229913424100339899225 17951422435068075254924419)
              ·
                refine ⟨26927133652602112882386629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17951422435068075254924419 26927133652602112882386629)
                ·
                  refine ⟨5048837559862896165447493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26927133652602112882386629 5048837559862896165447493)
                  ·
                    refine ⟨946657042474293031021405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5048837559862896165447493 946657042474293031021405)
                    ·
                      rfl

theorem cell22_2765412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2765412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765412 prefixEnd_2765412 := by exact prefixLift 2765412
  have htrace : WordTrace (prefixWord ++ tailWord_2765412) baseStart_2765412 baseEnd_2765412 := by
    simpa [prefixWord, tailWord_2765412, baseEnd_2765412] using wordTrace_append hprefix tailTrace_2765412
  have hstable : (prefixWord ++ tailWord_2765412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765412).length < 2 ^ (prefixWord ++ tailWord_2765412).sum := by decide
  have hdescent : baseEnd_2765412 < baseStart_2765412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765444 : List Nat := [2, 3, 2, 1, 3, 1, 4, 6]
def baseStart_2765444 : Nat := 118140960795 + 2765444 * 2 ^ 59
def prefixEnd_2765444 : Nat := 4983230072969 + 3 ^ 40 * 2765444 * 2
def baseEnd_2765444 : Nat := 105185332969806179357923

theorem tailTrace_2765444 : CollatzResearch.WordTrace tailWord_2765444 prefixEnd_2765444 105185332969806179357923 := by
  unfold tailWord_2765444
  simp only [CollatzResearch.WordTrace]
  refine ⟨50432014496638081539283693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67242685995517442052378257 50432014496638081539283693)
  ·
    refine ⟨18912005436239280577231385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50432014496638081539283693 18912005436239280577231385)
    ·
      refine ⟨14184004077179460432923539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18912005436239280577231385 14184004077179460432923539)
      ·
        refine ⟨21276006115769190649385309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14184004077179460432923539 21276006115769190649385309)
        ·
          refine ⟨7978502293413446493519491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21276006115769190649385309 7978502293413446493519491)
          ·
            refine ⟨11967753440120169740279237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978502293413446493519491 11967753440120169740279237)
            ·
              refine ⟨2243953770022531826302357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11967753440120169740279237 2243953770022531826302357)
              ·
                refine ⟨105185332969806179357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2243953770022531826302357 105185332969806179357923)
                ·
                  rfl

theorem cell22_2765444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_2765444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765444 prefixEnd_2765444 := by exact prefixLift 2765444
  have htrace : WordTrace (prefixWord ++ tailWord_2765444) baseStart_2765444 baseEnd_2765444 := by
    simpa [prefixWord, tailWord_2765444, baseEnd_2765444] using wordTrace_append hprefix tailTrace_2765444
  have hstable : (prefixWord ++ tailWord_2765444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765444).length < 2 ^ (prefixWord ++ tailWord_2765444).sum := by decide
  have hdescent : baseEnd_2765444 < baseStart_2765444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765482 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2765482 : Nat := 118140960795 + 2765482 * 2 ^ 59
def prefixEnd_2765482 : Nat := 4983230072969 + 3 ^ 40 * 2765482 * 2
def baseEnd_2765482 : Nat := 946681004904836181771191

theorem tailTrace_2765482 : CollatzResearch.WordTrace tailWord_2765482 prefixEnd_2765482 946681004904836181771191 := by
  unfold tailWord_2765482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25216353741784623892112675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67243609978092330378967133 25216353741784623892112675)
  ·
    refine ⟨37824530612676935838169013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25216353741784623892112675 37824530612676935838169013)
    ·
      refine ⟨3546049744938462734828345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37824530612676935838169013 3546049744938462734828345)
      ·
        refine ⟨2659537308703847051121259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546049744938462734828345 2659537308703847051121259)
        ·
          refine ⟨3989305963055770576681889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659537308703847051121259 3989305963055770576681889)
          ·
            refine ⟨2991979472291827932511417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3989305963055770576681889 2991979472291827932511417)
            ·
              refine ⟨2243984604218870949383563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2991979472291827932511417 2243984604218870949383563)
              ·
                refine ⟨3365976906328306424075345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243984604218870949383563 3365976906328306424075345)
                ·
                  refine ⟨2524482679746229818056509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365976906328306424075345 2524482679746229818056509)
                  ·
                    refine ⟨946681004904836181771191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524482679746229818056509 946681004904836181771191)
                    ·
                      rfl

theorem cell22_2765482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2765482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765482 prefixEnd_2765482 := by exact prefixLift 2765482
  have htrace : WordTrace (prefixWord ++ tailWord_2765482) baseStart_2765482 baseEnd_2765482 := by
    simpa [prefixWord, tailWord_2765482, baseEnd_2765482] using wordTrace_append hprefix tailTrace_2765482
  have hstable : (prefixWord ++ tailWord_2765482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765482).length < 2 ^ (prefixWord ++ tailWord_2765482).sum := by decide
  have hdescent : baseEnd_2765482 < baseStart_2765482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765547 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_2765547 : Nat := 118140960795 + 2765547 * 2 ^ 59
def prefixEnd_2765547 : Nat := 4983230072969 + 3 ^ 40 * 2765547 * 2
def baseEnd_2765547 : Nat := 946703255733197678895991

theorem tailTrace_2765547 : CollatzResearch.WordTrace tailWord_2765547 prefixEnd_2765547 946703255733197678895991 := by
  unfold tailWord_2765547
  simp only [CollatzResearch.WordTrace]
  refine ⟨100867785711903011669566895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67245190474602007779711263 100867785711903011669566895)
  ·
    refine ⟨151301678567854517504350343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100867785711903011669566895 151301678567854517504350343)
    ·
      refine ⟨226952517851781776256525515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151301678567854517504350343 226952517851781776256525515)
      ·
        refine ⟨340428776777672664384788273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226952517851781776256525515 340428776777672664384788273)
        ·
          refine ⟨255321582583254498288591205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340428776777672664384788273 255321582583254498288591205)
          ·
            refine ⟨47872796734360218429110851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255321582583254498288591205 47872796734360218429110851)
            ·
              refine ⟨71809195101540327643666277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47872796734360218429110851 71809195101540327643666277)
              ·
                refine ⟨13464224081538811433187427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71809195101540327643666277 13464224081538811433187427)
                ·
                  refine ⟨20196336122308217149781141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464224081538811433187427 20196336122308217149781141)
                  ·
                    refine ⟨946703255733197678895991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20196336122308217149781141 946703255733197678895991)
                    ·
                      rfl

theorem cell22_2765547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_2765547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765547 prefixEnd_2765547 := by exact prefixLift 2765547
  have htrace : WordTrace (prefixWord ++ tailWord_2765547) baseStart_2765547 baseEnd_2765547 := by
    simpa [prefixWord, tailWord_2765547, baseEnd_2765547] using wordTrace_append hprefix tailTrace_2765547
  have hstable : (prefixWord ++ tailWord_2765547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765547).length < 2 ^ (prefixWord ++ tailWord_2765547).sum := by decide
  have hdescent : baseEnd_2765547 < baseStart_2765547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765562 : List Nat := [3, 1, 1, 1, 1, 3, 2, 10]
def baseStart_2765562 : Nat := 118140960795 + 2765562 * 2 ^ 59
def prefixEnd_2765562 : Nat := 4983230072969 + 3 ^ 40 * 2765562 * 2
def baseEnd_2765562 : Nat := 105189821171082515530105

theorem tailTrace_2765562 : CollatzResearch.WordTrace tailWord_2765562 prefixEnd_2765562 105189821171082515530105 := by
  unfold tailWord_2765562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217083201712167307840735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67245555204565779487575293 25217083201712167307840735)
  ·
    refine ⟨37825624802568250961761103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25217083201712167307840735 37825624802568250961761103)
    ·
      refine ⟨56738437203852376442641655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37825624802568250961761103 56738437203852376442641655)
      ·
        refine ⟨85107655805778564663962483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56738437203852376442641655 85107655805778564663962483)
        ·
          refine ⟨127661483708667846995943725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85107655805778564663962483 127661483708667846995943725)
          ·
            refine ⟨47873056390750442623478897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127661483708667846995943725 47873056390750442623478897)
            ·
              refine ⟨35904792293062831967609173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47873056390750442623478897 35904792293062831967609173)
              ·
                refine ⟨105189821171082515530105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35904792293062831967609173 105189821171082515530105)
                ·
                  rfl

theorem cell22_2765562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_2765562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765562 prefixEnd_2765562 := by exact prefixLift 2765562
  have htrace : WordTrace (prefixWord ++ tailWord_2765562) baseStart_2765562 baseEnd_2765562 := by
    simpa [prefixWord, tailWord_2765562, baseEnd_2765562] using wordTrace_append hprefix tailTrace_2765562
  have hstable : (prefixWord ++ tailWord_2765562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765562).length < 2 ^ (prefixWord ++ tailWord_2765562).sum := by decide
  have hdescent : baseEnd_2765562 < baseStart_2765562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765564 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_2765564 : Nat := 118140960795 + 2765564 * 2 ^ 59
def prefixEnd_2765564 : Nat := 4983230072969 + 3 ^ 40 * 2765564 * 2
def baseEnd_2765564 : Nat := 946709075180615301220939

theorem tailTrace_2765564 : CollatzResearch.WordTrace tailWord_2765564 prefixEnd_2765564 946709075180615301220939 := by
  unfold tailWord_2765564
  simp only [CollatzResearch.WordTrace]
  refine ⟨50434202876420711786467873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67245603835227615715290497 50434202876420711786467873)
  ·
    refine ⟨37825652157315533839850905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50434202876420711786467873 37825652157315533839850905)
    ·
      refine ⟨28369239117986650379888179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37825652157315533839850905 28369239117986650379888179)
      ·
        refine ⟨42553858676979975569832269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28369239117986650379888179 42553858676979975569832269)
        ·
          refine ⟨15957697003867490838687101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42553858676979975569832269 15957697003867490838687101)
          ·
            refine ⟨5984136376450309064507663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15957697003867490838687101 5984136376450309064507663)
            ·
              refine ⟨8976204564675463596761495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984136376450309064507663 8976204564675463596761495)
              ·
                refine ⟨13464306847013195395142243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976204564675463596761495 13464306847013195395142243)
                ·
                  refine ⟨20196460270519793092713365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13464306847013195395142243 20196460270519793092713365)
                  ·
                    refine ⟨946709075180615301220939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20196460270519793092713365 946709075180615301220939)
                    ·
                      rfl

theorem cell22_2765564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_2765564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765564 prefixEnd_2765564 := by exact prefixLift 2765564
  have htrace : WordTrace (prefixWord ++ tailWord_2765564) baseStart_2765564 baseEnd_2765564 := by
    simpa [prefixWord, tailWord_2765564, baseEnd_2765564] using wordTrace_append hprefix tailTrace_2765564
  have hstable : (prefixWord ++ tailWord_2765564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765564).length < 2 ^ (prefixWord ++ tailWord_2765564).sum := by decide
  have hdescent : baseEnd_2765564 < baseStart_2765564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765566 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2765566 : Nat := 118140960795 + 2765566 * 2 ^ 59
def prefixEnd_2765566 : Nat := 4983230072969 + 3 ^ 40 * 2765566 * 2
def baseEnd_2765566 : Nat := 946709759821487962670933

theorem tailTrace_2765566 : CollatzResearch.WordTrace tailWord_2765566 prefixEnd_2765566 946709759821487962670933 := by
  unfold tailWord_2765566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12608559837354272239313569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67245652465889451943005701 12608559837354272239313569)
  ·
    refine ⟨9456419878015704179485177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12608559837354272239313569 9456419878015704179485177)
    ·
      refine ⟨7092314908511778134613883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9456419878015704179485177 7092314908511778134613883)
      ·
        refine ⟨10638472362767667201920825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092314908511778134613883 10638472362767667201920825)
        ·
          refine ⟨7978854272075750401440619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10638472362767667201920825 7978854272075750401440619)
          ·
            refine ⟨11968281408113625602160929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7978854272075750401440619 11968281408113625602160929)
            ·
              refine ⟨8976211056085219201620697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11968281408113625602160929 8976211056085219201620697)
              ·
                refine ⟨6732158292063914401215523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8976211056085219201620697 6732158292063914401215523)
                ·
                  refine ⟨10098237438095871601823285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732158292063914401215523 10098237438095871601823285)
                  ·
                    refine ⟨946709759821487962670933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10098237438095871601823285 946709759821487962670933)
                    ·
                      rfl

theorem cell22_2765566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2765566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765566 prefixEnd_2765566 := by exact prefixLift 2765566
  have htrace : WordTrace (prefixWord ++ tailWord_2765566) baseStart_2765566 baseEnd_2765566 := by
    simpa [prefixWord, tailWord_2765566, baseEnd_2765566] using wordTrace_append hprefix tailTrace_2765566
  have hstable : (prefixWord ++ tailWord_2765566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765566).length < 2 ^ (prefixWord ++ tailWord_2765566).sum := by decide
  have hdescent : baseEnd_2765566 < baseStart_2765566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765570 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2765570 : Nat := 118140960795 + 2765570 * 2 ^ 59
def prefixEnd_2765570 : Nat := 4983230072969 + 3 ^ 40 * 2765570 * 2
def baseEnd_2765570 : Nat := 946711129103233285570921

theorem tailTrace_2765570 : CollatzResearch.WordTrace tailWord_2765570 prefixEnd_2765570 946711129103233285570921 := by
  unfold tailWord_2765570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217156147704921649413541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67245749727213124398436109 25217156147704921649413541)
  ·
    refine ⟨4728216777694672809265039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25217156147704921649413541 4728216777694672809265039)
    ·
      refine ⟨7092325166542009213897559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4728216777694672809265039 7092325166542009213897559)
      ·
        refine ⟨10638487749813013820846339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092325166542009213897559 10638487749813013820846339)
        ·
          refine ⟨15957731624719520731269509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10638487749813013820846339 15957731624719520731269509)
          ·
            refine ⟨2992074679634910137113033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15957731624719520731269509 2992074679634910137113033)
            ·
              refine ⟨2244056009726182602834775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992074679634910137113033 2244056009726182602834775)
              ·
                refine ⟨3366084014589273904252163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244056009726182602834775 3366084014589273904252163)
                ·
                  refine ⟨5049126021883910856378245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366084014589273904252163 5049126021883910856378245)
                  ·
                    refine ⟨946711129103233285570921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049126021883910856378245 946711129103233285570921)
                    ·
                      rfl

theorem cell22_2765570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2765570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765570 prefixEnd_2765570 := by exact prefixLift 2765570
  have htrace : WordTrace (prefixWord ++ tailWord_2765570) baseStart_2765570 baseEnd_2765570 := by
    simpa [prefixWord, tailWord_2765570, baseEnd_2765570] using wordTrace_append hprefix tailTrace_2765570
  have hstable : (prefixWord ++ tailWord_2765570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765570).length < 2 ^ (prefixWord ++ tailWord_2765570).sum := by decide
  have hdescent : baseEnd_2765570 < baseStart_2765570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765613 : List Nat := [1, 5, 3, 2, 1, 1, 1, 8]
def baseStart_2765613 : Nat := 118140960795 + 2765613 * 2 ^ 59
def prefixEnd_2765613 : Nat := 4983230072969 + 3 ^ 40 * 2765613 * 2
def baseEnd_2765613 : Nat := 105191760986888389638421

theorem tailTrace_2765613 : CollatzResearch.WordTrace tailWord_2765613 prefixEnd_2765613 105191760986888389638421 := by
  unfold tailWord_2765613
  simp only [CollatzResearch.WordTrace]
  refine ⟨100870192929663904941469493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67246795286442603294312995 100870192929663904941469493)
  ·
    refine ⟨9456580587155991088262765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100870192929663904941469493 9456580587155991088262765)
    ·
      refine ⟨3546217720183496658098537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9456580587155991088262765 3546217720183496658098537)
      ·
        refine ⟨2659663290137622493573903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3546217720183496658098537 2659663290137622493573903)
        ·
          refine ⟨3989494935206433740360855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659663290137622493573903 3989494935206433740360855)
          ·
            refine ⟨5984242402809650610541283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989494935206433740360855 5984242402809650610541283)
            ·
              refine ⟨8976363604214475915811925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984242402809650610541283 8976363604214475915811925)
              ·
                refine ⟨105191760986888389638421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8976363604214475915811925 105191760986888389638421)
                ·
                  rfl

theorem cell22_2765613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 8].length) (baseStart_2765613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765613 prefixEnd_2765613 := by exact prefixLift 2765613
  have htrace : WordTrace (prefixWord ++ tailWord_2765613) baseStart_2765613 baseEnd_2765613 := by
    simpa [prefixWord, tailWord_2765613, baseEnd_2765613] using wordTrace_append hprefix tailTrace_2765613
  have hstable : (prefixWord ++ tailWord_2765613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765613).length < 2 ^ (prefixWord ++ tailWord_2765613).sum := by decide
  have hdescent : baseEnd_2765613 < baseStart_2765613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765658 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_2765658 : Nat := 118140960795 + 2765658 * 2 ^ 59
def prefixEnd_2765658 : Nat := 4983230072969 + 3 ^ 40 * 2765658 * 2
def baseEnd_2765658 : Nat := 315580417767210129790217

theorem tailTrace_2765658 : CollatzResearch.WordTrace tailWord_2765658 prefixEnd_2765658 315580417767210129790217 := by
  unfold tailWord_2765658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217958553625219406714407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67247889476333918417905085 25217958553625219406714407)
  ·
    refine ⟨37826937830437829110071611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25217958553625219406714407 37826937830437829110071611)
    ·
      refine ⟨56740406745656743665107417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37826937830437829110071611 56740406745656743665107417)
      ·
        refine ⟨42555305059242557748830563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56740406745656743665107417 42555305059242557748830563)
        ·
          refine ⟨63832957588863836623245845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42555305059242557748830563 63832957588863836623245845)
          ·
            refine ⟨2992169886977992341714649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63832957588863836623245845 2992169886977992341714649)
            ·
              refine ⟨2244127415233494256285987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992169886977992341714649 2244127415233494256285987)
              ·
                refine ⟨3366191122850241384428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244127415233494256285987 3366191122850241384428981)
                ·
                  refine ⟨315580417767210129790217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3366191122850241384428981 315580417767210129790217)
                  ·
                    rfl

theorem cell22_2765658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_2765658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765658 prefixEnd_2765658 := by exact prefixLift 2765658
  have htrace : WordTrace (prefixWord ++ tailWord_2765658) baseStart_2765658 baseEnd_2765658 := by
    simpa [prefixWord, tailWord_2765658, baseEnd_2765658] using wordTrace_append hprefix tailTrace_2765658
  have hstable : (prefixWord ++ tailWord_2765658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765658).length < 2 ^ (prefixWord ++ tailWord_2765658).sum := by decide
  have hdescent : baseEnd_2765658 < baseStart_2765658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765669 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 6]
def baseStart_2765669 : Nat := 118140960795 + 2765669 * 2 ^ 59
def prefixEnd_2765669 : Nat := 4983230072969 + 3 ^ 40 * 2765669 * 2
def baseEnd_2765669 : Nat := 315581672942143342448539

theorem tailTrace_2765669 : CollatzResearch.WordTrace tailWord_2765669 prefixEnd_2765669 315581672942143342448539 := by
  unfold tailWord_2765669
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872235417461026505508061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248156944974017670338707 100872235417461026505508061)
  ·
    refine ⟨37827088281547884939565523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100872235417461026505508061 37827088281547884939565523)
    ·
      refine ⟨56740632422321827409348285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37827088281547884939565523 56740632422321827409348285)
      ·
        refine ⟨21277737158370685278505607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56740632422321827409348285 21277737158370685278505607)
        ·
          refine ⟨31916605737556027917758411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277737158370685278505607 31916605737556027917758411)
          ·
            refine ⟨47874908606334041876637617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31916605737556027917758411 47874908606334041876637617)
            ·
              refine ⟨35906181454750531407478213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47874908606334041876637617 35906181454750531407478213)
              ·
                refine ⟨6732409022765724638902165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35906181454750531407478213 6732409022765724638902165)
                ·
                  refine ⟨315581672942143342448539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6732409022765724638902165 315581672942143342448539)
                  ·
                    rfl

theorem cell22_2765669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_2765669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765669 prefixEnd_2765669 := by exact prefixLift 2765669
  have htrace : WordTrace (prefixWord ++ tailWord_2765669) baseStart_2765669 baseEnd_2765669 := by
    simpa [prefixWord, tailWord_2765669, baseEnd_2765669] using wordTrace_append hprefix tailTrace_2765669
  have hstable : (prefixWord ++ tailWord_2765669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765669).length < 2 ^ (prefixWord ++ tailWord_2765669).sum := by decide
  have hdescent : baseEnd_2765669 < baseStart_2765669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765671 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2765671 : Nat := 118140960795 + 2765671 * 2 ^ 59
def prefixEnd_2765671 : Nat := 4983230072969 + 3 ^ 40 * 2765671 * 2
def baseEnd_2765671 : Nat := 946745703467302688795611

theorem tailTrace_2765671 : CollatzResearch.WordTrace tailWord_2765671 prefixEnd_2765671 946745703467302688795611 := by
  unfold tailWord_2765671
  simp only [CollatzResearch.WordTrace]
  refine ⟨100872308363453780847080867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248205575635853898053911 100872308363453780847080867)
  ·
    refine ⟨151308462545180671270621301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100872308363453780847080867 151308462545180671270621301)
    ·
      refine ⟨14185168363610687931620747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151308462545180671270621301 14185168363610687931620747)
      ·
        refine ⟨21277752545416031897431121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185168363610687931620747 21277752545416031897431121)
        ·
          refine ⟨15958314409062023923073341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21277752545416031897431121 15958314409062023923073341)
          ·
            refine ⟨5984367903398258971152503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15958314409062023923073341 5984367903398258971152503)
            ·
              refine ⟨8976551855097388456728755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984367903398258971152503 8976551855097388456728755)
              ·
                refine ⟨13464827782646082685093133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8976551855097388456728755 13464827782646082685093133)
                ·
                  refine ⟨5049310418492281006909925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13464827782646082685093133 5049310418492281006909925)
                  ·
                    refine ⟨946745703467302688795611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049310418492281006909925 946745703467302688795611)
                    ·
                      rfl

theorem cell22_2765671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2765671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765671 prefixEnd_2765671 := by exact prefixLift 2765671
  have htrace : WordTrace (prefixWord ++ tailWord_2765671) baseStart_2765671 baseEnd_2765671 := by
    simpa [prefixWord, tailWord_2765671, baseEnd_2765671] using wordTrace_append hprefix tailTrace_2765671
  have hstable : (prefixWord ++ tailWord_2765671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765671).length < 2 ^ (prefixWord ++ tailWord_2765671).sum := by decide
  have hdescent : baseEnd_2765671 < baseStart_2765671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765703 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 4]
def baseStart_2765703 : Nat := 118140960795 + 2765703 * 2 ^ 59
def prefixEnd_2765703 : Nat := 4983230072969 + 3 ^ 40 * 2765703 * 2
def baseEnd_2765703 : Nat := 315585552573755090665171

theorem tailTrace_2765703 : CollatzResearch.WordTrace tailWord_2765703 prefixEnd_2765703 315585552573755090665171 := by
  unfold tailWord_2765703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100873475499337850312245763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67248983666225233541497175 100873475499337850312245763)
  ·
    refine ⟨151310213249006775468368645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100873475499337850312245763 151310213249006775468368645)
    ·
      refine ⟨28370664984188770400319121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151310213249006775468368645 28370664984188770400319121)
      ·
        refine ⟨21277998738141577800239341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28370664984188770400319121 21277998738141577800239341)
        ·
          refine ⟨7979249526803091675089753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21277998738141577800239341 7979249526803091675089753)
          ·
            refine ⟨5984437145102318756317315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7979249526803091675089753 5984437145102318756317315)
            ·
              refine ⟨8976655717653478134475973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5984437145102318756317315 8976655717653478134475973)
              ·
                refine ⟨1683122947060027150214245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8976655717653478134475973 1683122947060027150214245)
                ·
                  refine ⟨315585552573755090665171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683122947060027150214245 315585552573755090665171)
                  ·
                    rfl

theorem cell22_2765703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 4].length) (baseStart_2765703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765703 prefixEnd_2765703 := by exact prefixLift 2765703
  have htrace : WordTrace (prefixWord ++ tailWord_2765703) baseStart_2765703 baseEnd_2765703 := by
    simpa [prefixWord, tailWord_2765703, baseEnd_2765703] using wordTrace_append hprefix tailTrace_2765703
  have hstable : (prefixWord ++ tailWord_2765703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765703).length < 2 ^ (prefixWord ++ tailWord_2765703).sum := by decide
  have hdescent : baseEnd_2765703 < baseStart_2765703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765716 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2765716 : Nat := 118140960795 + 2765716 * 2 ^ 59
def prefixEnd_2765716 : Nat := 4983230072969 + 3 ^ 40 * 2765716 * 2
def baseEnd_2765716 : Nat := 946761107886937571420473

theorem tailTrace_2765716 : CollatzResearch.WordTrace tailWord_2765716 prefixEnd_2765716 946761107886937571420473 := by
  unfold tailWord_2765716
  simp only [CollatzResearch.WordTrace]
  refine ⟨50436974824145376766234501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67249299765527169021646001 50436974824145376766234501)
  ·
    refine ⟨9456932779527258143668969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50436974824145376766234501 9456932779527258143668969)
    ·
      refine ⟨7092699584645443607751727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9456932779527258143668969 7092699584645443607751727)
      ·
        refine ⟨10639049376968165411627591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7092699584645443607751727 10639049376968165411627591)
        ·
          refine ⟨15958574065452248117441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10639049376968165411627591 15958574065452248117441387)
          ·
            refine ⟨23937861098178372176162081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15958574065452248117441387 23937861098178372176162081)
            ·
              refine ⟨17953395823633779132121561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23937861098178372176162081 17953395823633779132121561)
              ·
                refine ⟨13465046867725334349091171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17953395823633779132121561 13465046867725334349091171)
                ·
                  refine ⟨20197570301588001523636757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13465046867725334349091171 20197570301588001523636757)
                  ·
                    refine ⟨946761107886937571420473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20197570301588001523636757 946761107886937571420473)
                    ·
                      rfl

theorem cell22_2765716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2765716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765716 prefixEnd_2765716 := by exact prefixLift 2765716
  have htrace : WordTrace (prefixWord ++ tailWord_2765716) baseStart_2765716 baseEnd_2765716 := by
    simpa [prefixWord, tailWord_2765716, baseEnd_2765716] using wordTrace_append hprefix tailTrace_2765716
  have hstable : (prefixWord ++ tailWord_2765716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765716).length < 2 ^ (prefixWord ++ tailWord_2765716).sum := by decide
  have hdescent : baseEnd_2765716 < baseStart_2765716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765748 : List Nat := [2, 5, 2, 1, 1, 2, 9]
def baseStart_2765748 : Nat := 118140960795 + 2765748 * 2 ^ 59
def prefixEnd_2765748 : Nat := 4983230072969 + 3 ^ 40 * 2765748 * 2
def baseEnd_2765748 : Nat := 35065631931144450171125

theorem tailTrace_2765748 : CollatzResearch.WordTrace tailWord_2765748 prefixEnd_2765748 35065631931144450171125 := by
  unfold tailWord_2765748
  simp only [CollatzResearch.WordTrace]
  refine ⟨50437558392087411498816949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67250077856116548665089265 50437558392087411498816949)
  ·
    refine ⟨4728521099258194828014089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50437558392087411498816949 4728521099258194828014089)
    ·
      refine ⟨3546390824443646121010567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4728521099258194828014089 3546390824443646121010567)
      ·
        refine ⟨5319586236665469181515851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546390824443646121010567 5319586236665469181515851)
        ·
          refine ⟨7979379354998203772273777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319586236665469181515851 7979379354998203772273777)
          ·
            refine ⟨5984534516248652829205333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7979379354998203772273777 5984534516248652829205333)
            ·
              refine ⟨35065631931144450171125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5984534516248652829205333 35065631931144450171125)
              ·
                rfl

theorem cell22_2765748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 9].length) (baseStart_2765748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765748 prefixEnd_2765748 := by exact prefixLift 2765748
  have htrace : WordTrace (prefixWord ++ tailWord_2765748) baseStart_2765748 baseEnd_2765748 := by
    simpa [prefixWord, tailWord_2765748, baseEnd_2765748] using wordTrace_append hprefix tailTrace_2765748
  have hstable : (prefixWord ++ tailWord_2765748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765748).length < 2 ^ (prefixWord ++ tailWord_2765748).sum := by decide
  have hdescent : baseEnd_2765748 < baseStart_2765748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765814 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_2765814 : Nat := 118140960795 + 2765814 * 2 ^ 59
def prefixEnd_2765814 : Nat := 4983230072969 + 3 ^ 40 * 2765814 * 2
def baseEnd_2765814 : Nat := 946794655289697982470173

theorem tailTrace_2765814 : CollatzResearch.WordTrace tailWord_2765814 prefixEnd_2765814 946794655289697982470173 := by
  unfold tailWord_2765814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304845250120982266846031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67251682667957144179690997 6304845250120982266846031)
  ·
    refine ⟨9457267875181473400269047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304845250120982266846031 9457267875181473400269047)
    ·
      refine ⟨14185901812772210100403571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9457267875181473400269047 14185901812772210100403571)
      ·
        refine ⟨21278852719158315150605357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185901812772210100403571 21278852719158315150605357)
        ·
          refine ⟨7979569769684368181477009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21278852719158315150605357 7979569769684368181477009)
          ·
            refine ⟨5984677327263276136107757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7979569769684368181477009 5984677327263276136107757)
            ·
              refine ⟨2244253997723728551040409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5984677327263276136107757 2244253997723728551040409)
              ·
                refine ⟨1683190498292796413280307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244253997723728551040409 1683190498292796413280307)
                ·
                  refine ⟨2524785747439194619920461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683190498292796413280307 2524785747439194619920461)
                  ·
                    refine ⟨946794655289697982470173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524785747439194619920461 946794655289697982470173)
                    ·
                      rfl

theorem cell22_2765814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_2765814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765814 prefixEnd_2765814 := by exact prefixLift 2765814
  have htrace : WordTrace (prefixWord ++ tailWord_2765814) baseStart_2765814 baseEnd_2765814 := by
    simpa [prefixWord, tailWord_2765814, baseEnd_2765814] using wordTrace_append hprefix tailTrace_2765814
  have hstable : (prefixWord ++ tailWord_2765814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765814).length < 2 ^ (prefixWord ++ tailWord_2765814).sum := by decide
  have hdescent : baseEnd_2765814 < baseStart_2765814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765866 : List Nat := [3, 1, 4, 1, 13]
def baseStart_2765866 : Nat := 118140960795 + 2765866 * 2 ^ 59
def prefixEnd_2765866 : Nat := 4983230072969 + 3 ^ 40 * 2765866 * 2
def baseEnd_2765866 : Nat := 3896347555359618025391

theorem tailTrace_2765866 : CollatzResearch.WordTrace tailWord_2765866 prefixEnd_2765866 3896347555359618025391 := by
  unfold tailWord_2765866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219855149436832287607363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67252947065164886100286301 25219855149436832287607363)
  ·
    refine ⟨37829782724155248431411045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25219855149436832287607363 37829782724155248431411045)
    ·
      refine ⟨7093084260779109080889571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37829782724155248431411045 7093084260779109080889571)
      ·
        refine ⟨10639626391168663621334357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093084260779109080889571 10639626391168663621334357)
        ·
          refine ⟨3896347555359618025391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10639626391168663621334357 3896347555359618025391)
          ·
            rfl

theorem cell22_2765866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 13].length) (baseStart_2765866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765866 prefixEnd_2765866 := by exact prefixLift 2765866
  have htrace : WordTrace (prefixWord ++ tailWord_2765866) baseStart_2765866 baseEnd_2765866 := by
    simpa [prefixWord, tailWord_2765866, baseEnd_2765866] using wordTrace_append hprefix tailTrace_2765866
  have hstable : (prefixWord ++ tailWord_2765866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765866).length < 2 ^ (prefixWord ++ tailWord_2765866).sum := by decide
  have hdescent : baseEnd_2765866 < baseStart_2765866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765896 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_2765896 : Nat := 118140960795 + 2765896 * 2 ^ 59
def prefixEnd_2765896 : Nat := 4983230072969 + 3 ^ 40 * 2765896 * 2
def baseEnd_2765896 : Nat := 946822725565477101919921

theorem tailTrace_2765896 : CollatzResearch.WordTrace tailWord_2765896 prefixEnd_2765896 946822725565477101919921 := by
  unfold tailWord_2765896
  simp only [CollatzResearch.WordTrace]
  refine ⟨50440257393819322137010771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67253676525092429516014361 50440257393819322137010771)
  ·
    refine ⟨75660386090728983205516157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50440257393819322137010771 75660386090728983205516157)
    ·
      refine ⟨28372644784023368702068559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75660386090728983205516157 28372644784023368702068559)
      ·
        refine ⟨42558967176035053053102839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28372644784023368702068559 42558967176035053053102839)
        ·
          refine ⟨63838450764052579579654259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42558967176035053053102839 63838450764052579579654259)
          ·
            refine ⟨95757676146078869369481389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63838450764052579579654259 95757676146078869369481389)
            ·
              refine ⟨35909128554779576013555521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95757676146078869369481389 35909128554779576013555521)
              ·
                refine ⟨26931846416084682010166641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35909128554779576013555521 26931846416084682010166641)
                ·
                  refine ⟨20198884812063511507624981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26931846416084682010166641 20198884812063511507624981)
                  ·
                    refine ⟨946822725565477101919921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20198884812063511507624981 946822725565477101919921)
                    ·
                      rfl

theorem cell22_2765896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_2765896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765896 prefixEnd_2765896 := by exact prefixLift 2765896
  have htrace : WordTrace (prefixWord ++ tailWord_2765896) baseStart_2765896 baseEnd_2765896 := by
    simpa [prefixWord, tailWord_2765896, baseEnd_2765896] using wordTrace_append hprefix tailTrace_2765896
  have hstable : (prefixWord ++ tailWord_2765896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765896).length < 2 ^ (prefixWord ++ tailWord_2765896).sum := by decide
  have hdescent : baseEnd_2765896 < baseStart_2765896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765898 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2765898 : Nat := 118140960795 + 2765898 * 2 ^ 59
def prefixEnd_2765898 : Nat := 4983230072969 + 3 ^ 40 * 2765898 * 2
def baseEnd_2765898 : Nat := 946823410206349763369915

theorem tailTrace_2765898 : CollatzResearch.WordTrace tailWord_2765898 prefixEnd_2765898 946823410206349763369915 := by
  unfold tailWord_2765898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25220146933407849653898587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67253725155754265743729565 25220146933407849653898587)
  ·
    refine ⟨37830220400111774480847881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25220146933407849653898587 37830220400111774480847881)
    ·
      refine ⟨28372665300083830860635911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37830220400111774480847881 28372665300083830860635911)
      ·
        refine ⟨42558997950125746290953867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28372665300083830860635911 42558997950125746290953867)
        ·
          refine ⟨63838496925188619436430801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42558997950125746290953867 63838496925188619436430801)
          ·
            refine ⟨47878872693891464577323101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63838496925188619436430801 47878872693891464577323101)
            ·
              refine ⟨17954577260209299216496163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47878872693891464577323101 17954577260209299216496163)
              ·
                refine ⟨26931865890313948824744245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17954577260209299216496163 26931865890313948824744245)
                ·
                  refine ⟨2524862427216932702319773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26931865890313948824744245 2524862427216932702319773)
                  ·
                    refine ⟨946823410206349763369915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524862427216932702319773 946823410206349763369915)
                    ·
                      rfl

theorem cell22_2765898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2765898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765898 prefixEnd_2765898 := by exact prefixLift 2765898
  have htrace : WordTrace (prefixWord ++ tailWord_2765898) baseStart_2765898 baseEnd_2765898 := by
    simpa [prefixWord, tailWord_2765898, baseEnd_2765898] using wordTrace_append hprefix tailTrace_2765898
  have hstable : (prefixWord ++ tailWord_2765898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765898).length < 2 ^ (prefixWord ++ tailWord_2765898).sum := by decide
  have hdescent : baseEnd_2765898 < baseStart_2765898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765911 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 7]
def baseStart_2765911 : Nat := 118140960795 + 2765911 * 2 ^ 59
def prefixEnd_2765911 : Nat := 4983230072969 + 3 ^ 40 * 2765911 * 2
def baseEnd_2765911 : Nat := 315609286790674020931625

theorem tailTrace_2765911 : CollatzResearch.WordTrace tailWord_2765911 prefixEnd_2765911 315609286790674020931625 := by
  unfold tailWord_2765911
  simp only [CollatzResearch.WordTrace]
  refine ⟨100881061882584301835817587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67254041255056201223878391 100881061882584301835817587)
  ·
    refine ⟨151321592823876452753726381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100881061882584301835817587 151321592823876452753726381)
    ·
      refine ⟨56745597308953669782647393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151321592823876452753726381 56745597308953669782647393)
      ·
        refine ⟨42559197981715252336985545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56745597308953669782647393 42559197981715252336985545)
        ·
          refine ⟨31919398486286439252739159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42559197981715252336985545 31919398486286439252739159)
          ·
            refine ⟨47879097729429658879108739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31919398486286439252739159 47879097729429658879108739)
            ·
              refine ⟨71818646594144488318663109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47879097729429658879108739 71818646594144488318663109)
              ·
                refine ⟨13465996236402091559749333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71818646594144488318663109 13465996236402091559749333)
                ·
                  refine ⟨315609286790674020931625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13465996236402091559749333 315609286790674020931625)
                  ·
                    rfl

theorem cell22_2765911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_2765911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765911 prefixEnd_2765911 := by exact prefixLift 2765911
  have htrace : WordTrace (prefixWord ++ tailWord_2765911) baseStart_2765911 baseEnd_2765911 := by
    simpa [prefixWord, tailWord_2765911, baseEnd_2765911] using wordTrace_append hprefix tailTrace_2765911
  have hstable : (prefixWord ++ tailWord_2765911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765911).length < 2 ^ (prefixWord ++ tailWord_2765911).sum := by decide
  have hdescent : baseEnd_2765911 < baseStart_2765911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2765975 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 1, 4]
def baseStart_2765975 : Nat := 118140960795 + 2765975 * 2 ^ 59
def prefixEnd_2765975 : Nat := 4983230072969 + 3 ^ 40 * 2765975 * 2
def baseEnd_2765975 : Nat := 946849768879947229194679

theorem tailTrace_2765975 : CollatzResearch.WordTrace tailWord_2765975 prefixEnd_2765975 946849768879947229194679 := by
  unfold tailWord_2765975
  simp only [CollatzResearch.WordTrace]
  refine ⟨100883396154352440766147379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67255597436234960510764919 100883396154352440766147379)
  ·
    refine ⟨151325094231528661149221069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100883396154352440766147379 151325094231528661149221069)
    ·
      refine ⟨56746910336823247930957901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151325094231528661149221069 56746910336823247930957901)
      ·
        refine ⟨21280091376308717974109213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56746910336823247930957901 21280091376308717974109213)
        ·
          refine ⟨7980034266115769240290955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21280091376308717974109213 7980034266115769240290955)
          ·
            refine ⟨11970051399173653860436433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980034266115769240290955 11970051399173653860436433)
            ·
              refine ⟨8977538549380240395327325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11970051399173653860436433 8977538549380240395327325)
              ·
                refine ⟨3366576956017590148247747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8977538549380240395327325 3366576956017590148247747)
                ·
                  refine ⟨5049865434026385222371621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3366576956017590148247747 5049865434026385222371621)
                  ·
                    refine ⟨946849768879947229194679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5049865434026385222371621 946849768879947229194679)
                    ·
                      rfl

theorem cell22_2765975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_2765975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2765975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2765975 prefixEnd_2765975 := by exact prefixLift 2765975
  have htrace : WordTrace (prefixWord ++ tailWord_2765975) baseStart_2765975 baseEnd_2765975 := by
    simpa [prefixWord, tailWord_2765975, baseEnd_2765975] using wordTrace_append hprefix tailTrace_2765975
  have hstable : (prefixWord ++ tailWord_2765975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2765975).length < 2 ^ (prefixWord ++ tailWord_2765975).sum := by decide
  have hdescent : baseEnd_2765975 < baseStart_2765975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2765975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766048 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_2766048 : Nat := 118140960795 + 2766048 * 2 ^ 59
def prefixEnd_2766048 : Nat := 4983230072969 + 3 ^ 40 * 2766048 * 2
def baseEnd_2766048 : Nat := 946874758271799372119455

theorem tailTrace_2766048 : CollatzResearch.WordTrace tailWord_2766048 prefixEnd_2766048 946874758271799372119455 := by
  unfold tailWord_2766048
  simp only [CollatzResearch.WordTrace]
  refine ⟨50443029341543987116777399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67257372455391982822369865 50443029341543987116777399)
  ·
    refine ⟨75664544012315980675166099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50443029341543987116777399 75664544012315980675166099)
    ·
      refine ⟨113496816018473971012749149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75664544012315980675166099 113496816018473971012749149)
      ·
        refine ⟨42561306006927739129780931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113496816018473971012749149 42561306006927739129780931)
        ·
          refine ⟨63841959010391608694671397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42561306006927739129780931 63841959010391608694671397)
          ·
            refine ⟨11970367314448426630250887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63841959010391608694671397 11970367314448426630250887)
            ·
              refine ⟨17955550971672639945376331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970367314448426630250887 17955550971672639945376331)
              ·
                refine ⟨26933326457508959918064497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17955550971672639945376331 26933326457508959918064497)
                ·
                  refine ⟨20199994843131719938548373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26933326457508959918064497 20199994843131719938548373)
                  ·
                    refine ⟨946874758271799372119455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20199994843131719938548373 946874758271799372119455)
                    ·
                      rfl

theorem cell22_2766048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_2766048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766048 prefixEnd_2766048 := by exact prefixLift 2766048
  have htrace : WordTrace (prefixWord ++ tailWord_2766048) baseStart_2766048 baseEnd_2766048 := by
    simpa [prefixWord, tailWord_2766048, baseEnd_2766048] using wordTrace_append hprefix tailTrace_2766048
  have hstable : (prefixWord ++ tailWord_2766048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766048).length < 2 ^ (prefixWord ++ tailWord_2766048).sum := by decide
  have hdescent : baseEnd_2766048 < baseStart_2766048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766084 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2766084 : Nat := 118140960795 + 2766084 * 2 ^ 59
def prefixEnd_2766084 : Nat := 4983230072969 + 3 ^ 40 * 2766084 * 2
def baseEnd_2766084 : Nat := 946887081807507278219345

theorem tailTrace_2766084 : CollatzResearch.WordTrace tailWord_2766084 prefixEnd_2766084 946887081807507278219345 := by
  unfold tailWord_2766084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50443685855478776190932653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67258247807305034921243537 50443685855478776190932653)
  ·
    refine ⟨18916382195804541071599745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50443685855478776190932653 18916382195804541071599745)
    ·
      refine ⟨14187286646853405803699809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18916382195804541071599745 14187286646853405803699809)
      ·
        refine ⟨10640464985140054352774857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14187286646853405803699809 10640464985140054352774857)
        ·
          refine ⟨7980348738855040764581143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10640464985140054352774857 7980348738855040764581143)
          ·
            refine ⟨11970523108282561146871715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980348738855040764581143 11970523108282561146871715)
            ·
              refine ⟨17955784662423841720307573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11970523108282561146871715 17955784662423841720307573)
              ·
                refine ⟨1683354812102235161278835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17955784662423841720307573 1683354812102235161278835)
                ·
                  refine ⟨2525032218153352741918253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683354812102235161278835 2525032218153352741918253)
                  ·
                    refine ⟨946887081807507278219345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525032218153352741918253 946887081807507278219345)
                    ·
                      rfl

theorem cell22_2766084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2766084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766084 prefixEnd_2766084 := by exact prefixLift 2766084
  have htrace : WordTrace (prefixWord ++ tailWord_2766084) baseStart_2766084 baseEnd_2766084 := by
    simpa [prefixWord, tailWord_2766084, baseEnd_2766084] using wordTrace_append hprefix tailTrace_2766084
  have hstable : (prefixWord ++ tailWord_2766084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766084).length < 2 ^ (prefixWord ++ tailWord_2766084).sum := by decide
  have hdescent : baseEnd_2766084 < baseStart_2766084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766114 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2766114 : Nat := 118140960795 + 2766114 * 2 ^ 59
def prefixEnd_2766114 : Nat := 4983230072969 + 3 ^ 40 * 2766114 * 2
def baseEnd_2766114 : Nat := 315632450473532399989751

theorem tailTrace_2766114 : CollatzResearch.WordTrace tailWord_2766114 prefixEnd_2766114 315632450473532399989751 := by
  unfold tailWord_2766114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222116475212216876364349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67258977267232578336971597 25222116475212216876364349)
  ·
    refine ⟨9458293678204581328636631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25222116475212216876364349 9458293678204581328636631)
    ·
      refine ⟨14187440517306871992954947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458293678204581328636631 14187440517306871992954947)
      ·
        refine ⟨21281160775960307989432421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187440517306871992954947 21281160775960307989432421)
        ·
          refine ⟨3990217645492557748018579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21281160775960307989432421 3990217645492557748018579)
          ·
            refine ⟨5985326468238836622027869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990217645492557748018579 5985326468238836622027869)
            ·
              refine ⟨2244497425589563733260451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5985326468238836622027869 2244497425589563733260451)
              ·
                refine ⟨3366746138384345599890677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244497425589563733260451 3366746138384345599890677)
                ·
                  refine ⟨315632450473532399989751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3366746138384345599890677 315632450473532399989751)
                  ·
                    rfl

theorem cell22_2766114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2766114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766114 prefixEnd_2766114 := by exact prefixLift 2766114
  have htrace : WordTrace (prefixWord ++ tailWord_2766114) baseStart_2766114 baseEnd_2766114 := by
    simpa [prefixWord, tailWord_2766114, baseEnd_2766114] using wordTrace_append hprefix tailTrace_2766114
  have hstable : (prefixWord ++ tailWord_2766114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766114).length < 2 ^ (prefixWord ++ tailWord_2766114).sum := by decide
  have hdescent : baseEnd_2766114 < baseStart_2766114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766123 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_2766123 : Nat := 118140960795 + 2766123 * 2 ^ 59
def prefixEnd_2766123 : Nat := 4983230072969 + 3 ^ 40 * 2766123 * 2
def baseEnd_2766123 : Nat := 946900432304524176494225

theorem tailTrace_2766123 : CollatzResearch.WordTrace tailWord_2766123 prefixEnd_2766123 946900432304524176494225 := by
  unfold tailWord_2766123
  simp only [CollatzResearch.WordTrace]
  refine ⟨100888794157816262042535023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67259196105210841361690015 100888794157816262042535023)
  ·
    refine ⟨151333191236724393063802535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100888794157816262042535023 151333191236724393063802535)
    ·
      refine ⟨226999786855086589595703803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151333191236724393063802535 226999786855086589595703803)
      ·
        refine ⟨340499680282629884393555705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226999786855086589595703803 340499680282629884393555705)
        ·
          refine ⟨255374760211972413295166779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340499680282629884393555705 255374760211972413295166779)
          ·
            refine ⟨383062140317958619942750169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255374760211972413295166779 383062140317958619942750169)
            ·
              refine ⟨287296605238468964957062627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383062140317958619942750169 287296605238468964957062627)
              ·
                refine ⟨430944907857703447435593941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287296605238468964957062627 430944907857703447435593941)
                ·
                  refine ⟨10100271277914924549271733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 430944907857703447435593941 10100271277914924549271733)
                  ·
                    refine ⟨946900432304524176494225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10100271277914924549271733 946900432304524176494225)
                    ·
                      rfl

theorem cell22_2766123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_2766123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766123 prefixEnd_2766123 := by exact prefixLift 2766123
  have htrace : WordTrace (prefixWord ++ tailWord_2766123) baseStart_2766123 baseEnd_2766123 := by
    simpa [prefixWord, tailWord_2766123, baseEnd_2766123] using wordTrace_append hprefix tailTrace_2766123
  have hstable : (prefixWord ++ tailWord_2766123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766123).length < 2 ^ (prefixWord ++ tailWord_2766123).sum := by decide
  have hdescent : baseEnd_2766123 < baseStart_2766123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766153 : List Nat := [1, 2, 1, 1, 2, 3, 12]
def baseStart_2766153 : Nat := 118140960795 + 2766153 * 2 ^ 59
def prefixEnd_2766153 : Nat := 4983230072969 + 3 ^ 40 * 2766153 * 2
def baseEnd_2766153 : Nat := 35070766737689411046079

theorem tailTrace_2766153 : CollatzResearch.WordTrace tailWord_2766153 prefixEnd_2766153 35070766737689411046079 := by
  unfold tailWord_2766153
  simp only [CollatzResearch.WordTrace]
  refine ⟨100889888347707577166127113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67259925565138384777418075 100889888347707577166127113)
  ·
    refine ⟨75667416260780682874595335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100889888347707577166127113 75667416260780682874595335)
    ·
      refine ⟨113501124391171024311893003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75667416260780682874595335 113501124391171024311893003)
      ·
        refine ⟨170251686586756536467839505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113501124391171024311893003 170251686586756536467839505)
        ·
          refine ⟨127688764940067402350879629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170251686586756536467839505 127688764940067402350879629)
          ·
            refine ⟨47883286852525275881579861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127688764940067402350879629 47883286852525275881579861)
            ·
              refine ⟨35070766737689411046079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47883286852525275881579861 35070766737689411046079)
              ·
                rfl

theorem cell22_2766153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 12].length) (baseStart_2766153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766153 prefixEnd_2766153 := by exact prefixLift 2766153
  have htrace : WordTrace (prefixWord ++ tailWord_2766153) baseStart_2766153 baseEnd_2766153 := by
    simpa [prefixWord, tailWord_2766153, baseEnd_2766153] using wordTrace_append hprefix tailTrace_2766153
  have hstable : (prefixWord ++ tailWord_2766153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766153).length < 2 ^ (prefixWord ++ tailWord_2766153).sum := by decide
  have hdescent : baseEnd_2766153 < baseStart_2766153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
