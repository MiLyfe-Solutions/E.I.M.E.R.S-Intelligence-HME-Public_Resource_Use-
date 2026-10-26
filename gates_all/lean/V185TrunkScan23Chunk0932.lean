import V185TrunkScan23Chunk0931

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5515804 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5515804 : Nat := 118140960795 + 5515804 * 2 ^ 59
def prefixEnd_5515804 : Nat := 4983230072969 + 3 ^ 40 * 5515804 * 2
def baseEnd_5515804 : Nat := 2832258647992242625183285

theorem tailTrace_5515804 : CollatzResearch.WordTrace tailWord_5515804 prefixEnd_5515804 2832258647992242625183285 := by
  unfold tailWord_5515804
  simp only [CollatzResearch.WordTrace]
  refine ⟨100588949654595803584961233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134118599539461071446614977 100588949654595803584961233)
  ·
    refine ⟨75441712240946852688720925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100588949654595803584961233 75441712240946852688720925)
    ·
      refine ⟨28290642090355069758270347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75441712240946852688720925 28290642090355069758270347)
      ·
        refine ⟨42435963135532604637405521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28290642090355069758270347 42435963135532604637405521)
        ·
          refine ⟨31826972351649453478054141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42435963135532604637405521 31826972351649453478054141)
          ·
            refine ⟨11935114631868545054270303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31826972351649453478054141 11935114631868545054270303)
            ·
              refine ⟨17902671947802817581405455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11935114631868545054270303 17902671947802817581405455)
              ·
                refine ⟨26854007921704226372108183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17902671947802817581405455 26854007921704226372108183)
                ·
                  refine ⟨40281011882556339558162275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26854007921704226372108183 40281011882556339558162275)
                  ·
                    refine ⟨60421517823834509337243413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40281011882556339558162275 60421517823834509337243413)
                    ·
                      refine ⟨2832258647992242625183285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60421517823834509337243413 2832258647992242625183285)
                      ·
                        rfl

theorem cell23_5515804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5515804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515804 prefixEnd_5515804 := by exact prefixLift 5515804
  have htrace : WordTrace (prefixWord ++ tailWord_5515804) baseStart_5515804 baseEnd_5515804 := by
    simpa [prefixWord, tailWord_5515804, baseEnd_5515804] using wordTrace_append hprefix tailTrace_5515804
  have hstable : (prefixWord ++ tailWord_5515804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515804).length < 2 ^ (prefixWord ++ tailWord_5515804).sum := by decide
  have hdescent : baseEnd_5515804 < baseStart_5515804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515808 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5515808 : Nat := 118140960795 + 5515808 * 2 ^ 59
def prefixEnd_5515808 : Nat := 4983230072969 + 3 ^ 40 * 5515808 * 2
def baseEnd_5515808 : Nat := 2832260701914860609533267

theorem tailTrace_5515808 : CollatzResearch.WordTrace tailWord_5515808 prefixEnd_5515808 2832260701914860609533267 := by
  unfold tailWord_5515808
  simp only [CollatzResearch.WordTrace]
  refine ⟨100589022600588557926534039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134118696800784743902045385 100589022600588557926534039)
  ·
    refine ⟨150883533900882836889801059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100589022600588557926534039 150883533900882836889801059)
    ·
      refine ⟨226325300851324255334701589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150883533900882836889801059 226325300851324255334701589)
      ·
        refine ⟨10608998477405824468814137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 226325300851324255334701589 10608998477405824468814137)
        ·
          refine ⟨7956748858054368351610603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10608998477405824468814137 7956748858054368351610603)
          ·
            refine ⟨11935123287081552527415905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7956748858054368351610603 11935123287081552527415905)
            ·
              refine ⟨8951342465311164395561929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11935123287081552527415905 8951342465311164395561929)
              ·
                refine ⟨6713506848983373296671447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8951342465311164395561929 6713506848983373296671447)
                ·
                  refine ⟨10070260273475059945007171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713506848983373296671447 10070260273475059945007171)
                  ·
                    refine ⟨15105390410212589917510757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10070260273475059945007171 15105390410212589917510757)
                    ·
                      refine ⟨2832260701914860609533267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15105390410212589917510757 2832260701914860609533267)
                      ·
                        rfl

theorem cell23_5515808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5515808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515808 prefixEnd_5515808 := by exact prefixLift 5515808
  have htrace : WordTrace (prefixWord ++ tailWord_5515808) baseStart_5515808 baseEnd_5515808 := by
    simpa [prefixWord, tailWord_5515808, baseEnd_5515808] using wordTrace_append hprefix tailTrace_5515808
  have hstable : (prefixWord ++ tailWord_5515808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515808).length < 2 ^ (prefixWord ++ tailWord_5515808).sum := by decide
  have hdescent : baseEnd_5515808 < baseStart_5515808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515811 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 3]
def baseStart_5515811 : Nat := 118140960795 + 5515811 * 2 ^ 59
def prefixEnd_5515811 : Nat := 4983230072969 + 3 ^ 40 * 5515811 * 2
def baseEnd_5515811 : Nat := 2832262242356824097795753

theorem tailTrace_5515811 : CollatzResearch.WordTrace tailWord_5515811 prefixEnd_5515811 2832262242356824097795753 := by
  unfold tailWord_5515811
  simp only [CollatzResearch.WordTrace]
  refine ⟨201178154620166247365427287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134118769746777498243618191 201178154620166247365427287)
  ·
    refine ⟨301767231930249371048140931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201178154620166247365427287 301767231930249371048140931)
    ·
      refine ⟨452650847895374056572211397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301767231930249371048140931 452650847895374056572211397)
      ·
        refine ⟨84872033980382635607289637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 452650847895374056572211397 84872033980382635607289637)
        ·
          refine ⟨15913506371321744176366807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84872033980382635607289637 15913506371321744176366807)
          ·
            refine ⟨23870259556982616264550211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15913506371321744176366807 23870259556982616264550211)
            ·
              refine ⟨35805389335473924396825317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23870259556982616264550211 35805389335473924396825317)
              ·
                refine ⟨6713510500401360824404747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35805389335473924396825317 6713510500401360824404747)
                ·
                  refine ⟨10070265750602041236607121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713510500401360824404747 10070265750602041236607121)
                  ·
                    refine ⟨7552699312951530927455341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10070265750602041236607121 7552699312951530927455341)
                    ·
                      refine ⟨2832262242356824097795753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552699312951530927455341 2832262242356824097795753)
                      ·
                        rfl

theorem cell23_5515811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_5515811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515811 prefixEnd_5515811 := by exact prefixLift 5515811
  have htrace : WordTrace (prefixWord ++ tailWord_5515811) baseStart_5515811 baseEnd_5515811 := by
    simpa [prefixWord, tailWord_5515811, baseEnd_5515811] using wordTrace_append hprefix tailTrace_5515811
  have hstable : (prefixWord ++ tailWord_5515811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515811).length < 2 ^ (prefixWord ++ tailWord_5515811).sum := by decide
  have hdescent : baseEnd_5515811 < baseStart_5515811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515824 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_5515824 : Nat := 118140960795 + 5515824 * 2 ^ 59
def prefixEnd_5515824 : Nat := 4983230072969 + 3 ^ 40 * 5515824 * 2
def baseEnd_5515824 : Nat := 2832268917605332546933193

theorem tailTrace_5515824 : CollatzResearch.WordTrace tailWord_5515824 prefixEnd_5515824 2832268917605332546933193 := by
  unfold tailWord_5515824
  simp only [CollatzResearch.WordTrace]
  refine ⟨100589314384559575292825263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134119085846079433723767017 100589314384559575292825263)
  ·
    refine ⟨150883971576839362939237895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100589314384559575292825263 150883971576839362939237895)
    ·
      refine ⟨226325957365259044408856843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150883971576839362939237895 226325957365259044408856843)
      ·
        refine ⟨339488936047888566613285265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226325957365259044408856843 339488936047888566613285265)
        ·
          refine ⟨254616702035916424959963949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339488936047888566613285265 254616702035916424959963949)
          ·
            refine ⟨95481263263468659359986481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254616702035916424959963949 95481263263468659359986481)
            ·
              refine ⟨71610947447601494519989861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95481263263468659359986481 71610947447601494519989861)
              ·
                refine ⟨13427052646425280222498099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71610947447601494519989861 13427052646425280222498099)
                ·
                  refine ⟨20140578969637920333747149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427052646425280222498099 20140578969637920333747149)
                  ·
                    refine ⟨7552717113614220125155181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20140578969637920333747149 7552717113614220125155181)
                    ·
                      refine ⟨2832268917605332546933193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552717113614220125155181 2832268917605332546933193)
                      ·
                        rfl

theorem cell23_5515824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_5515824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515824 prefixEnd_5515824 := by exact prefixLift 5515824
  have htrace : WordTrace (prefixWord ++ tailWord_5515824) baseStart_5515824 baseEnd_5515824 := by
    simpa [prefixWord, tailWord_5515824, baseEnd_5515824] using wordTrace_append hprefix tailTrace_5515824
  have hstable : (prefixWord ++ tailWord_5515824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515824).length < 2 ^ (prefixWord ++ tailWord_5515824).sum := by decide
  have hdescent : baseEnd_5515824 < baseStart_5515824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515825 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_5515825 : Nat := 118140960795 + 5515825 * 2 ^ 59
def prefixEnd_5515825 : Nat := 4983230072969 + 3 ^ 40 * 5515825 * 2
def baseEnd_5515825 : Nat := 2832269431085987043020689

theorem tailTrace_5515825 : CollatzResearch.WordTrace tailWord_5515825 prefixEnd_5515825 2832269431085987043020689 := by
  unfold tailWord_5515825
  simp only [CollatzResearch.WordTrace]
  refine ⟨201178665242115527756436929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134119110161410351837624619 201178665242115527756436929)
  ·
    refine ⟨150883998931586645817327697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201178665242115527756436929 150883998931586645817327697)
    ·
      refine ⟨113162999198689984362995773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150883998931586645817327697 113162999198689984362995773)
      ·
        refine ⟨42436124699508744136123415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113162999198689984362995773 42436124699508744136123415)
        ·
          refine ⟨63654187049263116204185123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42436124699508744136123415 63654187049263116204185123)
          ·
            refine ⟨95481280573894674306277685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63654187049263116204185123 95481280573894674306277685)
            ·
              refine ⟨8951370053802625716213533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95481280573894674306277685 8951370053802625716213533)
              ·
                refine ⟨3356763770175984643580075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8951370053802625716213533 3356763770175984643580075)
                ·
                  refine ⟨5035145655263976965370113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356763770175984643580075 5035145655263976965370113)
                  ·
                    refine ⟨3776359241447982724027585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035145655263976965370113 3776359241447982724027585)
                    ·
                      refine ⟨2832269431085987043020689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776359241447982724027585 2832269431085987043020689)
                      ·
                        rfl

theorem cell23_5515825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_5515825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515825 prefixEnd_5515825 := by exact prefixLift 5515825
  have htrace : WordTrace (prefixWord ++ tailWord_5515825) baseStart_5515825 baseEnd_5515825 := by
    simpa [prefixWord, tailWord_5515825, baseEnd_5515825] using wordTrace_append hprefix tailTrace_5515825
  have hstable : (prefixWord ++ tailWord_5515825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515825).length < 2 ^ (prefixWord ++ tailWord_5515825).sum := by decide
  have hdescent : baseEnd_5515825 < baseStart_5515825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515858 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_5515858 : Nat := 118140960795 + 5515858 * 2 ^ 59
def prefixEnd_5515858 : Nat := 4983230072969 + 3 ^ 40 * 5515858 * 2
def baseEnd_5515858 : Nat := 2832286375947585413908037

theorem tailTrace_5515858 : CollatzResearch.WordTrace tailWord_5515858 prefixEnd_5515858 2832286375947585413908037 := by
  unfold tailWord_5515858
  simp only [CollatzResearch.WordTrace]
  refine ⟨50294967212748993598097057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134119912567330649594925485 50294967212748993598097057)
  ·
    refine ⟨37721225409561745198572793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50294967212748993598097057 37721225409561745198572793)
    ·
      refine ⟨28290919057171308898929595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37721225409561745198572793 28290919057171308898929595)
      ·
        refine ⟨42436378585756963348394393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28290919057171308898929595 42436378585756963348394393)
        ·
          refine ⟨31827283939317722511295795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42436378585756963348394393 31827283939317722511295795)
          ·
            refine ⟨47740925908976583766943693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31827283939317722511295795 47740925908976583766943693)
            ·
              refine ⟨17902847215866218912603885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47740925908976583766943693 17902847215866218912603885)
              ·
                refine ⟨6713567705949832092226457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17902847215866218912603885 6713567705949832092226457)
                ·
                  refine ⟨5035175779462374069169843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6713567705949832092226457 5035175779462374069169843)
                  ·
                    refine ⟨7552763669193561103754765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035175779462374069169843 7552763669193561103754765)
                    ·
                      refine ⟨2832286375947585413908037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552763669193561103754765 2832286375947585413908037)
                      ·
                        rfl

theorem cell23_5515858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_5515858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515858 prefixEnd_5515858 := by exact prefixLift 5515858
  have htrace : WordTrace (prefixWord ++ tailWord_5515858) baseStart_5515858 baseEnd_5515858 := by
    simpa [prefixWord, tailWord_5515858, baseEnd_5515858] using wordTrace_append hprefix tailTrace_5515858
  have hstable : (prefixWord ++ tailWord_5515858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515858).length < 2 ^ (prefixWord ++ tailWord_5515858).sum := by decide
  have hdescent : baseEnd_5515858 < baseStart_5515858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515867 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_5515867 : Nat := 118140960795 + 5515867 * 2 ^ 59
def prefixEnd_5515867 : Nat := 4983230072969 + 3 ^ 40 * 5515867 * 2
def baseEnd_5515867 : Nat := 2832290997273475878695495

theorem tailTrace_5515867 : CollatzResearch.WordTrace tailWord_5515867 prefixEnd_5515867 2832290997273475878695495 := by
  unfold tailWord_5515867
  simp only [CollatzResearch.WordTrace]
  refine ⟨201180197107963368929465855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134120131405308912619643903 201180197107963368929465855)
  ·
    refine ⟨301770295661945053394198783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201180197107963368929465855 301770295661945053394198783)
    ·
      refine ⟨452655443492917580091298175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301770295661945053394198783 452655443492917580091298175)
      ·
        refine ⟨678983165239376370136947263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452655443492917580091298175 678983165239376370136947263)
        ·
          refine ⟨1018474747859064555205420895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678983165239376370136947263 1018474747859064555205420895)
          ·
            refine ⟨1527712121788596832808131343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018474747859064555205420895 1527712121788596832808131343)
            ·
              refine ⟨2291568182682895249212197015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527712121788596832808131343 2291568182682895249212197015)
              ·
                refine ⟨3437352274024342873818295523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291568182682895249212197015 3437352274024342873818295523)
                ·
                  refine ⟨5156028411036514310727443285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437352274024342873818295523 5156028411036514310727443285)
                  ·
                    refine ⟨30211103970917076039418613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5156028411036514310727443285 30211103970917076039418613)
                    ·
                      refine ⟨2832290997273475878695495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30211103970917076039418613 2832290997273475878695495)
                      ·
                        rfl

theorem cell23_5515867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_5515867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515867 prefixEnd_5515867 := by exact prefixLift 5515867
  have htrace : WordTrace (prefixWord ++ tailWord_5515867) baseStart_5515867 baseEnd_5515867 := by
    simpa [prefixWord, tailWord_5515867, baseEnd_5515867] using wordTrace_append hprefix tailTrace_5515867
  have hstable : (prefixWord ++ tailWord_5515867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515867).length < 2 ^ (prefixWord ++ tailWord_5515867).sum := by decide
  have hdescent : baseEnd_5515867 < baseStart_5515867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515884 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_5515884 : Nat := 118140960795 + 5515884 * 2 ^ 59
def prefixEnd_5515884 : Nat := 4983230072969 + 3 ^ 40 * 5515884 * 2
def baseEnd_5515884 : Nat := 2832299726444602312182917

theorem tailTrace_5515884 : CollatzResearch.WordTrace tailWord_5515884 prefixEnd_5515884 2832299726444602312182917 := by
  unfold tailWord_5515884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100590408574450890416417353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134120544765934520555223137 100590408574450890416417353)
  ·
    refine ⟨75442806430838167812313015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100590408574450890416417353 75442806430838167812313015)
    ·
      refine ⟨113164209646257251718469523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75442806430838167812313015 113164209646257251718469523)
      ·
        refine ⟨169746314469385877577704285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113164209646257251718469523 169746314469385877577704285)
        ·
          refine ⟨63654867926019704091639107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169746314469385877577704285 63654867926019704091639107)
          ·
            refine ⟨95482301889029556137458661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63654867926019704091639107 95482301889029556137458661)
            ·
              refine ⟨17902931604193041775773499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95482301889029556137458661 17902931604193041775773499)
              ·
                refine ⟨26854397406289562663660249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17902931604193041775773499 26854397406289562663660249)
                ·
                  refine ⟨20140798054717171997745187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26854397406289562663660249 20140798054717171997745187)
                  ·
                    refine ⟨30211197082075757996617781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20140798054717171997745187 30211197082075757996617781)
                    ·
                      refine ⟨2832299726444602312182917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30211197082075757996617781 2832299726444602312182917)
                      ·
                        rfl

theorem cell23_5515884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_5515884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515884 prefixEnd_5515884 := by exact prefixLift 5515884
  have htrace : WordTrace (prefixWord ++ tailWord_5515884) baseStart_5515884 baseEnd_5515884 := by
    simpa [prefixWord, tailWord_5515884, baseEnd_5515884] using wordTrace_append hprefix tailTrace_5515884
  have hstable : (prefixWord ++ tailWord_5515884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515884).length < 2 ^ (prefixWord ++ tailWord_5515884).sum := by decide
  have hdescent : baseEnd_5515884 < baseStart_5515884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515991 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_5515991 : Nat := 118140960795 + 5515991 * 2 ^ 59
def prefixEnd_5515991 : Nat := 4983230072969 + 3 ^ 40 * 5515991 * 2
def baseEnd_5515991 : Nat := 2832354668874633393544925

theorem tailTrace_5515991 : CollatzResearch.WordTrace tailWord_5515991 prefixEnd_5515991 2832354668874633393544925 := by
  unfold tailWord_5515991
  simp only [CollatzResearch.WordTrace]
  refine ⟨201184719759514138106979827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134123146506342758737986551 201184719759514138106979827)
  ·
    refine ⟨301777079639271207160469741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201184719759514138106979827 301777079639271207160469741)
    ·
      refine ⟨113166404864726702685176153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301777079639271207160469741 113166404864726702685176153)
      ·
        refine ⟨84874803648545027013882115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113166404864726702685176153 84874803648545027013882115)
        ·
          refine ⟨127312205472817540520823173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84874803648545027013882115 127312205472817540520823173)
          ·
            refine ⟨23871038526153288847654345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127312205472817540520823173 23871038526153288847654345)
            ·
              refine ⟨17903278894614966635740759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23871038526153288847654345 17903278894614966635740759)
              ·
                refine ⟨26854918341922449953611139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17903278894614966635740759 26854918341922449953611139)
                ·
                  refine ⟨40282377512883674930416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26854918341922449953611139 40282377512883674930416709)
                  ·
                    refine ⟨7552945783665689049453133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40282377512883674930416709 7552945783665689049453133)
                    ·
                      refine ⟨2832354668874633393544925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7552945783665689049453133 2832354668874633393544925)
                      ·
                        rfl

theorem cell23_5515991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_5515991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515991 prefixEnd_5515991 := by exact prefixLift 5515991
  have htrace : WordTrace (prefixWord ++ tailWord_5515991) baseStart_5515991 baseEnd_5515991 := by
    simpa [prefixWord, tailWord_5515991, baseEnd_5515991] using wordTrace_append hprefix tailTrace_5515991
  have hstable : (prefixWord ++ tailWord_5515991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515991).length < 2 ^ (prefixWord ++ tailWord_5515991).sum := by decide
  have hdescent : baseEnd_5515991 < baseStart_5515991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5515994 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_5515994 : Nat := 118140960795 + 5515994 * 2 ^ 59
def prefixEnd_5515994 : Nat := 4983230072969 + 3 ^ 40 * 5515994 * 2
def baseEnd_5515994 : Nat := 314706245479621875756379

theorem tailTrace_5515994 : CollatzResearch.WordTrace tailWord_5515994 prefixEnd_5515994 314706245479621875756379 := by
  unfold tailWord_5515994
  simp only [CollatzResearch.WordTrace]
  refine ⟨50296207294625817404834759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134123219452335513079559357 50296207294625817404834759)
  ·
    refine ⟨75444310941938726107252139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50296207294625817404834759 75444310941938726107252139)
    ·
      refine ⟨113166466412908089160878209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75444310941938726107252139 113166466412908089160878209)
      ·
        refine ⟨84874849809681066870658657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113166466412908089160878209 84874849809681066870658657)
        ·
          refine ⟨63656137357260800152993993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84874849809681066870658657 63656137357260800152993993)
          ·
            refine ⟨47742103017945600114745495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63656137357260800152993993 47742103017945600114745495)
            ·
              refine ⟨71613154526918400172118243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47742103017945600114745495 71613154526918400172118243)
              ·
                refine ⟨107419731790377600258177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71613154526918400172118243 107419731790377600258177365)
                ·
                  refine ⟨314706245479621875756379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107419731790377600258177365 314706245479621875756379)
                  ·
                    rfl

theorem cell23_5515994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_5515994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5515994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5515994 prefixEnd_5515994 := by exact prefixLift 5515994
  have htrace : WordTrace (prefixWord ++ tailWord_5515994) baseStart_5515994 baseEnd_5515994 := by
    simpa [prefixWord, tailWord_5515994, baseEnd_5515994] using wordTrace_append hprefix tailTrace_5515994
  have hstable : (prefixWord ++ tailWord_5515994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5515994).length < 2 ^ (prefixWord ++ tailWord_5515994).sum := by decide
  have hdescent : baseEnd_5515994 < baseStart_5515994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5515994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516028 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 6]
def baseStart_5516028 : Nat := 118140960795 + 5516028 * 2 ^ 59
def prefixEnd_5516028 : Nat := 4983230072969 + 3 ^ 40 * 5516028 * 2
def baseEnd_5516028 : Nat := 314708185295427749864695

theorem tailTrace_5516028 : CollatzResearch.WordTrace tailWord_5516028 prefixEnd_5516028 314708185295427749864695 := by
  unfold tailWord_5516028
  simp only [CollatzResearch.WordTrace]
  refine ⟨100593034630190046713038369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134124046173586728950717825 100593034630190046713038369)
  ·
    refine ⟨75444775972642535034778777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100593034630190046713038369 75444775972642535034778777)
    ·
      refine ⟨56583581979481901276084083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75444775972642535034778777 56583581979481901276084083)
      ·
        refine ⟨84875372969222851914126125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56583581979481901276084083 84875372969222851914126125)
        ·
          refine ⟨31828264863458569467797297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84875372969222851914126125 31828264863458569467797297)
          ·
            refine ⟨23871198647593927100847973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31828264863458569467797297 23871198647593927100847973)
            ·
              refine ⟨4475849746423861331408995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23871198647593927100847973 4475849746423861331408995)
              ·
                refine ⟨6713774619635791997113493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475849746423861331408995 6713774619635791997113493)
                ·
                  refine ⟨314708185295427749864695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6713774619635791997113493 314708185295427749864695)
                  ·
                    rfl

theorem cell23_5516028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_5516028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516028 prefixEnd_5516028 := by exact prefixLift 5516028
  have htrace : WordTrace (prefixWord ++ tailWord_5516028) baseStart_5516028 baseEnd_5516028 := by
    simpa [prefixWord, tailWord_5516028, baseEnd_5516028] using wordTrace_append hprefix tailTrace_5516028
  have hstable : (prefixWord ++ tailWord_5516028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516028).length < 2 ^ (prefixWord ++ tailWord_5516028).sum := by decide
  have hdescent : baseEnd_5516028 < baseStart_5516028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516072 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5516072 : Nat := 118140960795 + 5516072 * 2 ^ 59
def prefixEnd_5516072 : Nat := 4983230072969 + 3 ^ 40 * 5516072 * 2
def baseEnd_5516072 : Nat := 2832396260807647576632053

theorem tailTrace_5516072 : CollatzResearch.WordTrace tailWord_5516072 prefixEnd_5516072 2832396260807647576632053 := by
  unfold tailWord_5516072
  simp only [CollatzResearch.WordTrace]
  refine ⟨100593837036110344470339235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134125116048147125960452313 100593837036110344470339235)
  ·
    refine ⟨150890755554165516705508853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100593837036110344470339235 150890755554165516705508853)
    ·
      refine ⟨14146008333203017191141455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150890755554165516705508853 14146008333203017191141455)
      ·
        refine ⟨21219012499804525786712183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14146008333203017191141455 21219012499804525786712183)
        ·
          refine ⟨31828518749706788680068275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21219012499804525786712183 31828518749706788680068275)
          ·
            refine ⟨47742778124560183020102413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31828518749706788680068275 47742778124560183020102413)
            ·
              refine ⟨17903541796710068632538405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47742778124560183020102413 17903541796710068632538405)
              ·
                refine ⟨3356914086883137868600951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17903541796710068632538405 3356914086883137868600951)
                ·
                  refine ⟨5035371130324706802901427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356914086883137868600951 5035371130324706802901427)
                  ·
                    refine ⟨7553056695487060204352141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035371130324706802901427 7553056695487060204352141)
                    ·
                      refine ⟨2832396260807647576632053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553056695487060204352141 2832396260807647576632053)
                      ·
                        rfl

theorem cell23_5516072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5516072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516072 prefixEnd_5516072 := by exact prefixLift 5516072
  have htrace : WordTrace (prefixWord ++ tailWord_5516072) baseStart_5516072 baseEnd_5516072 := by
    simpa [prefixWord, tailWord_5516072, baseEnd_5516072] using wordTrace_append hprefix tailTrace_5516072
  have hstable : (prefixWord ++ tailWord_5516072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516072).length < 2 ^ (prefixWord ++ tailWord_5516072).sum := by decide
  have hdescent : baseEnd_5516072 < baseStart_5516072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516081 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5516081 : Nat := 118140960795 + 5516081 * 2 ^ 59
def prefixEnd_5516081 : Nat := 4983230072969 + 3 ^ 40 * 5516081 * 2
def baseEnd_5516081 : Nat := 2832400882133538041419511

theorem tailTrace_5516081 : CollatzResearch.WordTrace tailWord_5516081 prefixEnd_5516081 2832400882133538041419511 := by
  unfold tailWord_5516081
  simp only [CollatzResearch.WordTrace]
  refine ⟨201188002329188083477756097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134125334886125388985170731 201188002329188083477756097)
  ·
    refine ⟨150891001746891062608317073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201188002329188083477756097 150891001746891062608317073)
    ·
      refine ⟨113168251310168296956237805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150891001746891062608317073 113168251310168296956237805)
      ·
        refine ⟨42438094241313111358589177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113168251310168296956237805 42438094241313111358589177)
        ·
          refine ⟨31828570680984833518941883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42438094241313111358589177 31828570680984833518941883)
          ·
            refine ⟨47742856021477250278412825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31828570680984833518941883 47742856021477250278412825)
            ·
              refine ⟨35807142016107937708809619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47742856021477250278412825 35807142016107937708809619)
              ·
                refine ⟨53710713024161906563214429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35807142016107937708809619 53710713024161906563214429)
                ·
                  refine ⟨20141517384060714961205411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53710713024161906563214429 20141517384060714961205411)
                  ·
                    refine ⟨30212276076091072441808117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20141517384060714961205411 30212276076091072441808117)
                    ·
                      refine ⟨2832400882133538041419511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30212276076091072441808117 2832400882133538041419511)
                      ·
                        rfl

theorem cell23_5516081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5516081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516081 prefixEnd_5516081 := by exact prefixLift 5516081
  have htrace : WordTrace (prefixWord ++ tailWord_5516081) baseStart_5516081 baseEnd_5516081 := by
    simpa [prefixWord, tailWord_5516081, baseEnd_5516081] using wordTrace_append hprefix tailTrace_5516081
  have hstable : (prefixWord ++ tailWord_5516081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516081).length < 2 ^ (prefixWord ++ tailWord_5516081).sum := by decide
  have hdescent : baseEnd_5516081 < baseStart_5516081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516088 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_5516088 : Nat := 118140960795 + 5516088 * 2 ^ 59
def prefixEnd_5516088 : Nat := 4983230072969 + 3 ^ 40 * 5516088 * 2
def baseEnd_5516088 : Nat := 944134825499373171343993

theorem tailTrace_5516088 : CollatzResearch.WordTrace tailWord_5516088 prefixEnd_5516088 944134825499373171343993 := by
  unfold tailWord_5516088
  simp only [CollatzResearch.WordTrace]
  refine ⟨100594128820081361836630459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134125505093441815782173945 100594128820081361836630459)
  ·
    refine ⟨150891193230122042754945689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100594128820081361836630459 150891193230122042754945689)
    ·
      refine ⟨113168394922591532066209267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150891193230122042754945689 113168394922591532066209267)
      ·
        refine ⟨169752592383887298099313901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113168394922591532066209267 169752592383887298099313901)
        ·
          refine ⟨63657222143957736787242713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169752592383887298099313901 63657222143957736787242713)
          ·
            refine ⟨47742916607968302590432035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63657222143957736787242713 47742916607968302590432035)
            ·
              refine ⟨71614374911952453885648053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47742916607968302590432035 71614374911952453885648053)
              ·
                refine ⟨6713847647995542551779505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71614374911952453885648053 6713847647995542551779505)
                ·
                  refine ⟨5035385735996656913834629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6713847647995542551779505 5035385735996656913834629)
                  ·
                    refine ⟨944134825499373171343993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035385735996656913834629 944134825499373171343993)
                    ·
                      rfl

theorem cell23_5516088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_5516088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516088 prefixEnd_5516088 := by exact prefixLift 5516088
  have htrace : WordTrace (prefixWord ++ tailWord_5516088) baseStart_5516088 baseEnd_5516088 := by
    simpa [prefixWord, tailWord_5516088, baseEnd_5516088] using wordTrace_append hprefix tailTrace_5516088
  have hstable : (prefixWord ++ tailWord_5516088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516088).length < 2 ^ (prefixWord ++ tailWord_5516088).sum := by decide
  have hdescent : baseEnd_5516088 < baseStart_5516088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516095 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 5, 2, 2]
def baseStart_5516095 : Nat := 118140960795 + 5516095 * 2 ^ 59
def prefixEnd_5516095 : Nat := 4983230072969 + 3 ^ 40 * 5516095 * 2
def baseEnd_5516095 : Nat := 2832408070862700986644447

theorem tailTrace_5516095 : CollatzResearch.WordTrace tailWord_5516095 prefixEnd_5516095 2832408070862700986644447 := by
  unfold tailWord_5516095
  simp only [CollatzResearch.WordTrace]
  refine ⟨201188512951137363868765739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134125675300758242579177159 201188512951137363868765739)
  ·
    refine ⟨301782769426706045803148609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201188512951137363868765739 301782769426706045803148609)
    ·
      refine ⟨226337077070029534352361457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301782769426706045803148609 226337077070029534352361457)
      ·
        refine ⟨169752807802522150764271093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226337077070029534352361457 169752807802522150764271093)
        ·
          refine ⟨15914325731486451634150415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169752807802522150764271093 15914325731486451634150415)
          ·
            refine ⟨23871488597229677451225623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15914325731486451634150415 23871488597229677451225623)
            ·
              refine ⟨35807232895844516176838435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23871488597229677451225623 35807232895844516176838435)
              ·
                refine ⟨53710849343766774265257653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35807232895844516176838435 53710849343766774265257653)
                ·
                  refine ⟨5035392125978135087367905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53710849343766774265257653 5035392125978135087367905)
                  ·
                    refine ⟨3776544094483601315525929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035392125978135087367905 3776544094483601315525929)
                    ·
                      refine ⟨2832408070862700986644447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776544094483601315525929 2832408070862700986644447)
                      ·
                        rfl

theorem cell23_5516095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_5516095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516095 prefixEnd_5516095 := by exact prefixLift 5516095
  have htrace : WordTrace (prefixWord ++ tailWord_5516095) baseStart_5516095 baseEnd_5516095 := by
    simpa [prefixWord, tailWord_5516095, baseEnd_5516095] using wordTrace_append hprefix tailTrace_5516095
  have hstable : (prefixWord ++ tailWord_5516095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516095).length < 2 ^ (prefixWord ++ tailWord_5516095).sum := by decide
  have hdescent : baseEnd_5516095 < baseStart_5516095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516108 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5516108 : Nat := 118140960795 + 5516108 * 2 ^ 59
def prefixEnd_5516108 : Nat := 4983230072969 + 3 ^ 40 * 5516108 * 2
def baseEnd_5516108 : Nat := 2832414746111209435781887

theorem tailTrace_5516108 : CollatzResearch.WordTrace tailWord_5516108 prefixEnd_5516108 2832414746111209435781887 := by
  unfold tailWord_5516108
  simp only [CollatzResearch.WordTrace]
  refine ⟨100594493550045133544494489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134125991400060178059325985 100594493550045133544494489)
  ·
    refine ⟨75445870162533850158370867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100594493550045133544494489 75445870162533850158370867)
    ·
      refine ⟨113168805243800775237556301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75445870162533850158370867 113168805243800775237556301)
      ·
        refine ⟨42438301966425290714083613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113168805243800775237556301 42438301966425290714083613)
        ·
          refine ⟨15914363237409484017781355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42438301966425290714083613 15914363237409484017781355)
          ·
            refine ⟨23871544856114226026672033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15914363237409484017781355 23871544856114226026672033)
            ·
              refine ⟨17903658642085669520004025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23871544856114226026672033 17903658642085669520004025)
              ·
                refine ⟨13427743981564252140003019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17903658642085669520004025 13427743981564252140003019)
                ·
                  refine ⟨20141615972346378210004529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427743981564252140003019 20141615972346378210004529)
                  ·
                    refine ⟨15106211979259783657503397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20141615972346378210004529 15106211979259783657503397)
                    ·
                      refine ⟨2832414746111209435781887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15106211979259783657503397 2832414746111209435781887)
                      ·
                        rfl

theorem cell23_5516108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5516108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516108 prefixEnd_5516108 := by exact prefixLift 5516108
  have htrace : WordTrace (prefixWord ++ tailWord_5516108) baseStart_5516108 baseEnd_5516108 := by
    simpa [prefixWord, tailWord_5516108, baseEnd_5516108] using wordTrace_append hprefix tailTrace_5516108
  have hstable : (prefixWord ++ tailWord_5516108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516108).length < 2 ^ (prefixWord ++ tailWord_5516108).sum := by decide
  have hdescent : baseEnd_5516108 < baseStart_5516108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516109 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5516109 : Nat := 118140960795 + 5516109 * 2 ^ 59
def prefixEnd_5516109 : Nat := 4983230072969 + 3 ^ 40 * 5516109 * 2
def baseEnd_5516109 : Nat := 944138419863954643956461

theorem tailTrace_5516109 : CollatzResearch.WordTrace tailWord_5516109 prefixEnd_5516109 944138419863954643956461 := by
  unfold tailWord_5516109
  simp only [CollatzResearch.WordTrace]
  refine ⟨201189023573086644259775381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134126015715391096173183587 201189023573086644259775381)
  ·
    refine ⟨9430735479988436449676971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 201189023573086644259775381 9430735479988436449676971)
    ·
      refine ⟨14146103219982654674515457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430735479988436449676971 14146103219982654674515457)
      ·
        refine ⟨10609577414986991005886593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14146103219982654674515457 10609577414986991005886593)
        ·
          refine ⟨7957183061240243254414945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10609577414986991005886593 7957183061240243254414945)
          ·
            refine ⟨5967887295930182440811209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957183061240243254414945 5967887295930182440811209)
            ·
              refine ⟨4475915471947636830608407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967887295930182440811209 4475915471947636830608407)
              ·
                refine ⟨6713873207921455245912611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475915471947636830608407 6713873207921455245912611)
                ·
                  refine ⟨10070809811882182868868917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713873207921455245912611 10070809811882182868868917)
                  ·
                    refine ⟨944138419863954643956461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10070809811882182868868917 944138419863954643956461)
                    ·
                      rfl

theorem cell23_5516109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5516109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516109 prefixEnd_5516109 := by exact prefixLift 5516109
  have htrace : WordTrace (prefixWord ++ tailWord_5516109) baseStart_5516109 baseEnd_5516109 := by
    simpa [prefixWord, tailWord_5516109, baseEnd_5516109] using wordTrace_append hprefix tailTrace_5516109
  have hstable : (prefixWord ++ tailWord_5516109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516109).length < 2 ^ (prefixWord ++ tailWord_5516109).sum := by decide
  have hdescent : baseEnd_5516109 < baseStart_5516109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516112 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 1, 2, 2]
def baseStart_5516112 : Nat := 118140960795 + 5516112 * 2 ^ 59
def prefixEnd_5516112 : Nat := 4983230072969 + 3 ^ 40 * 5516112 * 2
def baseEnd_5516112 : Nat := 2832416800033827420131869

theorem tailTrace_5516112 : CollatzResearch.WordTrace tailWord_5516112 prefixEnd_5516112 2832416800033827420131869 := by
  unfold tailWord_5516112
  simp only [CollatzResearch.WordTrace]
  refine ⟨100594566496037887886067295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134126088661383850514756393 100594566496037887886067295)
  ·
    refine ⟨150891849744056831829100943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100594566496037887886067295 150891849744056831829100943)
    ·
      refine ⟨226337774616085247743651415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150891849744056831829100943 226337774616085247743651415)
      ·
        refine ⟨339506661924127871615477123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226337774616085247743651415 339506661924127871615477123)
        ·
          refine ⟨509259992886191807423215685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339506661924127871615477123 509259992886191807423215685)
          ·
            refine ⟨95486248666160963891852941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 509259992886191807423215685 95486248666160963891852941)
            ·
              refine ⟨35807343249810361459444853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95486248666160963891852941 35807343249810361459444853)
              ·
                refine ⟨3356938429669721386822955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35807343249810361459444853 3356938429669721386822955)
                ·
                  refine ⟨5035407644504582080234433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3356938429669721386822955 5035407644504582080234433)
                  ·
                    refine ⟨3776555733378436560175825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035407644504582080234433 3776555733378436560175825)
                    ·
                      refine ⟨2832416800033827420131869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776555733378436560175825 2832416800033827420131869)
                      ·
                        rfl

theorem cell23_5516112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 2, 2].length) (baseStart_5516112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516112 prefixEnd_5516112 := by exact prefixLift 5516112
  have htrace : WordTrace (prefixWord ++ tailWord_5516112) baseStart_5516112 baseEnd_5516112 := by
    simpa [prefixWord, tailWord_5516112, baseEnd_5516112] using wordTrace_append hprefix tailTrace_5516112
  have hstable : (prefixWord ++ tailWord_5516112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516112).length < 2 ^ (prefixWord ++ tailWord_5516112).sum := by decide
  have hdescent : baseEnd_5516112 < baseStart_5516112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516142 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5516142 : Nat := 118140960795 + 5516142 * 2 ^ 59
def prefixEnd_5516142 : Nat := 4983230072969 + 3 ^ 40 * 5516142 * 2
def baseEnd_5516142 : Nat := 2832432204453462302756731

theorem tailTrace_5516142 : CollatzResearch.WordTrace tailWord_5516142 prefixEnd_5516142 2832432204453462302756731 := by
  unfold tailWord_5516142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148778397745886361965835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134126818121311393930484453 25148778397745886361965835)
  ·
    refine ⟨37723167596618829542948753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148778397745886361965835 37723167596618829542948753)
    ·
      refine ⟨28292375697464122157211565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37723167596618829542948753 28292375697464122157211565)
      ·
        refine ⟨10609640886549045808954337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28292375697464122157211565 10609640886549045808954337)
        ·
          refine ⟨7957230664911784356715753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10609640886549045808954337 7957230664911784356715753)
          ·
            refine ⟨5967922998683838267536815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957230664911784356715753 5967922998683838267536815)
            ·
              refine ⟨8951884498025757401305223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967922998683838267536815 8951884498025757401305223)
              ·
                refine ⟨13427826747038636101957835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951884498025757401305223 13427826747038636101957835)
                ·
                  refine ⟨20141740120557954152936753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427826747038636101957835 20141740120557954152936753)
                  ·
                    refine ⟨15106305090418465614702565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20141740120557954152936753 15106305090418465614702565)
                    ·
                      refine ⟨2832432204453462302756731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15106305090418465614702565 2832432204453462302756731)
                      ·
                        rfl

theorem cell23_5516142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5516142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516142 prefixEnd_5516142 := by exact prefixLift 5516142
  have htrace : WordTrace (prefixWord ++ tailWord_5516142) baseStart_5516142 baseEnd_5516142 := by
    simpa [prefixWord, tailWord_5516142, baseEnd_5516142] using wordTrace_append hprefix tailTrace_5516142
  have hstable : (prefixWord ++ tailWord_5516142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516142).length < 2 ^ (prefixWord ++ tailWord_5516142).sum := by decide
  have hdescent : baseEnd_5516142 < baseStart_5516142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516145 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_5516145 : Nat := 118140960795 + 5516145 * 2 ^ 59
def prefixEnd_5516145 : Nat := 4983230072969 + 3 ^ 40 * 5516145 * 2
def baseEnd_5516145 : Nat := 2832433744895425791019217

theorem tailTrace_5516145 : CollatzResearch.WordTrace tailWord_5516145 prefixEnd_5516145 2832433744895425791019217 := by
  unfold tailWord_5516145
  simp only [CollatzResearch.WordTrace]
  refine ⟨201190336600956222408085889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134126891067304148272057259 201190336600956222408085889)
  ·
    refine ⟨150892752450717166806064417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201190336600956222408085889 150892752450717166806064417)
    ·
      refine ⟨113169564338037875104548313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150892752450717166806064417 113169564338037875104548313)
      ·
        refine ⟨84877173253528406328411235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113169564338037875104548313 84877173253528406328411235)
        ·
          refine ⟨127315759880292609492616853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84877173253528406328411235 127315759880292609492616853)
          ·
            refine ⟨5967926244388716069966415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127315759880292609492616853 5967926244388716069966415)
            ·
              refine ⟨8951889366583074104949623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5967926244388716069966415 8951889366583074104949623)
              ·
                refine ⟨13427834049874611157424435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8951889366583074104949623 13427834049874611157424435)
                ·
                  refine ⟨20141751074811916736136653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13427834049874611157424435 20141751074811916736136653)
                  ·
                    refine ⟨7553156653054468776051245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20141751074811916736136653 7553156653054468776051245)
                    ·
                      refine ⟨2832433744895425791019217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553156653054468776051245 2832433744895425791019217)
                      ·
                        rfl

theorem cell23_5516145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_5516145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516145 prefixEnd_5516145 := by exact prefixLift 5516145
  have htrace : WordTrace (prefixWord ++ tailWord_5516145) baseStart_5516145 baseEnd_5516145 := by
    simpa [prefixWord, tailWord_5516145, baseEnd_5516145] using wordTrace_append hprefix tailTrace_5516145
  have hstable : (prefixWord ++ tailWord_5516145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516145).length < 2 ^ (prefixWord ++ tailWord_5516145).sum := by decide
  have hdescent : baseEnd_5516145 < baseStart_5516145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516151 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_5516151 : Nat := 118140960795 + 5516151 * 2 ^ 59
def prefixEnd_5516151 : Nat := 4983230072969 + 3 ^ 40 * 5516151 * 2
def baseEnd_5516151 : Nat := 2832436825779352767544189

theorem tailTrace_5516151 : CollatzResearch.WordTrace tailWord_5516151 prefixEnd_5516151 2832436825779352767544189 := by
  unfold tailWord_5516151
  simp only [CollatzResearch.WordTrace]
  refine ⟨201190555438934485432804307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134127036959289656955202871 201190555438934485432804307)
  ·
    refine ⟨301785833158401728149206461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201190555438934485432804307 301785833158401728149206461)
    ·
      refine ⟨113169687434400648055952423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301785833158401728149206461 113169687434400648055952423)
      ·
        refine ⟨169754531151600972083928635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113169687434400648055952423 169754531151600972083928635)
        ·
          refine ⟨254631796727401458125892953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169754531151600972083928635 254631796727401458125892953)
          ·
            refine ⟨190973847545551093594419715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254631796727401458125892953 190973847545551093594419715)
            ·
              refine ⟨286460771318326640391629573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190973847545551093594419715 286460771318326640391629573)
              ·
                refine ⟨53711394622186245073430545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286460771318326640391629573 53711394622186245073430545)
                ·
                  refine ⟨40283545966639683805072909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53711394622186245073430545 40283545966639683805072909)
                  ·
                    refine ⟨15106329737489881426902341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40283545966639683805072909 15106329737489881426902341)
                    ·
                      refine ⟨2832436825779352767544189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15106329737489881426902341 2832436825779352767544189)
                      ·
                        rfl

theorem cell23_5516151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_5516151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516151 prefixEnd_5516151 := by exact prefixLift 5516151
  have htrace : WordTrace (prefixWord ++ tailWord_5516151) baseStart_5516151 baseEnd_5516151 := by
    simpa [prefixWord, tailWord_5516151, baseEnd_5516151] using wordTrace_append hprefix tailTrace_5516151
  have hstable : (prefixWord ++ tailWord_5516151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516151).length < 2 ^ (prefixWord ++ tailWord_5516151).sum := by decide
  have hdescent : baseEnd_5516151 < baseStart_5516151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516155 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 1, 3, 2]
def baseStart_5516155 : Nat := 118140960795 + 5516155 * 2 ^ 59
def prefixEnd_5516155 : Nat := 4983230072969 + 3 ^ 40 * 5516155 * 2
def baseEnd_5516155 : Nat := 2832438879701970751894171

theorem tailTrace_5516155 : CollatzResearch.WordTrace tailWord_5516155 prefixEnd_5516155 2832438879701970751894171 := by
  unfold tailWord_5516155
  simp only [CollatzResearch.WordTrace]
  refine ⟨201190701330919994115949919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134127134220613329410633279 201190701330919994115949919)
  ·
    refine ⟨301786051996379991173924879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201190701330919994115949919 301786051996379991173924879)
    ·
      refine ⟨452679077994569986760887319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301786051996379991173924879 452679077994569986760887319)
      ·
        refine ⟨679018616991854980141330979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452679077994569986760887319 679018616991854980141330979)
        ·
          refine ⟨1018527925487782470211996469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679018616991854980141330979 1018527925487782470211996469)
          ·
            refine ⟨95486993014479606582374669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1018527925487782470211996469 95486993014479606582374669)
            ·
              refine ⟨35807622380429852468390501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95486993014479606582374669 35807622380429852468390501)
              ·
                refine ⟨6713929196330597337823219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35807622380429852468390501 6713929196330597337823219)
                ·
                  refine ⟨10070893794495896006734829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6713929196330597337823219 10070893794495896006734829)
                  ·
                    refine ⟨3776585172935961002525561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10070893794495896006734829 3776585172935961002525561)
                    ·
                      refine ⟨2832438879701970751894171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776585172935961002525561 2832438879701970751894171)
                      ·
                        rfl

theorem cell23_5516155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3, 2].length) (baseStart_5516155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516155 prefixEnd_5516155 := by exact prefixLift 5516155
  have htrace : WordTrace (prefixWord ++ tailWord_5516155) baseStart_5516155 baseEnd_5516155 := by
    simpa [prefixWord, tailWord_5516155, baseEnd_5516155] using wordTrace_append hprefix tailTrace_5516155
  have hstable : (prefixWord ++ tailWord_5516155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516155).length < 2 ^ (prefixWord ++ tailWord_5516155).sum := by decide
  have hdescent : baseEnd_5516155 < baseStart_5516155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516171 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_5516171 : Nat := 118140960795 + 5516171 * 2 ^ 59
def prefixEnd_5516171 : Nat := 4983230072969 + 3 ^ 40 * 5516171 * 2
def baseEnd_5516171 : Nat := 2832447095392442689294097

theorem tailTrace_5516171 : CollatzResearch.WordTrace tailWord_5516171 prefixEnd_5516171 2832447095392442689294097 := by
  unfold tailWord_5516171
  simp only [CollatzResearch.WordTrace]
  refine ⟨201191284898862028848532367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134127523265908019232354911 201191284898862028848532367)
  ·
    refine ⟨301786927348293043272798551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201191284898862028848532367 301786927348293043272798551)
    ·
      refine ⟨452680391022439564909197827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301786927348293043272798551 452680391022439564909197827)
      ·
        refine ⟨679020586533659347363796741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452680391022439564909197827 679020586533659347363796741)
        ·
          refine ⟨127316359975061127630711889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 679020586533659347363796741 127316359975061127630711889)
          ·
            refine ⟨95487269981295845723033917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127316359975061127630711889 95487269981295845723033917)
            ·
              refine ⟨35807726242985942146137719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95487269981295845723033917 35807726242985942146137719)
              ·
                refine ⟨53711589364478913219206579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35807726242985942146137719 53711589364478913219206579)
                ·
                  refine ⟨80567384046718369828809869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53711589364478913219206579 80567384046718369828809869)
                  ·
                    refine ⟨30212769017519388685803701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80567384046718369828809869 30212769017519388685803701)
                    ·
                      refine ⟨2832447095392442689294097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30212769017519388685803701 2832447095392442689294097)
                      ·
                        rfl

theorem cell23_5516171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_5516171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516171 prefixEnd_5516171 := by exact prefixLift 5516171
  have htrace : WordTrace (prefixWord ++ tailWord_5516171) baseStart_5516171 baseEnd_5516171 := by
    simpa [prefixWord, tailWord_5516171, baseEnd_5516171] using wordTrace_append hprefix tailTrace_5516171
  have hstable : (prefixWord ++ tailWord_5516171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516171).length < 2 ^ (prefixWord ++ tailWord_5516171).sum := by decide
  have hdescent : baseEnd_5516171 < baseStart_5516171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516230 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5516230 : Nat := 118140960795 + 5516230 * 2 ^ 59
def prefixEnd_5516230 : Nat := 4983230072969 + 3 ^ 40 * 5516230 * 2
def baseEnd_5516230 : Nat := 2832477390751057958456327

theorem tailTrace_5516230 : CollatzResearch.WordTrace tailWord_5516230 prefixEnd_5516230 2832477390751057958456327 := by
  unfold tailWord_5516230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287294900176508810154067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134128957870432187949953429 6287294900176508810154067)
  ·
    refine ⟨9430942350264763215231101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6287294900176508810154067 9430942350264763215231101)
    ·
      refine ⟨3536603381349286205711663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9430942350264763215231101 3536603381349286205711663)
      ·
        refine ⟨5304905072023929308567495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536603381349286205711663 5304905072023929308567495)
        ·
          refine ⟨7957357608035893962851243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304905072023929308567495 7957357608035893962851243)
          ·
            refine ⟨11936036412053840944276865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957357608035893962851243 11936036412053840944276865)
            ·
              refine ⟨8952027309040380708207649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936036412053840944276865 8952027309040380708207649)
              ·
                refine ⟨6714020481780285531155737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952027309040380708207649 6714020481780285531155737)
                ·
                  refine ⟨5035515361335214148366803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714020481780285531155737 5035515361335214148366803)
                  ·
                    refine ⟨7553273042002821222550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035515361335214148366803 7553273042002821222550205)
                    ·
                      refine ⟨2832477390751057958456327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553273042002821222550205 2832477390751057958456327)
                      ·
                        rfl

theorem cell23_5516230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5516230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516230 prefixEnd_5516230 := by exact prefixLift 5516230
  have htrace : WordTrace (prefixWord ++ tailWord_5516230) baseStart_5516230 baseEnd_5516230 := by
    simpa [prefixWord, tailWord_5516230, baseEnd_5516230] using wordTrace_append hprefix tailTrace_5516230
  have hstable : (prefixWord ++ tailWord_5516230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516230).length < 2 ^ (prefixWord ++ tailWord_5516230).sum := by decide
  have hdescent : baseEnd_5516230 < baseStart_5516230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516242 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_5516242 : Nat := 118140960795 + 5516242 * 2 ^ 59
def prefixEnd_5516242 : Nat := 4983230072969 + 3 ^ 40 * 5516242 * 2
def baseEnd_5516242 : Nat := 314720394724323545722919

theorem tailTrace_5516242 : CollatzResearch.WordTrace tailWord_5516242 prefixEnd_5516242 314720394724323545722919 := by
  unfold tailWord_5516242
  simp only [CollatzResearch.WordTrace]
  refine ⟨50298468620401201993591745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134129249654403205316244653 50298468620401201993591745)
  ·
    refine ⟨37723851465300901495193809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50298468620401201993591745 37723851465300901495193809)
    ·
      refine ⟨28292888598975676121395357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37723851465300901495193809 28292888598975676121395357)
      ·
        refine ⟨10609833224615878545523259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28292888598975676121395357 10609833224615878545523259)
        ·
          refine ⟨15914749836923817818284889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10609833224615878545523259 15914749836923817818284889)
          ·
            refine ⟨11936062377692863363713667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15914749836923817818284889 11936062377692863363713667)
            ·
              refine ⟨17904093566539295045570501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11936062377692863363713667 17904093566539295045570501)
              ·
                refine ⟨3357017543726117821044469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17904093566539295045570501 3357017543726117821044469)
                ·
                  refine ⟨314720394724323545722919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357017543726117821044469 314720394724323545722919)
                  ·
                    rfl

theorem cell23_5516242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_5516242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516242 prefixEnd_5516242 := by exact prefixLift 5516242
  have htrace : WordTrace (prefixWord ++ tailWord_5516242) baseStart_5516242 baseEnd_5516242 := by
    simpa [prefixWord, tailWord_5516242, baseEnd_5516242] using wordTrace_append hprefix tailTrace_5516242
  have hstable : (prefixWord ++ tailWord_5516242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516242).length < 2 ^ (prefixWord ++ tailWord_5516242).sum := by decide
  have hdescent : baseEnd_5516242 < baseStart_5516242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516248 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5516248 : Nat := 118140960795 + 5516248 * 2 ^ 59
def prefixEnd_5516248 : Nat := 4983230072969 + 3 ^ 40 * 5516248 * 2
def baseEnd_5516248 : Nat := 2832486633402838888031243

theorem tailTrace_5516248 : CollatzResearch.WordTrace tailWord_5516248 prefixEnd_5516248 2832486633402838888031243 := by
  unfold tailWord_5516248
  simp only [CollatzResearch.WordTrace]
  refine ⟨100597046659791535499542699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134129395546388713999390265 100597046659791535499542699)
  ·
    refine ⟨150895569989687303249314049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100597046659791535499542699 150895569989687303249314049)
    ·
      refine ⟨113171677492265477436985537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150895569989687303249314049 113171677492265477436985537)
      ·
        refine ⟨84878758119199108077739153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113171677492265477436985537 84878758119199108077739153)
        ·
          refine ⟨63659068589399331058304365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84878758119199108077739153 63659068589399331058304365)
          ·
            refine ⟨23872150721024749146864137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63659068589399331058304365 23872150721024749146864137)
            ·
              refine ⟨17904113040768561860148103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23872150721024749146864137 17904113040768561860148103)
              ·
                refine ⟨26856169561152842790222155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17904113040768561860148103 26856169561152842790222155)
                ·
                  refine ⟨40284254341729264185333233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26856169561152842790222155 40284254341729264185333233)
                  ·
                    refine ⟨30213190756296948138999925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40284254341729264185333233 30213190756296948138999925)
                    ·
                      refine ⟨2832486633402838888031243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30213190756296948138999925 2832486633402838888031243)
                      ·
                        rfl

theorem cell23_5516248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5516248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516248 prefixEnd_5516248 := by exact prefixLift 5516248
  have htrace : WordTrace (prefixWord ++ tailWord_5516248) baseStart_5516248 baseEnd_5516248 := by
    simpa [prefixWord, tailWord_5516248, baseEnd_5516248] using wordTrace_append hprefix tailTrace_5516248
  have hstable : (prefixWord ++ tailWord_5516248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516248).length < 2 ^ (prefixWord ++ tailWord_5516248).sum := by decide
  have hdescent : baseEnd_5516248 < baseStart_5516248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516295 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5516295 : Nat := 118140960795 + 5516295 * 2 ^ 59
def prefixEnd_5516295 : Nat := 4983230072969 + 3 ^ 40 * 5516295 * 2
def baseEnd_5516295 : Nat := 2832510766993600204143527

theorem tailTrace_5516295 : CollatzResearch.WordTrace tailWord_5516295 prefixEnd_5516295 2832510766993600204143527 := by
  unfold tailWord_5516295
  simp only [CollatzResearch.WordTrace]
  refine ⟨201195807550412798026046339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134130538366941865350697559 201195807550412798026046339)
  ·
    refine ⟨301793711325619197039069509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201195807550412798026046339 301793711325619197039069509)
    ·
      refine ⟨56586320873553599444825533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301793711325619197039069509 56586320873553599444825533)
      ·
        refine ⟨21219870327582599791809575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56586320873553599444825533 21219870327582599791809575)
        ·
          refine ⟨31829805491373899687714363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21219870327582599791809575 31829805491373899687714363)
          ·
            refine ⟨47744708237060849531571545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31829805491373899687714363 47744708237060849531571545)
            ·
              refine ⟨35808531177795637148678659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47744708237060849531571545 35808531177795637148678659)
              ·
                refine ⟨53712796766693455723017989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35808531177795637148678659 53712796766693455723017989)
                ·
                  refine ⟨10071149393755022948065873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53712796766693455723017989 10071149393755022948065873)
                  ·
                    refine ⟨7553362045316267211049405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10071149393755022948065873 7553362045316267211049405)
                    ·
                      refine ⟨2832510766993600204143527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553362045316267211049405 2832510766993600204143527)
                      ·
                        rfl

theorem cell23_5516295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5516295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516295 prefixEnd_5516295 := by exact prefixLift 5516295
  have htrace : WordTrace (prefixWord ++ tailWord_5516295) baseStart_5516295 baseEnd_5516295 := by
    simpa [prefixWord, tailWord_5516295, baseEnd_5516295] using wordTrace_append hprefix tailTrace_5516295
  have hstable : (prefixWord ++ tailWord_5516295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516295).length < 2 ^ (prefixWord ++ tailWord_5516295).sum := by decide
  have hdescent : baseEnd_5516295 < baseStart_5516295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516302 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_5516302 : Nat := 118140960795 + 5516302 * 2 ^ 59
def prefixEnd_5516302 : Nat := 4983230072969 + 3 ^ 40 * 5516302 * 2
def baseEnd_5516302 : Nat := 944171453786060558918665

theorem tailTrace_5516302 : CollatzResearch.WordTrace tailWord_5516302 prefixEnd_5516302 944171453786060558918665 := by
  unfold tailWord_5516302
  simp only [CollatzResearch.WordTrace]
  refine ⟨25149507857673429777693895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134130708574258292147700773 25149507857673429777693895)
  ·
    refine ⟨37724261786510144666540843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25149507857673429777693895 37724261786510144666540843)
    ·
      refine ⟨56586392679765216999811265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37724261786510144666540843 56586392679765216999811265)
      ·
        refine ⟨42439794509823912749858449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56586392679765216999811265 42439794509823912749858449)
        ·
          refine ⟨31829845882367934562393837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42439794509823912749858449 31829845882367934562393837)
          ·
            refine ⟨11936192205887975460897689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31829845882367934562393837 11936192205887975460897689)
            ·
              refine ⟨8952144154415981595673267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936192205887975460897689 8952144154415981595673267)
              ·
                refine ⟨13428216231623972393509901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8952144154415981595673267 13428216231623972393509901)
                ·
                  refine ⟨5035581086858989647566213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13428216231623972393509901 5035581086858989647566213)
                  ·
                    refine ⟨944171453786060558918665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035581086858989647566213 944171453786060558918665)
                    ·
                      rfl

theorem cell23_5516302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_5516302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516302 prefixEnd_5516302 := by exact prefixLift 5516302
  have htrace : WordTrace (prefixWord ++ tailWord_5516302) baseStart_5516302 baseEnd_5516302 := by
    simpa [prefixWord, tailWord_5516302, baseEnd_5516302] using wordTrace_append hprefix tailTrace_5516302
  have hstable : (prefixWord ++ tailWord_5516302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516302).length < 2 ^ (prefixWord ++ tailWord_5516302).sum := by decide
  have hdescent : baseEnd_5516302 < baseStart_5516302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516352 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2]
def baseStart_5516352 : Nat := 118140960795 + 5516352 * 2 ^ 59
def prefixEnd_5516352 : Nat := 4983230072969 + 3 ^ 40 * 5516352 * 2
def baseEnd_5516352 : Nat := 2832540035390906481130765

theorem tailTrace_5516352 : CollatzResearch.WordTrace tailWord_5516352 prefixEnd_5516352 2832540035390906481130765 := by
  unfold tailWord_5516352
  simp only [CollatzResearch.WordTrace]
  refine ⟨100598943255603148380435655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134131924340804197840580873 100598943255603148380435655)
  ·
    refine ⟨150898414883404722570653483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100598943255603148380435655 150898414883404722570653483)
    ·
      refine ⟨226347622325107083855980225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150898414883404722570653483 226347622325107083855980225)
      ·
        refine ⟨169760716743830312891985169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226347622325107083855980225 169760716743830312891985169)
        ·
          refine ⟨127320537557872734668988877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169760716743830312891985169 127320537557872734668988877)
          ·
            refine ⟨47745201584202275500870829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127320537557872734668988877 47745201584202275500870829)
            ·
              refine ⟨17904450594075853312826561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47745201584202275500870829 17904450594075853312826561)
              ·
                refine ⟨13428337945556889984619921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17904450594075853312826561 13428337945556889984619921)
                ·
                  refine ⟨10071253459167667488464941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13428337945556889984619921 10071253459167667488464941)
                  ·
                    refine ⟨3776720047187875308174353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10071253459167667488464941 3776720047187875308174353)
                    ·
                      refine ⟨2832540035390906481130765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776720047187875308174353 2832540035390906481130765)
                      ·
                        rfl

theorem cell23_5516352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_5516352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516352 prefixEnd_5516352 := by exact prefixLift 5516352
  have htrace : WordTrace (prefixWord ++ tailWord_5516352) baseStart_5516352 baseEnd_5516352 := by
    simpa [prefixWord, tailWord_5516352, baseEnd_5516352] using wordTrace_append hprefix tailTrace_5516352
  have hstable : (prefixWord ++ tailWord_5516352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516352).length < 2 ^ (prefixWord ++ tailWord_5516352).sum := by decide
  have hdescent : baseEnd_5516352 < baseStart_5516352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516359 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_5516359 : Nat := 118140960795 + 5516359 * 2 ^ 59
def prefixEnd_5516359 : Nat := 4983230072969 + 3 ^ 40 * 5516359 * 2
def baseEnd_5516359 : Nat := 2832543629755487953743233

theorem tailTrace_5516359 : CollatzResearch.WordTrace tailWord_5516359 prefixEnd_5516359 2832543629755487953743233 := by
  unfold tailWord_5516359
  simp only [CollatzResearch.WordTrace]
  refine ⟨201198141822180936956376131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134132094548120624637584087 201198141822180936956376131)
  ·
    refine ⟨301797212733271405434564197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201198141822180936956376131 301797212733271405434564197)
    ·
      refine ⟨56586977387488388518980787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301797212733271405434564197 56586977387488388518980787)
      ·
        refine ⟨84880466081232582778471181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56586977387488388518980787 84880466081232582778471181)
        ·
          refine ⟨31830174780462218541926693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84880466081232582778471181 31830174780462218541926693)
          ·
            refine ⟨5968157771336665976611255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31830174780462218541926693 5968157771336665976611255)
            ·
              refine ⟨8952236657004998964916883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968157771336665976611255 8952236657004998964916883)
              ·
                refine ⟨13428354985507498447375325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8952236657004998964916883 13428354985507498447375325)
                ·
                  refine ⟨5035633119565311917765747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13428354985507498447375325 5035633119565311917765747)
                  ·
                    refine ⟨7553449679347967876648621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035633119565311917765747 7553449679347967876648621)
                    ·
                      refine ⟨2832543629755487953743233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553449679347967876648621 2832543629755487953743233)
                      ·
                        rfl

theorem cell23_5516359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_5516359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516359 prefixEnd_5516359 := by exact prefixLift 5516359
  have htrace : WordTrace (prefixWord ++ tailWord_5516359) baseStart_5516359 baseEnd_5516359 := by
    simpa [prefixWord, tailWord_5516359, baseEnd_5516359] using wordTrace_append hprefix tailTrace_5516359
  have hstable : (prefixWord ++ tailWord_5516359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516359).length < 2 ^ (prefixWord ++ tailWord_5516359).sum := by decide
  have hdescent : baseEnd_5516359 < baseStart_5516359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516386 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5516386 : Nat := 118140960795 + 5516386 * 2 ^ 59
def prefixEnd_5516386 : Nat := 4983230072969 + 3 ^ 40 * 5516386 * 2
def baseEnd_5516386 : Nat := 2832557493733159348105609

theorem tailTrace_5516386 : CollatzResearch.WordTrace tailWord_5516386 prefixEnd_5516386 2832557493733159348105609 := by
  unfold tailWord_5516386
  simp only [CollatzResearch.WordTrace]
  refine ⟨50299781648270780141902253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134132751062055413711739341 50299781648270780141902253)
  ·
    refine ⟨18862418118101542553213345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50299781648270780141902253 18862418118101542553213345)
    ·
      refine ⟨14146813588576156914910009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18862418118101542553213345 14146813588576156914910009)
      ·
        refine ⟨10610110191432117686182507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14146813588576156914910009 10610110191432117686182507)
        ·
          refine ⟨15915165287148176529273761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610110191432117686182507 15915165287148176529273761)
          ·
            refine ⟨11936373965361132396955321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15915165287148176529273761 11936373965361132396955321)
            ·
              refine ⟨8952280474020849297716491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936373965361132396955321 8952280474020849297716491)
              ·
                refine ⟨13428420711031273946574737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8952280474020849297716491 13428420711031273946574737)
                ·
                  refine ⟨10071315533273455459931053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13428420711031273946574737 10071315533273455459931053)
                  ·
                    refine ⟨3776743324977545797474145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10071315533273455459931053 3776743324977545797474145)
                    ·
                      refine ⟨2832557493733159348105609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776743324977545797474145 2832557493733159348105609)
                      ·
                        rfl

theorem cell23_5516386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5516386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516386 prefixEnd_5516386 := by exact prefixLift 5516386
  have htrace : WordTrace (prefixWord ++ tailWord_5516386) baseStart_5516386 baseEnd_5516386 := by
    simpa [prefixWord, tailWord_5516386, baseEnd_5516386] using wordTrace_append hprefix tailTrace_5516386
  have hstable : (prefixWord ++ tailWord_5516386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516386).length < 2 ^ (prefixWord ++ tailWord_5516386).sum := by decide
  have hdescent : baseEnd_5516386 < baseStart_5516386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516405 : List Nat := [1, 3, 4, 3, 12]
def baseStart_5516405 : Nat := 118140960795 + 5516405 * 2 ^ 59
def prefixEnd_5516405 : Nat := 4983230072969 + 3 ^ 40 * 5516405 * 2
def baseEnd_5516405 : Nat := 3885551783080376918749

theorem tailTrace_5516405 : CollatzResearch.WordTrace tailWord_5516405 prefixEnd_5516405 3885551783080376918749 := by
  unfold tailWord_5516405
  simp only [CollatzResearch.WordTrace]
  refine ⟨201199819580014286812550669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134133213053342857875033779 201199819580014286812550669)
  ·
    refine ⟨75449932342505357554706501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201199819580014286812550669 75449932342505357554706501)
    ·
      refine ⟨14146862314219754541507469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75449932342505357554706501 14146862314219754541507469)
      ·
        refine ⟨5305073367832407953065301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14146862314219754541507469 5305073367832407953065301)
        ·
          refine ⟨3885551783080376918749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5305073367832407953065301 3885551783080376918749)
          ·
            rfl

theorem cell23_5516405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 12].length) (baseStart_5516405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516405 prefixEnd_5516405 := by exact prefixLift 5516405
  have htrace : WordTrace (prefixWord ++ tailWord_5516405) baseStart_5516405 baseEnd_5516405 := by
    simpa [prefixWord, tailWord_5516405, baseEnd_5516405] using wordTrace_append hprefix tailTrace_5516405
  have hstable : (prefixWord ++ tailWord_5516405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516405).length < 2 ^ (prefixWord ++ tailWord_5516405).sum := by decide
  have hdescent : baseEnd_5516405 < baseStart_5516405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516409 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_5516409 : Nat := 118140960795 + 5516409 * 2 ^ 59
def prefixEnd_5516409 : Nat := 4983230072969 + 3 ^ 40 * 5516409 * 2
def baseEnd_5516409 : Nat := 944189767929404252706001

theorem tailTrace_5516409 : CollatzResearch.WordTrace tailWord_5516409 prefixEnd_5516409 944189767929404252706001 := by
  unfold tailWord_5516409
  simp only [CollatzResearch.WordTrace]
  refine ⟨201199965471999795495696281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134133310314666530330464187 201199965471999795495696281)
  ·
    refine ⟨150899974103999846621772211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201199965471999795495696281 150899974103999846621772211)
    ·
      refine ⟨226349961155999769932658317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150899974103999846621772211 226349961155999769932658317)
      ·
        refine ⟨84881235433499913724746869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226349961155999769932658317 84881235433499913724746869)
        ·
          refine ⟨7957615821890616911695019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84881235433499913724746869 7957615821890616911695019)
          ·
            refine ⟨11936423732835925367542529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957615821890616911695019 11936423732835925367542529)
            ·
              refine ⟨8952317799626944025656897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936423732835925367542529 8952317799626944025656897)
              ·
                refine ⟨6714238349720208019242673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952317799626944025656897 6714238349720208019242673)
                ·
                  refine ⟨5035678762290156014432005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714238349720208019242673 5035678762290156014432005)
                  ·
                    refine ⟨944189767929404252706001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035678762290156014432005 944189767929404252706001)
                    ·
                      rfl

theorem cell23_5516409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_5516409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516409 prefixEnd_5516409 := by exact prefixLift 5516409
  have htrace : WordTrace (prefixWord ++ tailWord_5516409) baseStart_5516409 baseEnd_5516409 := by
    simpa [prefixWord, tailWord_5516409, baseEnd_5516409] using wordTrace_append hprefix tailTrace_5516409
  have hstable : (prefixWord ++ tailWord_5516409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516409).length < 2 ^ (prefixWord ++ tailWord_5516409).sum := by decide
  have hdescent : baseEnd_5516409 < baseStart_5516409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516445 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5516445 : Nat := 118140960795 + 5516445 * 2 ^ 59
def prefixEnd_5516445 : Nat := 4983230072969 + 3 ^ 40 * 5516445 * 2
def baseEnd_5516445 : Nat := 2832587789091774617267837

theorem tailTrace_5516445 : CollatzResearch.WordTrace tailWord_5516445 prefixEnd_5516445 2832587789091774617267837 := by
  unfold tailWord_5516445
  simp only [CollatzResearch.WordTrace]
  refine ⟨201201278499869373644006789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134134185666579582429337859 201201278499869373644006789)
  ·
    refine ⟨37725239718725507558251273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201201278499869373644006789 37725239718725507558251273)
    ·
      refine ⟨28293929789044130668688455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37725239718725507558251273 28293929789044130668688455)
      ·
        refine ⟨42440894683566196003032683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28293929789044130668688455 42440894683566196003032683)
        ·
          refine ⟨63661342025349294004549025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42440894683566196003032683 63661342025349294004549025)
          ·
            refine ⟨47746006519011970503411769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63661342025349294004549025 47746006519011970503411769)
            ·
              refine ⟨35809504889258977877558827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47746006519011970503411769 35809504889258977877558827)
              ·
                refine ⟨53714257333888466816338241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35809504889258977877558827 53714257333888466816338241)
                ·
                  refine ⟨40285693000416350112253681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53714257333888466816338241 40285693000416350112253681)
                  ·
                    refine ⟨30214269750312262584190261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40285693000416350112253681 30214269750312262584190261)
                    ·
                      refine ⟨2832587789091774617267837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30214269750312262584190261 2832587789091774617267837)
                      ·
                        rfl

theorem cell23_5516445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5516445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516445 prefixEnd_5516445 := by exact prefixLift 5516445
  have htrace : WordTrace (prefixWord ++ tailWord_5516445) baseStart_5516445 baseEnd_5516445 := by
    simpa [prefixWord, tailWord_5516445, baseEnd_5516445] using wordTrace_append hprefix tailTrace_5516445
  have hstable : (prefixWord ++ tailWord_5516445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516445).length < 2 ^ (prefixWord ++ tailWord_5516445).sum := by decide
  have hdescent : baseEnd_5516445 < baseStart_5516445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516450 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_5516450 : Nat := 118140960795 + 5516450 * 2 ^ 59
def prefixEnd_5516450 : Nat := 4983230072969 + 3 ^ 40 * 5516450 * 2
def baseEnd_5516450 : Nat := 2832590356495047097705315

theorem tailTrace_5516450 : CollatzResearch.WordTrace tailWord_5516450 prefixEnd_5516450 2832590356495047097705315 := by
  unfold tailWord_5516450
  simp only [CollatzResearch.WordTrace]
  refine ⟨50300365216212814874484701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134134307243234172998625869 50300365216212814874484701)
  ·
    refine ⟨18862636956079805577931763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50300365216212814874484701 18862636956079805577931763)
    ·
      refine ⟨28293955434119708366897645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18862636956079805577931763 28293955434119708366897645)
      ·
        refine ⟨10610233287794890637586617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28293955434119708366897645 10610233287794890637586617)
        ·
          refine ⟨7957674965846167978189963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10610233287794890637586617 7957674965846167978189963)
          ·
            refine ⟨11936512448769251967284945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957674965846167978189963 11936512448769251967284945)
            ·
              refine ⟨8952384336576938975463709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936512448769251967284945 8952384336576938975463709)
              ·
                refine ⟨3357144126216352115798891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8952384336576938975463709 3357144126216352115798891)
                ·
                  refine ⟨5035716189324528173698337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357144126216352115798891 5035716189324528173698337)
                  ·
                    refine ⟨3776787141993396130273753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035716189324528173698337 3776787141993396130273753)
                    ·
                      refine ⟨2832590356495047097705315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776787141993396130273753 2832590356495047097705315)
                      ·
                        rfl

theorem cell23_5516450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_5516450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516450 prefixEnd_5516450 := by exact prefixLift 5516450
  have htrace : WordTrace (prefixWord ++ tailWord_5516450) baseStart_5516450 baseEnd_5516450 := by
    simpa [prefixWord, tailWord_5516450, baseEnd_5516450] using wordTrace_append hprefix tailTrace_5516450
  have hstable : (prefixWord ++ tailWord_5516450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516450).length < 2 ^ (prefixWord ++ tailWord_5516450).sum := by decide
  have hdescent : baseEnd_5516450 < baseStart_5516450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516466 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_5516466 : Nat := 118140960795 + 5516466 * 2 ^ 59
def prefixEnd_5516466 : Nat := 4983230072969 + 3 ^ 40 * 5516466 * 2
def baseEnd_5516466 : Nat := 2832598572185519035105241

theorem tailTrace_5516466 : CollatzResearch.WordTrace tailWord_5516466 prefixEnd_5516466 2832598572185519035105241 := by
  unfold tailWord_5516466
  simp only [CollatzResearch.WordTrace]
  refine ⟨50300511108198323557630313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134134696288528862820347501 50300511108198323557630313)
  ·
    refine ⟨37725383331148742668222735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50300511108198323557630313 37725383331148742668222735)
    ·
      refine ⟨56588074996723114002334103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37725383331148742668222735 56588074996723114002334103)
      ·
        refine ⟨84882112495084671003501155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56588074996723114002334103 84882112495084671003501155)
        ·
          refine ⟨127323168742627006505251733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84882112495084671003501155 127323168742627006505251733)
          ·
            refine ⟨5968273534810640929933675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127323168742627006505251733 5968273534810640929933675)
            ·
              refine ⟨8952410302215961394900513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968273534810640929933675 8952410302215961394900513)
              ·
                refine ⟨6714307726661971046175385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952410302215961394900513 6714307726661971046175385)
                ·
                  refine ⟨5035730794996478284631539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714307726661971046175385 5035730794996478284631539)
                  ·
                    refine ⟨7553596192494717426947309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035730794996478284631539 7553596192494717426947309)
                    ·
                      refine ⟨2832598572185519035105241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553596192494717426947309 2832598572185519035105241)
                      ·
                        rfl

theorem cell23_5516466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_5516466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516466 prefixEnd_5516466 := by exact prefixLift 5516466
  have htrace : WordTrace (prefixWord ++ tailWord_5516466) baseStart_5516466 baseEnd_5516466 := by
    simpa [prefixWord, tailWord_5516466, baseEnd_5516466] using wordTrace_append hprefix tailTrace_5516466
  have hstable : (prefixWord ++ tailWord_5516466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516466).length < 2 ^ (prefixWord ++ tailWord_5516466).sum := by decide
  have hdescent : baseEnd_5516466 < baseStart_5516466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516475 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3]
def baseStart_5516475 : Nat := 118140960795 + 5516475 * 2 ^ 59
def prefixEnd_5516475 : Nat := 4983230072969 + 3 ^ 40 * 5516475 * 2
def baseEnd_5516475 : Nat := 2832603193511409499892699

theorem tailTrace_5516475 : CollatzResearch.WordTrace tailWord_5516475 prefixEnd_5516475 2832603193511409499892699 := by
  unfold tailWord_5516475
  simp only [CollatzResearch.WordTrace]
  refine ⟨201202372689760688767598879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134134915126507125845065919 201202372689760688767598879)
  ·
    refine ⟨301803559034641033151398319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201202372689760688767598879 301803559034641033151398319)
    ·
      refine ⟨452705338551961549727097479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301803559034641033151398319 452705338551961549727097479)
      ·
        refine ⟨679058007827942324590646219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452705338551961549727097479 679058007827942324590646219)
        ·
          refine ⟨1018587011741913486885969329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679058007827942324590646219 1018587011741913486885969329)
          ·
            refine ⟨763940258806435115164476997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018587011741913486885969329 763940258806435115164476997)
            ·
              refine ⟨143238798526206584093339437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 763940258806435115164476997 143238798526206584093339437)
              ·
                refine ⟨53714549447327469035002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143238798526206584093339437 53714549447327469035002289)
                ·
                  refine ⟨40285912085495601776251717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53714549447327469035002289 40285912085495601776251717)
                  ·
                    refine ⟨7553608516030425333047197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40285912085495601776251717 7553608516030425333047197)
                    ·
                      refine ⟨2832603193511409499892699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553608516030425333047197 2832603193511409499892699)
                      ·
                        rfl

theorem cell23_5516475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].length) (baseStart_5516475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516475 prefixEnd_5516475 := by exact prefixLift 5516475
  have htrace : WordTrace (prefixWord ++ tailWord_5516475) baseStart_5516475 baseEnd_5516475 := by
    simpa [prefixWord, tailWord_5516475, baseEnd_5516475] using wordTrace_append hprefix tailTrace_5516475
  have hstable : (prefixWord ++ tailWord_5516475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516475).length < 2 ^ (prefixWord ++ tailWord_5516475).sum := by decide
  have hdescent : baseEnd_5516475 < baseStart_5516475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516509 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5516509 : Nat := 118140960795 + 5516509 * 2 ^ 59
def prefixEnd_5516509 : Nat := 4983230072969 + 3 ^ 40 * 5516509 * 2
def baseEnd_5516509 : Nat := 2832620651853662366867543

theorem tailTrace_5516509 : CollatzResearch.WordTrace tailWord_5516509 prefixEnd_5516509 2832620651853662366867543 := by
  unfold tailWord_5516509
  simp only [CollatzResearch.WordTrace]
  refine ⟨201203612771637512574336581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134135741847758341716224387 201203612771637512574336581)
  ·
    refine ⟨37725677394682033607688109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201203612771637512574336581 37725677394682033607688109)
    ·
      refine ⟨14147129023005762602883041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37725677394682033607688109 14147129023005762602883041)
      ·
        refine ⟨10610346767254321952162281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14147129023005762602883041 10610346767254321952162281)
        ·
          refine ⟨7957760075440741464121711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10610346767254321952162281 7957760075440741464121711)
          ·
            refine ⟨11936640113161112196182567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7957760075440741464121711 11936640113161112196182567)
            ·
              refine ⟨17904960169741668294273851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11936640113161112196182567 17904960169741668294273851)
              ·
                refine ⟨26857440254612502441410777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17904960169741668294273851 26857440254612502441410777)
                ·
                  refine ⟨20143080190959376831058083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26857440254612502441410777 20143080190959376831058083)
                  ·
                    refine ⟨30214620286439065246587125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20143080190959376831058083 30214620286439065246587125)
                    ·
                      refine ⟨2832620651853662366867543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30214620286439065246587125 2832620651853662366867543)
                      ·
                        rfl

theorem cell23_5516509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5516509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516509 prefixEnd_5516509 := by exact prefixLift 5516509
  have htrace : WordTrace (prefixWord ++ tailWord_5516509) baseStart_5516509 baseEnd_5516509 := by
    simpa [prefixWord, tailWord_5516509, baseEnd_5516509] using wordTrace_append hprefix tailTrace_5516509
  have hstable : (prefixWord ++ tailWord_5516509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516509).length < 2 ^ (prefixWord ++ tailWord_5516509).sum := by decide
  have hdescent : baseEnd_5516509 < baseStart_5516509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516535 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_5516535 : Nat := 118140960795 + 5516535 * 2 ^ 59
def prefixEnd_5516535 : Nat := 4983230072969 + 3 ^ 40 * 5516535 * 2
def baseEnd_5516535 : Nat := 2832634002350679265142423

theorem tailTrace_5516535 : CollatzResearch.WordTrace tailWord_5516535 prefixEnd_5516535 2832634002350679265142423 := by
  unfold tailWord_5516535
  simp only [CollatzResearch.WordTrace]
  refine ⟨201204561069543319014783059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134136374046362212676522039 201204561069543319014783059)
  ·
    refine ⟨301806841604314978522174589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201204561069543319014783059 301806841604314978522174589)
    ·
      refine ⟨113177565601618116945815471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301806841604314978522174589 113177565601618116945815471)
      ·
        refine ⟨169766348402427175418723207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113177565601618116945815471 169766348402427175418723207)
        ·
          refine ⟨254649522603640763128084811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169766348402427175418723207 254649522603640763128084811)
          ·
            refine ⟨381974283905461144692127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254649522603640763128084811 381974283905461144692127217)
            ·
              refine ⟨286480712929095858519095413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381974283905461144692127217 286480712929095858519095413)
              ·
                refine ⟨26857566837102736736165195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286480712929095858519095413 26857566837102736736165195)
                ·
                  refine ⟨40286350255654105104247793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26857566837102736736165195 40286350255654105104247793)
                  ·
                    refine ⟨30214762691740578828185845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40286350255654105104247793 30214762691740578828185845)
                    ·
                      refine ⟨2832634002350679265142423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30214762691740578828185845 2832634002350679265142423)
                      ·
                        rfl

theorem cell23_5516535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_5516535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516535 prefixEnd_5516535 := by exact prefixLift 5516535
  have htrace : WordTrace (prefixWord ++ tailWord_5516535) baseStart_5516535 baseEnd_5516535 := by
    simpa [prefixWord, tailWord_5516535, baseEnd_5516535] using wordTrace_append hprefix tailTrace_5516535
  have hstable : (prefixWord ++ tailWord_5516535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516535).length < 2 ^ (prefixWord ++ tailWord_5516535).sum := by decide
  have hdescent : baseEnd_5516535 < baseStart_5516535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516540 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_5516540 : Nat := 118140960795 + 5516540 * 2 ^ 59
def prefixEnd_5516540 : Nat := 4983230072969 + 3 ^ 40 * 5516540 * 2
def baseEnd_5516540 : Nat := 2832636569753951745579901

theorem tailTrace_5516540 : CollatzResearch.WordTrace tailWord_5516540 prefixEnd_5516540 2832636569753951745579901 := by
  unfold tailWord_5516540
  simp only [CollatzResearch.WordTrace]
  refine ⟨100602371717262602434357537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134136495623016803245810049 100602371717262602434357537)
  ·
    refine ⟨75451778787946951825768153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100602371717262602434357537 75451778787946951825768153)
    ·
      refine ⟨56588834090960213869326115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75451778787946951825768153 56588834090960213869326115)
      ·
        refine ⟨84883251136440320803989173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56588834090960213869326115 84883251136440320803989173)
        ·
          refine ⟨7957804794041280075373985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84883251136440320803989173 7957804794041280075373985)
          ·
            refine ⟨5968353595530960056530489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957804794041280075373985 5968353595530960056530489)
            ·
              refine ⟨4476265196648220042397867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5968353595530960056530489 4476265196648220042397867)
              ·
                refine ⟨6714397794972330063596801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476265196648220042397867 6714397794972330063596801)
                ·
                  refine ⟨5035798346229247547697601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714397794972330063596801 5035798346229247547697601)
                  ·
                    refine ⟨3776848759671935660773201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035798346229247547697601 3776848759671935660773201)
                    ·
                      refine ⟨2832636569753951745579901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776848759671935660773201 2832636569753951745579901)
                      ·
                        rfl

theorem cell23_5516540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_5516540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516540 prefixEnd_5516540 := by exact prefixLift 5516540
  have htrace : WordTrace (prefixWord ++ tailWord_5516540) baseStart_5516540 baseEnd_5516540 := by
    simpa [prefixWord, tailWord_5516540, baseEnd_5516540] using wordTrace_append hprefix tailTrace_5516540
  have hstable : (prefixWord ++ tailWord_5516540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516540).length < 2 ^ (prefixWord ++ tailWord_5516540).sum := by decide
  have hdescent : baseEnd_5516540 < baseStart_5516540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516596 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5516596 : Nat := 118140960795 + 5516596 * 2 ^ 59
def prefixEnd_5516596 : Nat := 4983230072969 + 3 ^ 40 * 5516596 * 2
def baseEnd_5516596 : Nat := 2832665324670603526479643

theorem tailTrace_5516596 : CollatzResearch.WordTrace tailWord_5516596 prefixEnd_5516596 2832665324670603526479643 := by
  unfold tailWord_5516596
  simp only [CollatzResearch.WordTrace]
  refine ⟨100603392961161163216376821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134137857281548217621835761 100603392961161163216376821)
  ·
    refine ⟨9431568090108859051535327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100603392961161163216376821 9431568090108859051535327)
    ·
      refine ⟨14147352135163288577302991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9431568090108859051535327 14147352135163288577302991)
      ·
        refine ⟨21221028202744932865954487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14147352135163288577302991 21221028202744932865954487)
        ·
          refine ⟨31831542304117399298931731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221028202744932865954487 31831542304117399298931731)
          ·
            refine ⟨47747313456176098948397597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31831542304117399298931731 47747313456176098948397597)
            ·
              refine ⟨17905242546066037105649099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47747313456176098948397597 17905242546066037105649099)
              ·
                refine ⟨26857863819099055658473649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17905242546066037105649099 26857863819099055658473649)
                ·
                  refine ⟨20143397864324291743855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26857863819099055658473649 20143397864324291743855237)
                  ·
                    refine ⟨3776887099560804701972857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20143397864324291743855237 3776887099560804701972857)
                    ·
                      refine ⟨2832665324670603526479643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776887099560804701972857 2832665324670603526479643)
                      ·
                        rfl

theorem cell23_5516596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5516596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516596 prefixEnd_5516596 := by exact prefixLift 5516596
  have htrace : WordTrace (prefixWord ++ tailWord_5516596) baseStart_5516596 baseEnd_5516596 := by
    simpa [prefixWord, tailWord_5516596, baseEnd_5516596] using wordTrace_append hprefix tailTrace_5516596
  have hstable : (prefixWord ++ tailWord_5516596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516596).length < 2 ^ (prefixWord ++ tailWord_5516596).sum := by decide
  have hdescent : baseEnd_5516596 < baseStart_5516596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516602 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_5516602 : Nat := 118140960795 + 5516602 * 2 ^ 59
def prefixEnd_5516602 : Nat := 4983230072969 + 3 ^ 40 * 5516602 * 2
def baseEnd_5516602 : Nat := 314740933950503389222735

theorem tailTrace_5516602 : CollatzResearch.WordTrace tailWord_5516602 prefixEnd_5516602 314740933950503389222735 := by
  unfold tailWord_5516602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50301751190075147364368015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134138003173533726304981373 50301751190075147364368015)
  ·
    refine ⟨75452626785112721046552023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50301751190075147364368015 75452626785112721046552023)
    ·
      refine ⟨113178940177669081569828035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75452626785112721046552023 113178940177669081569828035)
      ·
        refine ⟨169768410266503622354742053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113178940177669081569828035 169768410266503622354742053)
        ·
          refine ⟨31831576924969429191514135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169768410266503622354742053 31831576924969429191514135)
          ·
            refine ⟨47747365387454143787271203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31831576924969429191514135 47747365387454143787271203)
            ·
              refine ⟨71621048081181215680906805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47747365387454143787271203 71621048081181215680906805)
              ·
                refine ⟨6714473257610738970085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71621048081181215680906805 6714473257610738970085013)
                ·
                  refine ⟨314740933950503389222735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6714473257610738970085013 314740933950503389222735)
                  ·
                    rfl

theorem cell23_5516602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_5516602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516602 prefixEnd_5516602 := by exact prefixLift 5516602
  have htrace : WordTrace (prefixWord ++ tailWord_5516602) baseStart_5516602 baseEnd_5516602 := by
    simpa [prefixWord, tailWord_5516602, baseEnd_5516602] using wordTrace_append hprefix tailTrace_5516602
  have hstable : (prefixWord ++ tailWord_5516602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516602).length < 2 ^ (prefixWord ++ tailWord_5516602).sum := by decide
  have hdescent : baseEnd_5516602 < baseStart_5516602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516639 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 4, 3, 2]
def baseStart_5516639 : Nat := 118140960795 + 5516639 * 2 ^ 59
def prefixEnd_5516639 : Nat := 4983230072969 + 3 ^ 40 * 5516639 * 2
def baseEnd_5516639 : Nat := 2832687404338746858241945

theorem tailTrace_5516639 : CollatzResearch.WordTrace tailWord_5516639 prefixEnd_5516639 2832687404338746858241945 := by
  unfold tailWord_5516639
  simp only [CollatzResearch.WordTrace]
  refine ⟨201208354261166544776568971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134138902840777696517712647 201208354261166544776568971)
  ·
    refine ⟨301812531391749817164853457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201208354261166544776568971 301812531391749817164853457)
    ·
      refine ⟨226359398543812362873640093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301812531391749817164853457 226359398543812362873640093)
      ·
        refine ⟨84884774453929636077615035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226359398543812362873640093 84884774453929636077615035)
        ·
          refine ⟨127327161680894454116422553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84884774453929636077615035 127327161680894454116422553)
          ·
            refine ⟨95495371260670840587316915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127327161680894454116422553 95495371260670840587316915)
            ·
              refine ⟨143243056891006260880975373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95495371260670840587316915 143243056891006260880975373)
              ·
                refine ⟨53716146334127347830365765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143243056891006260880975373 53716146334127347830365765)
                ·
                  refine ⟨10071777437648877718193581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53716146334127347830365765 10071777437648877718193581)
                  ·
                    refine ⟨3776916539118329144322593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10071777437648877718193581 3776916539118329144322593)
                    ·
                      refine ⟨2832687404338746858241945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776916539118329144322593 2832687404338746858241945)
                      ·
                        rfl

theorem cell23_5516639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_5516639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516639 prefixEnd_5516639 := by exact prefixLift 5516639
  have htrace : WordTrace (prefixWord ++ tailWord_5516639) baseStart_5516639 baseEnd_5516639 := by
    simpa [prefixWord, tailWord_5516639, baseEnd_5516639] using wordTrace_append hprefix tailTrace_5516639
  have hstable : (prefixWord ++ tailWord_5516639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516639).length < 2 ^ (prefixWord ++ tailWord_5516639).sum := by decide
  have hdescent : baseEnd_5516639 < baseStart_5516639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516669 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_5516669 : Nat := 118140960795 + 5516669 * 2 ^ 59
def prefixEnd_5516669 : Nat := 4983230072969 + 3 ^ 40 * 5516669 * 2
def baseEnd_5516669 : Nat := 2832702808758381740866807

theorem tailTrace_5516669 : CollatzResearch.WordTrace tailWord_5516669 prefixEnd_5516669 2832702808758381740866807 := by
  unfold tailWord_5516669
  simp only [CollatzResearch.WordTrace]
  refine ⟨201209448451057859900161061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134139632300705239933440707 201209448451057859900161061)
  ·
    refine ⟨37726771584573348731280199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201209448451057859900161061 37726771584573348731280199)
    ·
      refine ⟨56590157376860023096920299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37726771584573348731280199 56590157376860023096920299)
      ·
        refine ⟨84885236065290034645380449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56590157376860023096920299 84885236065290034645380449)
        ·
          refine ⟨63663927048967525984035337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84885236065290034645380449 63663927048967525984035337)
          ·
            refine ⟨47747945286725644488026503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63663927048967525984035337 47747945286725644488026503)
            ·
              refine ⟨71621917930088466732039755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47747945286725644488026503 71621917930088466732039755)
              ·
                refine ⟨107432876895132700098059633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71621917930088466732039755 107432876895132700098059633)
                ·
                  refine ⟨80574657671349525073544725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107432876895132700098059633 80574657671349525073544725)
                  ·
                    refine ⟨3776937078344508987822409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80574657671349525073544725 3776937078344508987822409)
                    ·
                      refine ⟨2832702808758381740866807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776937078344508987822409 2832702808758381740866807)
                      ·
                        rfl

theorem cell23_5516669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_5516669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516669 prefixEnd_5516669 := by exact prefixLift 5516669
  have htrace : WordTrace (prefixWord ++ tailWord_5516669) baseStart_5516669 baseEnd_5516669 := by
    simpa [prefixWord, tailWord_5516669, baseEnd_5516669] using wordTrace_append hprefix tailTrace_5516669
  have hstable : (prefixWord ++ tailWord_5516669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516669).length < 2 ^ (prefixWord ++ tailWord_5516669).sum := by decide
  have hdescent : baseEnd_5516669 < baseStart_5516669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516672 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_5516672 : Nat := 118140960795 + 5516672 * 2 ^ 59
def prefixEnd_5516672 : Nat := 4983230072969 + 3 ^ 40 * 5516672 * 2
def baseEnd_5516672 : Nat := 2832704349200345229129293

theorem tailTrace_5516672 : CollatzResearch.WordTrace tailWord_5516672 prefixEnd_5516672 2832704349200345229129293 := by
  unfold tailWord_5516672
  simp only [CollatzResearch.WordTrace]
  refine ⟨100604778935023495706260135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134139705246697994275013513 100604778935023495706260135)
  ·
    refine ⟨150907168402535243559390203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100604778935023495706260135 150907168402535243559390203)
    ·
      refine ⟨226360752603802865339085305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150907168402535243559390203 226360752603802865339085305)
      ·
        refine ⟨169770564452852149004313979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226360752603802865339085305 169770564452852149004313979)
        ·
          refine ⟨254655846679278223506470969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169770564452852149004313979 254655846679278223506470969)
          ·
            refine ⟨190991885009458667629853227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254655846679278223506470969 190991885009458667629853227)
            ·
              refine ⟨286487827514188001444779841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190991885009458667629853227 286487827514188001444779841)
              ·
                refine ⟨214865870635641001083584881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286487827514188001444779841 214865870635641001083584881)
                ·
                  refine ⟨161149402976730750812688661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214865870635641001083584881 161149402976730750812688661)
                  ·
                    refine ⟨7553878264534253944344781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161149402976730750812688661 7553878264534253944344781)
                    ·
                      refine ⟨2832704349200345229129293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553878264534253944344781 2832704349200345229129293)
                      ·
                        rfl

theorem cell23_5516672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_5516672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516672 prefixEnd_5516672 := by exact prefixLift 5516672
  have htrace : WordTrace (prefixWord ++ tailWord_5516672) baseStart_5516672 baseEnd_5516672 := by
    simpa [prefixWord, tailWord_5516672, baseEnd_5516672] using wordTrace_append hprefix tailTrace_5516672
  have hstable : (prefixWord ++ tailWord_5516672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516672).length < 2 ^ (prefixWord ++ tailWord_5516672).sum := by decide
  have hdescent : baseEnd_5516672 < baseStart_5516672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516679 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 4, 4]
def baseStart_5516679 : Nat := 118140960795 + 5516679 * 2 ^ 59
def prefixEnd_5516679 : Nat := 4983230072969 + 3 ^ 40 * 5516679 * 2
def baseEnd_5516679 : Nat := 944235981188308900580587

theorem tailTrace_5516679 : CollatzResearch.WordTrace tailWord_5516679 prefixEnd_5516679 944235981188308900580587 := by
  unfold tailWord_5516679
  simp only [CollatzResearch.WordTrace]
  refine ⟨201209813181021631608025091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134139875454014421072016727 201209813181021631608025091)
  ·
    refine ⟨301814719771532447412037637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201209813181021631608025091 301814719771532447412037637)
    ·
      refine ⟨56590259957162333889757057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301814719771532447412037637 56590259957162333889757057)
      ·
        refine ⟨42442694967871750417317793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56590259957162333889757057 42442694967871750417317793)
        ·
          refine ⟨31832021225903812812988345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42442694967871750417317793 31832021225903812812988345)
          ·
            refine ⟨23874015919427859609741259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31832021225903812812988345 23874015919427859609741259)
            ·
              refine ⟨35811023879141789414611889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23874015919427859609741259 35811023879141789414611889)
              ·
                refine ⟨26858267909356342060958917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35811023879141789414611889 26858267909356342060958917)
                ·
                  refine ⟨5035925233004314136429797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26858267909356342060958917 5035925233004314136429797)
                  ·
                    refine ⟨944235981188308900580587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5035925233004314136429797 944235981188308900580587)
                    ·
                      rfl

theorem cell23_5516679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_5516679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516679 prefixEnd_5516679 := by exact prefixLift 5516679
  have htrace : WordTrace (prefixWord ++ tailWord_5516679) baseStart_5516679 baseEnd_5516679 := by
    simpa [prefixWord, tailWord_5516679, baseEnd_5516679] using wordTrace_append hprefix tailTrace_5516679
  have hstable : (prefixWord ++ tailWord_5516679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516679).length < 2 ^ (prefixWord ++ tailWord_5516679).sum := by decide
  have hdescent : baseEnd_5516679 < baseStart_5516679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516680 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5516680 : Nat := 118140960795 + 5516680 * 2 ^ 59
def prefixEnd_5516680 : Nat := 4983230072969 + 3 ^ 40 * 5516680 * 2
def baseEnd_5516680 : Nat := 2832708457045581197829257

theorem tailTrace_5516680 : CollatzResearch.WordTrace tailWord_5516680 prefixEnd_5516680 2832708457045581197829257 := by
  unfold tailWord_5516680
  simp only [CollatzResearch.WordTrace]
  refine ⟨100604924827009004389405747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134139899769345339185874329 100604924827009004389405747)
  ·
    refine ⟨150907387240513506584108621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100604924827009004389405747 150907387240513506584108621)
    ·
      refine ⟨56590270215192564969040733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150907387240513506584108621 56590270215192564969040733)
      ·
        refine ⟨21221351330697211863390275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56590270215192564969040733 21221351330697211863390275)
        ·
          refine ⟨31832026996045817795085413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221351330697211863390275 31832026996045817795085413)
          ·
            refine ⟨5968505061758590836578515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31832026996045817795085413 5968505061758590836578515)
            ·
              refine ⟨8952757592637886254867773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5968505061758590836578515 8952757592637886254867773)
              ·
                refine ⟨3357284097239207345575415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8952757592637886254867773 3357284097239207345575415)
                ·
                  refine ⟨5035926145858811018363123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357284097239207345575415 5035926145858811018363123)
                  ·
                    refine ⟨7553889218788216527544685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5035926145858811018363123 7553889218788216527544685)
                    ·
                      refine ⟨2832708457045581197829257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553889218788216527544685 2832708457045581197829257)
                      ·
                        rfl

theorem cell23_5516680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5516680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516680 prefixEnd_5516680 := by exact prefixLift 5516680
  have htrace : WordTrace (prefixWord ++ tailWord_5516680) baseStart_5516680 baseEnd_5516680 := by
    simpa [prefixWord, tailWord_5516680, baseEnd_5516680] using wordTrace_append hprefix tailTrace_5516680
  have hstable : (prefixWord ++ tailWord_5516680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516680).length < 2 ^ (prefixWord ++ tailWord_5516680).sum := by decide
  have hdescent : baseEnd_5516680 < baseStart_5516680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516690 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5516690 : Nat := 118140960795 + 5516690 * 2 ^ 59
def prefixEnd_5516690 : Nat := 4983230072969 + 3 ^ 40 * 5516690 * 2
def baseEnd_5516690 : Nat := 2832713591852126158704211

theorem tailTrace_5516690 : CollatzResearch.WordTrace tailWord_5516690 prefixEnd_5516690 2832713591852126158704211 := by
  unfold tailWord_5516690
  simp only [CollatzResearch.WordTrace]
  refine ⟨50302553595995445121668881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134140142922654520324450349 50302553595995445121668881)
  ·
    refine ⟨37726915196996583841251661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50302553595995445121668881 37726915196996583841251661)
    ·
      refine ⟨14147593198873718940469373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37726915196996583841251661 14147593198873718940469373)
      ·
        refine ⟨5305347449577644602676015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14147593198873718940469373 5305347449577644602676015)
        ·
          refine ⟨7958021174366466904014023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5305347449577644602676015 7958021174366466904014023)
          ·
            refine ⟨11937031761549700356021035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958021174366466904014023 11937031761549700356021035)
            ·
              refine ⟨17905547642324550534031553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11937031761549700356021035 17905547642324550534031553)
              ·
                refine ⟨13429160731743412900523665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17905547642324550534031553 13429160731743412900523665)
                ·
                  refine ⟨10071870548807559675392749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13429160731743412900523665 10071870548807559675392749)
                  ·
                    refine ⟨3776951455802834878272281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10071870548807559675392749 3776951455802834878272281)
                    ·
                      refine ⟨2832713591852126158704211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776951455802834878272281 2832713591852126158704211)
                      ·
                        rfl

theorem cell23_5516690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5516690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516690 prefixEnd_5516690 := by exact prefixLift 5516690
  have htrace : WordTrace (prefixWord ++ tailWord_5516690) baseStart_5516690 baseEnd_5516690 := by
    simpa [prefixWord, tailWord_5516690, baseEnd_5516690] using wordTrace_append hprefix tailTrace_5516690
  have hstable : (prefixWord ++ tailWord_5516690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516690).length < 2 ^ (prefixWord ++ tailWord_5516690).sum := by decide
  have hdescent : baseEnd_5516690 < baseStart_5516690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516703 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5516703 : Nat := 118140960795 + 5516703 * 2 ^ 59
def prefixEnd_5516703 : Nat := 4983230072969 + 3 ^ 40 * 5516703 * 2
def baseEnd_5516703 : Nat := 2832720267100634607841651

theorem tailTrace_5516703 : CollatzResearch.WordTrace tailWord_5516703 prefixEnd_5516703 2832720267100634607841651 := by
  unfold tailWord_5516703
  simp only [CollatzResearch.WordTrace]
  refine ⟨201210688532934683706898763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134140459021956455804599175 201210688532934683706898763)
  ·
    refine ⟨301816032799402025560348145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201210688532934683706898763 301816032799402025560348145)
    ·
      refine ⟨226362024599551519170261109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301816032799402025560348145 226362024599551519170261109)
      ·
        refine ⟨21221439806207954922211979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226362024599551519170261109 21221439806207954922211979)
        ·
          refine ⟨31832159709311932383317969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221439806207954922211979 31832159709311932383317969)
          ·
            refine ⟨23874119781983949287488477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31832159709311932383317969 23874119781983949287488477)
            ·
              refine ⟨8952794918243980982808179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23874119781983949287488477 8952794918243980982808179)
              ·
                refine ⟨13429192377365971474212269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8952794918243980982808179 13429192377365971474212269)
                ·
                  refine ⟨5035947141512239302829601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13429192377365971474212269 5035947141512239302829601)
                  ·
                    refine ⟨3776960356134179477122201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5035947141512239302829601 3776960356134179477122201)
                    ·
                      refine ⟨2832720267100634607841651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3776960356134179477122201 2832720267100634607841651)
                      ·
                        rfl

theorem cell23_5516703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5516703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516703 prefixEnd_5516703 := by exact prefixLift 5516703
  have htrace : WordTrace (prefixWord ++ tailWord_5516703) baseStart_5516703 baseEnd_5516703 := by
    simpa [prefixWord, tailWord_5516703, baseEnd_5516703] using wordTrace_append hprefix tailTrace_5516703
  have hstable : (prefixWord ++ tailWord_5516703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516703).length < 2 ^ (prefixWord ++ tailWord_5516703).sum := by decide
  have hdescent : baseEnd_5516703 < baseStart_5516703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516722 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_5516722 : Nat := 118140960795 + 5516722 * 2 ^ 59
def prefixEnd_5516722 : Nat := 4983230072969 + 3 ^ 40 * 5516722 * 2
def baseEnd_5516722 : Nat := 944243341077690011168021

theorem tailTrace_5516722 : CollatzResearch.WordTrace tailWord_5516722 prefixEnd_5516722 944243341077690011168021 := by
  unfold tailWord_5516722
  simp only [CollatzResearch.WordTrace]
  refine ⟨50302845379966462487960105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134140921013243899967893613 50302845379966462487960105)
  ·
    refine ⟨37727134034974846865970079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50302845379966462487960105 37727134034974846865970079)
    ·
      refine ⟨56590701052462270298955119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37727134034974846865970079 56590701052462270298955119)
      ·
        refine ⟨84886051578693405448432679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56590701052462270298955119 84886051578693405448432679)
        ·
          refine ⟨127329077368040108172649019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84886051578693405448432679 127329077368040108172649019)
          ·
            refine ⟨190993616052060162258973529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127329077368040108172649019 190993616052060162258973529)
            ·
              refine ⟨143245212039045121694230147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190993616052060162258973529 143245212039045121694230147)
              ·
                refine ⟨214867818058567682541345221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143245212039045121694230147 214867818058567682541345221)
                ·
                  refine ⟨40287715885981440476502229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214867818058567682541345221 40287715885981440476502229)
                  ·
                    refine ⟨944243341077690011168021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40287715885981440476502229 944243341077690011168021)
                    ·
                      rfl

theorem cell23_5516722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_5516722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516722 prefixEnd_5516722 := by exact prefixLift 5516722
  have htrace : WordTrace (prefixWord ++ tailWord_5516722) baseStart_5516722 baseEnd_5516722 := by
    simpa [prefixWord, tailWord_5516722, baseEnd_5516722] using wordTrace_append hprefix tailTrace_5516722
  have hstable : (prefixWord ++ tailWord_5516722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516722).length < 2 ^ (prefixWord ++ tailWord_5516722).sum := by decide
  have hdescent : baseEnd_5516722 < baseStart_5516722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516740 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5516740 : Nat := 118140960795 + 5516740 * 2 ^ 59
def prefixEnd_5516740 : Nat := 4983230072969 + 3 ^ 40 * 5516740 * 2
def baseEnd_5516740 : Nat := 2832739265884850963078981

theorem tailTrace_5516740 : CollatzResearch.WordTrace tailWord_5516740 prefixEnd_5516740 2832739265884850963078981 := by
  unfold tailWord_5516740
  simp only [CollatzResearch.WordTrace]
  refine ⟨100606019016900319512997837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134141358689200426017330449 100606019016900319512997837)
  ·
    refine ⟨37727257131337619817374189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100606019016900319512997837 37727257131337619817374189)
    ·
      refine ⟨14147721424251607431515321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37727257131337619817374189 14147721424251607431515321)
      ·
        refine ⟨10610791068188705573636491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14147721424251607431515321 10610791068188705573636491)
        ·
          refine ⟨15916186602283058360454737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610791068188705573636491 15916186602283058360454737)
          ·
            refine ⟨11937139951712293770341053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15916186602283058360454737 11937139951712293770341053)
            ·
              refine ⟨4476427481892110163877895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11937139951712293770341053 4476427481892110163877895)
              ·
                refine ⟨6714641222838165245816843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476427481892110163877895 6714641222838165245816843)
                ·
                  refine ⟨10071961834257247868725265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714641222838165245816843 10071961834257247868725265)
                  ·
                    refine ⟨7553971375692935901543949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10071961834257247868725265 7553971375692935901543949)
                    ·
                      refine ⟨2832739265884850963078981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7553971375692935901543949 2832739265884850963078981)
                      ·
                        rfl

theorem cell23_5516740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5516740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516740 prefixEnd_5516740 := by exact prefixLift 5516740
  have htrace : WordTrace (prefixWord ++ tailWord_5516740) baseStart_5516740 baseEnd_5516740 := by
    simpa [prefixWord, tailWord_5516740, baseEnd_5516740] using wordTrace_append hprefix tailTrace_5516740
  have hstable : (prefixWord ++ tailWord_5516740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516740).length < 2 ^ (prefixWord ++ tailWord_5516740).sum := by decide
  have hdescent : baseEnd_5516740 < baseStart_5516740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516752 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_5516752 : Nat := 118140960795 + 5516752 * 2 ^ 59
def prefixEnd_5516752 : Nat := 4983230072969 + 3 ^ 40 * 5516752 * 2
def baseEnd_5516752 : Nat := 944248475884234972042975

theorem tailTrace_5516752 : CollatzResearch.WordTrace tailWord_5516752 prefixEnd_5516752 944248475884234972042975 := by
  unfold tailWord_5516752
  simp only [CollatzResearch.WordTrace]
  refine ⟨100606237854878582537716255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134141650473171443383621673 100606237854878582537716255)
  ·
    refine ⟨150909356782317873806574383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100606237854878582537716255 150909356782317873806574383)
    ·
      refine ⟨226364035173476810709861575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150909356782317873806574383 226364035173476810709861575)
      ·
        refine ⟨339546052760215216064792363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226364035173476810709861575 339546052760215216064792363)
        ·
          refine ⟨509319079140322824097188545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339546052760215216064792363 509319079140322824097188545)
          ·
            refine ⟨381989309355242118072891409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509319079140322824097188545 381989309355242118072891409)
            ·
              refine ⟨286491982016431588554668557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381989309355242118072891409 286491982016431588554668557)
              ·
                refine ⟨107434493256161845708000709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286491982016431588554668557 107434493256161845708000709)
                ·
                  refine ⟨20143967485530346070250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107434493256161845708000709 20143967485530346070250133)
                  ·
                    refine ⟨944248475884234972042975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20143967485530346070250133 944248475884234972042975)
                    ·
                      rfl

theorem cell23_5516752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_5516752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516752 prefixEnd_5516752 := by exact prefixLift 5516752
  have htrace : WordTrace (prefixWord ++ tailWord_5516752) baseStart_5516752 baseEnd_5516752 := by
    simpa [prefixWord, tailWord_5516752, baseEnd_5516752] using wordTrace_append hprefix tailTrace_5516752
  have hstable : (prefixWord ++ tailWord_5516752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516752).length < 2 ^ (prefixWord ++ tailWord_5516752).sum := by decide
  have hdescent : baseEnd_5516752 < baseStart_5516752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516769 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_5516769 : Nat := 118140960795 + 5516769 * 2 ^ 59
def prefixEnd_5516769 : Nat := 4983230072969 + 3 ^ 40 * 5516769 * 2
def baseEnd_5516769 : Nat := 944251385607943783205449

theorem tailTrace_5516769 : CollatzResearch.WordTrace tailWord_5516769 prefixEnd_5516769 944251385607943783205449 := by
  unfold tailWord_5516769
  simp only [CollatzResearch.WordTrace]
  refine ⟨201213095750695576978801361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134142063833797051319200907 201213095750695576978801361)
  ·
    refine ⟨150909821813021682734101021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201213095750695576978801361 150909821813021682734101021)
    ·
      refine ⟨56591183179883131025287883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150909821813021682734101021 56591183179883131025287883)
      ·
        refine ⟨84886774769824696537931825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56591183179883131025287883 84886774769824696537931825)
        ·
          refine ⟨63665081077368522403448869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84886774769824696537931825 63665081077368522403448869)
          ·
            refine ⟨11937202702006597950646663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63665081077368522403448869 11937202702006597950646663)
            ·
              refine ⟨17905804053009896925969995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11937202702006597950646663 17905804053009896925969995)
              ·
                refine ⟨26858706079514845388954993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17905804053009896925969995 26858706079514845388954993)
                ·
                  refine ⟨20144029559636134041716245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26858706079514845388954993 20144029559636134041716245)
                  ·
                    refine ⟨944251385607943783205449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20144029559636134041716245 944251385607943783205449)
                    ·
                      rfl

theorem cell23_5516769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_5516769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516769 prefixEnd_5516769 := by exact prefixLift 5516769
  have htrace : WordTrace (prefixWord ++ tailWord_5516769) baseStart_5516769 baseEnd_5516769 := by
    simpa [prefixWord, tailWord_5516769, baseEnd_5516769] using wordTrace_append hprefix tailTrace_5516769
  have hstable : (prefixWord ++ tailWord_5516769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516769).length < 2 ^ (prefixWord ++ tailWord_5516769).sum := by decide
  have hdescent : baseEnd_5516769 < baseStart_5516769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516809 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_5516809 : Nat := 118140960795 + 5516809 * 2 ^ 59
def prefixEnd_5516809 : Nat := 4983230072969 + 3 ^ 40 * 5516809 * 2
def baseEnd_5516809 : Nat := 2832774696050011193116163

theorem tailTrace_5516809 : CollatzResearch.WordTrace tailWord_5516809 prefixEnd_5516809 2832774696050011193116163 := by
  unfold tailWord_5516809
  simp only [CollatzResearch.WordTrace]
  refine ⟨201214554670550663810257481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134143036447033775873504987 201214554670550663810257481)
  ·
    refine ⟨150910916002912997857693111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201214554670550663810257481 150910916002912997857693111)
    ·
      refine ⟨226366374004369496786539667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150910916002912997857693111 226366374004369496786539667)
      ·
        refine ⟨339549561006554245179809501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226366374004369496786539667 339549561006554245179809501)
        ·
          refine ⟨127331085377457841942428563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339549561006554245179809501 127331085377457841942428563)
          ·
            refine ⟨190996628066186762913642845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127331085377457841942428563 190996628066186762913642845)
            ·
              refine ⟨71623735524820036092616067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190996628066186762913642845 71623735524820036092616067)
              ·
                refine ⟨107435603287230054138924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71623735524820036092616067 107435603287230054138924101)
                ·
                  refine ⟨20144175616355635151048269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107435603287230054138924101 20144175616355635151048269)
                  ·
                    refine ⟨7554065856133363181643101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20144175616355635151048269 7554065856133363181643101)
                    ·
                      refine ⟨2832774696050011193116163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554065856133363181643101 2832774696050011193116163)
                      ·
                        rfl

theorem cell23_5516809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_5516809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516809 prefixEnd_5516809 := by exact prefixLift 5516809
  have htrace : WordTrace (prefixWord ++ tailWord_5516809) baseStart_5516809 baseEnd_5516809 := by
    simpa [prefixWord, tailWord_5516809, baseEnd_5516809] using wordTrace_append hprefix tailTrace_5516809
  have hstable : (prefixWord ++ tailWord_5516809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516809).length < 2 ^ (prefixWord ++ tailWord_5516809).sum := by decide
  have hdescent : baseEnd_5516809 < baseStart_5516809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516810 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_5516810 : Nat := 118140960795 + 5516810 * 2 ^ 59
def prefixEnd_5516810 : Nat := 4983230072969 + 3 ^ 40 * 5516810 * 2
def baseEnd_5516810 : Nat := 2832775209530665689203659

theorem tailTrace_5516810 : CollatzResearch.WordTrace tailWord_5516810 prefixEnd_5516810 2832775209530665689203659 := by
  unfold tailWord_5516810
  simp only [CollatzResearch.WordTrace]
  refine ⟨50303647785886760245260971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134143060762364693987362589 50303647785886760245260971)
  ·
    refine ⟨75455471678830140367891457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50303647785886760245260971 75455471678830140367891457)
    ·
      refine ⟨56591603759122605275918593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75455471678830140367891457 56591603759122605275918593)
      ·
        refine ⟨42443702819341953956938945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56591603759122605275918593 42443702819341953956938945)
        ·
          refine ⟨31832777114506465467704209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42443702819341953956938945 31832777114506465467704209)
          ·
            refine ⟨23874582835879849100778157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31832777114506465467704209 23874582835879849100778157)
            ·
              refine ⟨8952968563454943412791809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23874582835879849100778157 8952968563454943412791809)
              ·
                refine ⟨6714726422591207559593857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952968563454943412791809 6714726422591207559593857)
                ·
                  refine ⟨5036044816943405669695393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714726422591207559593857 5036044816943405669695393)
                  ·
                    refine ⟨3777033612707554252271545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036044816943405669695393 3777033612707554252271545)
                    ·
                      refine ⟨2832775209530665689203659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777033612707554252271545 2832775209530665689203659)
                      ·
                        rfl

theorem cell23_5516810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_5516810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516810 prefixEnd_5516810 := by exact prefixLift 5516810
  have htrace : WordTrace (prefixWord ++ tailWord_5516810) baseStart_5516810 baseEnd_5516810 := by
    simpa [prefixWord, tailWord_5516810, baseEnd_5516810] using wordTrace_append hprefix tailTrace_5516810
  have hstable : (prefixWord ++ tailWord_5516810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516810).length < 2 ^ (prefixWord ++ tailWord_5516810).sum := by decide
  have hdescent : baseEnd_5516810 < baseStart_5516810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516829 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_5516829 : Nat := 118140960795 + 5516829 * 2 ^ 59
def prefixEnd_5516829 : Nat := 4983230072969 + 3 ^ 40 * 5516829 * 2
def baseEnd_5516829 : Nat := 944261655221033704955357

theorem tailTrace_5516829 : CollatzResearch.WordTrace tailWord_5516829 prefixEnd_5516829 944261655221033704955357 := by
  unfold tailWord_5516829
  simp only [CollatzResearch.WordTrace]
  refine ⟨201215284130478207225985541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134143522753652138150657027 201215284130478207225985541)
  ·
    refine ⟨37727865774464663854872289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201215284130478207225985541 37727865774464663854872289)
    ·
      refine ⟨28295899330848497891154217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37727865774464663854872289 28295899330848497891154217)
      ·
        refine ⟨21221924498136373418365663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28295899330848497891154217 21221924498136373418365663)
        ·
          refine ⟨31832886747204560127548495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221924498136373418365663 31832886747204560127548495)
          ·
            refine ⟨47749330120806840191322743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31832886747204560127548495 47749330120806840191322743)
            ·
              refine ⟨71623995181210260286984115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47749330120806840191322743 71623995181210260286984115)
              ·
                refine ⟨107435992771815390430476173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71623995181210260286984115 107435992771815390430476173)
                ·
                  refine ⟨40288497289430771411428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107435992771815390430476173 40288497289430771411428565)
                  ·
                    refine ⟨944261655221033704955357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40288497289430771411428565 944261655221033704955357)
                    ·
                      rfl

theorem cell23_5516829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_5516829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516829 prefixEnd_5516829 := by exact prefixLift 5516829
  have htrace : WordTrace (prefixWord ++ tailWord_5516829) baseStart_5516829 baseEnd_5516829 := by
    simpa [prefixWord, tailWord_5516829, baseEnd_5516829] using wordTrace_append hprefix tailTrace_5516829
  have hstable : (prefixWord ++ tailWord_5516829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516829).length < 2 ^ (prefixWord ++ tailWord_5516829).sum := by decide
  have hdescent : baseEnd_5516829 < baseStart_5516829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516846 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5516846 : Nat := 118140960795 + 5516846 * 2 ^ 59
def prefixEnd_5516846 : Nat := 4983230072969 + 3 ^ 40 * 5516846 * 2
def baseEnd_5516846 : Nat := 944264564944742516117831

theorem tailTrace_5516846 : CollatzResearch.WordTrace tailWord_5516846 prefixEnd_5516846 944264564944742516117831 := by
  unfold tailWord_5516846
  simp only [CollatzResearch.WordTrace]
  refine ⟨25151988021427077391169299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134143936114277746086236261 25151988021427077391169299)
  ·
    refine ⟨37727982032140616086753949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25151988021427077391169299 37727982032140616086753949)
    ·
      refine ⟨14147993262052731032532731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37727982032140616086753949 14147993262052731032532731)
      ·
        refine ⟨21221989893079096548799097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14147993262052731032532731 21221989893079096548799097)
        ·
          refine ⟨15916492419809322411599323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21221989893079096548799097 15916492419809322411599323)
          ·
            refine ⟨23874738629713983617398985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15916492419809322411599323 23874738629713983617398985)
            ·
              refine ⟨17906053972285487713049239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23874738629713983617398985 17906053972285487713049239)
              ·
                refine ⟨26859080958428231569573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17906053972285487713049239 26859080958428231569573859)
                ·
                  refine ⟨40288621437642347354360789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26859080958428231569573859 40288621437642347354360789)
                  ·
                    refine ⟨944264564944742516117831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40288621437642347354360789 944264564944742516117831)
                    ·
                      rfl

theorem cell23_5516846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5516846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516846 prefixEnd_5516846 := by exact prefixLift 5516846
  have htrace : WordTrace (prefixWord ++ tailWord_5516846) baseStart_5516846 baseEnd_5516846 := by
    simpa [prefixWord, tailWord_5516846, baseEnd_5516846] using wordTrace_append hprefix tailTrace_5516846
  have hstable : (prefixWord ++ tailWord_5516846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516846).length < 2 ^ (prefixWord ++ tailWord_5516846).sum := by decide
  have hdescent : baseEnd_5516846 < baseStart_5516846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516933 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_5516933 : Nat := 118140960795 + 5516933 * 2 ^ 59
def prefixEnd_5516933 : Nat := 4983230072969 + 3 ^ 40 * 5516933 * 2
def baseEnd_5516933 : Nat := 2832838367651168707965593

theorem tailTrace_5516933 : CollatzResearch.WordTrace tailWord_5516933 prefixEnd_5516933 2832838367651168707965593 := by
  unfold tailWord_5516933
  simp only [CollatzResearch.WordTrace]
  refine ⟨201219077322101432987771453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134146051548067621991847635 201219077322101432987771453)
  ·
    refine ⟨75457153995788037370414295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201219077322101432987771453 75457153995788037370414295)
    ·
      refine ⟨113185730993682056055621443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75457153995788037370414295 113185730993682056055621443)
      ·
        refine ⟨169778596490523084083432165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113185730993682056055621443 169778596490523084083432165)
        ·
          refine ⟨31833486841973078265643531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169778596490523084083432165 31833486841973078265643531)
          ·
            refine ⟨47750230262959617398465297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31833486841973078265643531 47750230262959617398465297)
            ·
              refine ⟨35812672697219713048848973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47750230262959617398465297 35812672697219713048848973)
              ·
                refine ⟨13429752261457392393318365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35812672697219713048848973 13429752261457392393318365)
                ·
                  refine ⟨5036157098046522147494387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13429752261457392393318365 5036157098046522147494387)
                  ·
                    refine ⟨7554235647069783221241581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036157098046522147494387 7554235647069783221241581)
                    ·
                      refine ⟨2832838367651168707965593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554235647069783221241581 2832838367651168707965593)
                      ·
                        rfl

theorem cell23_5516933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_5516933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516933 prefixEnd_5516933 := by exact prefixLift 5516933
  have htrace : WordTrace (prefixWord ++ tailWord_5516933) baseStart_5516933 baseEnd_5516933 := by
    simpa [prefixWord, tailWord_5516933, baseEnd_5516933] using wordTrace_append hprefix tailTrace_5516933
  have hstable : (prefixWord ++ tailWord_5516933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516933).length < 2 ^ (prefixWord ++ tailWord_5516933).sum := by decide
  have hdescent : baseEnd_5516933 < baseStart_5516933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516960 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2]
def baseStart_5516960 : Nat := 118140960795 + 5516960 * 2 ^ 59
def prefixEnd_5516960 : Nat := 4983230072969 + 3 ^ 40 * 5516960 * 2
def baseEnd_5516960 : Nat := 2832852231628840102327969

theorem tailTrace_5516960 : CollatzResearch.WordTrace tailWord_5516960 prefixEnd_5516960 2832852231628840102327969 := by
  unfold tailWord_5516960
  simp only [CollatzResearch.WordTrace]
  refine ⟨100610031046501808299502167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134146708062002411066002889 100610031046501808299502167)
  ·
    refine ⟨150915046569752712449253251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100610031046501808299502167 150915046569752712449253251)
    ·
      refine ⟨226372569854629068673879877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150915046569752712449253251 226372569854629068673879877)
      ·
        refine ⟨42444856847742950376352477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226372569854629068673879877 42444856847742950376352477)
        ·
          refine ⟨15916821317903606391132179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42444856847742950376352477 15916821317903606391132179)
          ·
            refine ⟨23875231976855409586698269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15916821317903606391132179 23875231976855409586698269)
            ·
              refine ⟨8953211991320778595011851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23875231976855409586698269 8953211991320778595011851)
              ·
                refine ⟨13429817986981167892517777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8953211991320778595011851 13429817986981167892517777)
                ·
                  refine ⟨10072363490235875919388333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13429817986981167892517777 10072363490235875919388333)
                  ·
                    refine ⟨3777136308838453469770625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10072363490235875919388333 3777136308838453469770625)
                    ·
                      refine ⟨2832852231628840102327969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777136308838453469770625 2832852231628840102327969)
                      ·
                        rfl

theorem cell23_5516960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_5516960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516960 prefixEnd_5516960 := by exact prefixLift 5516960
  have htrace : WordTrace (prefixWord ++ tailWord_5516960) baseStart_5516960 baseEnd_5516960 := by
    simpa [prefixWord, tailWord_5516960, baseEnd_5516960] using wordTrace_append hprefix tailTrace_5516960
  have hstable : (prefixWord ++ tailWord_5516960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516960).length < 2 ^ (prefixWord ++ tailWord_5516960).sum := by decide
  have hdescent : baseEnd_5516960 < baseStart_5516960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516979 : List Nat := [1, 1, 1, 2, 3, 3, 12]
def baseStart_5516979 : Nat := 118140960795 + 5516979 * 2 ^ 59
def prefixEnd_5516979 : Nat := 4983230072969 + 3 ^ 40 * 5516979 * 2
def baseEnd_5516979 : Nat := 34973604787176241086301

theorem tailTrace_5516979 : CollatzResearch.WordTrace tailWord_5516979 prefixEnd_5516979 34973604787176241086301 := by
  unfold tailWord_5516979
  simp only [CollatzResearch.WordTrace]
  refine ⟨201220755079934782843945991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134147170053289855229297327 201220755079934782843945991)
  ·
    refine ⟨301831132619902174265918987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201220755079934782843945991 301831132619902174265918987)
    ·
      refine ⟨452746698929853261398878481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301831132619902174265918987 452746698929853261398878481)
      ·
        refine ⟨339560024197389946049158861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452746698929853261398878481 339560024197389946049158861)
        ·
          refine ⟨127335009074021229768434573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339560024197389946049158861 127335009074021229768434573)
          ·
            refine ⟨47750628402757961163162965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127335009074021229768434573 47750628402757961163162965)
            ·
              refine ⟨34973604787176241086301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47750628402757961163162965 34973604787176241086301)
              ·
                rfl

theorem cell23_5516979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 12].length) (baseStart_5516979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516979 prefixEnd_5516979 := by exact prefixLift 5516979
  have htrace : WordTrace (prefixWord ++ tailWord_5516979) baseStart_5516979 baseEnd_5516979 := by
    simpa [prefixWord, tailWord_5516979, baseEnd_5516979] using wordTrace_append hprefix tailTrace_5516979
  have hstable : (prefixWord ++ tailWord_5516979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516979).length < 2 ^ (prefixWord ++ tailWord_5516979).sum := by decide
  have hdescent : baseEnd_5516979 < baseStart_5516979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516983 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 4, 4]
def baseStart_5516983 : Nat := 118140960795 + 5516983 * 2 ^ 59
def prefixEnd_5516983 : Nat := 4983230072969 + 3 ^ 40 * 5516983 * 2
def baseEnd_5516983 : Nat := 944288013894631170780121

theorem tailTrace_5516983 : CollatzResearch.WordTrace tailWord_5516983 prefixEnd_5516983 944288013894631170780121 := by
  unfold tailWord_5516983
  simp only [CollatzResearch.WordTrace]
  refine ⟨201220900971920291527091603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134147267314613527684727735 201220900971920291527091603)
  ·
    refine ⟨301831351457880437290637405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201220900971920291527091603 301831351457880437290637405)
    ·
      refine ⟨113186756796705163983989027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301831351457880437290637405 113186756796705163983989027)
      ·
        refine ⟨169780135195057745975983541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113186756796705163983989027 169780135195057745975983541)
        ·
          refine ⟨15916887674536663685248457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169780135195057745975983541 15916887674536663685248457)
          ·
            refine ⟨11937665755902497763936343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15916887674536663685248457 11937665755902497763936343)
            ·
              refine ⟨17906498633853746645904515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11937665755902497763936343 17906498633853746645904515)
              ·
                refine ⟨26859747950780619968856773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17906498633853746645904515 26859747950780619968856773)
                ·
                  refine ⟨5036202740771366244160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26859747950780619968856773 5036202740771366244160645)
                  ·
                    refine ⟨944288013894631170780121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036202740771366244160645 944288013894631170780121)
                    ·
                      rfl

theorem cell23_5516983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_5516983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516983 prefixEnd_5516983 := by exact prefixLift 5516983
  have htrace : WordTrace (prefixWord ++ tailWord_5516983) baseStart_5516983 baseEnd_5516983 := by
    simpa [prefixWord, tailWord_5516983, baseEnd_5516983] using wordTrace_append hprefix tailTrace_5516983
  have hstable : (prefixWord ++ tailWord_5516983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516983).length < 2 ^ (prefixWord ++ tailWord_5516983).sum := by decide
  have hdescent : baseEnd_5516983 < baseStart_5516983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5516996 : List Nat := [2, 3, 3, 1, 1, 1, 2, 10]
def baseStart_5516996 : Nat := 118140960795 + 5516996 * 2 ^ 59
def prefixEnd_5516996 : Nat := 4983230072969 + 3 ^ 40 * 5516996 * 2
def baseEnd_5516996 : Nat := 104921137664163035610289

theorem tailTrace_5516996 : CollatzResearch.WordTrace tailWord_5516996 prefixEnd_5516996 104921137664163035610289 := by
  unfold tailWord_5516996
  simp only [CollatzResearch.WordTrace]
  refine ⟨100610687560436597373657421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134147583413915463164876561 100610687560436597373657421)
  ·
    refine ⟨37729007835163724015121533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100610687560436597373657421 37729007835163724015121533)
    ·
      refine ⟨14148377938186396505670575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37729007835163724015121533 14148377938186396505670575)
      ·
        refine ⟨21222566907279594758505863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14148377938186396505670575 21222566907279594758505863)
        ·
          refine ⟨31833850360919392137758795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21222566907279594758505863 31833850360919392137758795)
          ·
            refine ⟨47750775541379088206638193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31833850360919392137758795 47750775541379088206638193)
            ·
              refine ⟨35813081656034316154978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47750775541379088206638193 35813081656034316154978645)
              ·
                refine ⟨104921137664163035610289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35813081656034316154978645 104921137664163035610289)
                ·
                  rfl

theorem cell23_5516996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 10].length) (baseStart_5516996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5516996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5516996 prefixEnd_5516996 := by exact prefixLift 5516996
  have htrace : WordTrace (prefixWord ++ tailWord_5516996) baseStart_5516996 baseEnd_5516996 := by
    simpa [prefixWord, tailWord_5516996, baseEnd_5516996] using wordTrace_append hprefix tailTrace_5516996
  have hstable : (prefixWord ++ tailWord_5516996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5516996).length < 2 ^ (prefixWord ++ tailWord_5516996).sum := by decide
  have hdescent : baseEnd_5516996 < baseStart_5516996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5516996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517000 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 2, 4]
def baseStart_5517000 : Nat := 118140960795 + 5517000 * 2 ^ 59
def prefixEnd_5517000 : Nat := 4983230072969 + 3 ^ 40 * 5517000 * 2
def baseEnd_5517000 : Nat := 944290923618339981942595

theorem tailTrace_5517000 : CollatzResearch.WordTrace tailWord_5517000 prefixEnd_5517000 944290923618339981942595 := by
  unfold tailWord_5517000
  simp only [CollatzResearch.WordTrace]
  refine ⟨100610760506429351715230227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134147680675239135620306969 100610760506429351715230227)
  ·
    refine ⟨150916140759644027572845341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100610760506429351715230227 150916140759644027572845341)
    ·
      refine ⟨56593552784866510339817003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150916140759644027572845341 56593552784866510339817003)
      ·
        refine ⟨84890329177299765509725505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56593552784866510339817003 84890329177299765509725505)
        ·
          refine ⟨63667746882974824132294129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84890329177299765509725505 63667746882974824132294129)
          ·
            refine ⟨47750810162231118099220597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63667746882974824132294129 47750810162231118099220597)
            ·
              refine ⟨4476638452709167321801931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47750810162231118099220597 4476638452709167321801931)
              ·
                refine ⟨6714957679063750982702897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476638452709167321801931 6714957679063750982702897)
                ·
                  refine ⟨5036218259297813237027173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6714957679063750982702897 5036218259297813237027173)
                  ·
                    refine ⟨944290923618339981942595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036218259297813237027173 944290923618339981942595)
                    ·
                      rfl

theorem cell23_5517000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_5517000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517000 prefixEnd_5517000 := by exact prefixLift 5517000
  have htrace : WordTrace (prefixWord ++ tailWord_5517000) baseStart_5517000 baseEnd_5517000 := by
    simpa [prefixWord, tailWord_5517000, baseEnd_5517000] using wordTrace_append hprefix tailTrace_5517000
  have hstable : (prefixWord ++ tailWord_5517000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517000).length < 2 ^ (prefixWord ++ tailWord_5517000).sum := by decide
  have hdescent : baseEnd_5517000 < baseStart_5517000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517010 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5517010 : Nat := 118140960795 + 5517010 * 2 ^ 59
def prefixEnd_5517010 : Nat := 4983230072969 + 3 ^ 40 * 5517010 * 2
def baseEnd_5517010 : Nat := 2832877905661564906702739

theorem tailTrace_5517010 : CollatzResearch.WordTrace tailWord_5517010 prefixEnd_5517010 2832877905661564906702739 := by
  unfold tailWord_5517010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50305471435705618784581121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134147923828548316758882989 50305471435705618784581121)
  ·
    refine ⟨37729103576779214088435841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50305471435705618784581121 37729103576779214088435841)
    ·
      refine ⟨28296827682584410566326881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37729103576779214088435841 28296827682584410566326881)
      ·
        refine ⟨21222620761938307924745161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28296827682584410566326881 21222620761938307924745161)
        ·
          refine ⟨15916965571453730943558871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21222620761938307924745161 15916965571453730943558871)
          ·
            refine ⟨23875448357180596415338307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15916965571453730943558871 23875448357180596415338307)
            ·
              refine ⟨35813172535770894623007461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23875448357180596415338307 35813172535770894623007461)
              ·
                refine ⟨6714969850457042741813899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35813172535770894623007461 6714969850457042741813899)
                ·
                  refine ⟨10072454775685564112720849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714969850457042741813899 10072454775685564112720849)
                  ·
                    refine ⟨7554341081764173084540637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10072454775685564112720849 7554341081764173084540637)
                    ·
                      refine ⟨2832877905661564906702739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554341081764173084540637 2832877905661564906702739)
                      ·
                        rfl

theorem cell23_5517010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5517010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517010 prefixEnd_5517010 := by exact prefixLift 5517010
  have htrace : WordTrace (prefixWord ++ tailWord_5517010) baseStart_5517010 baseEnd_5517010 := by
    simpa [prefixWord, tailWord_5517010, baseEnd_5517010] using wordTrace_append hprefix tailTrace_5517010
  have hstable : (prefixWord ++ tailWord_5517010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517010).length < 2 ^ (prefixWord ++ tailWord_5517010).sum := by decide
  have hdescent : baseEnd_5517010 < baseStart_5517010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517023 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_5517023 : Nat := 118140960795 + 5517023 * 2 ^ 59
def prefixEnd_5517023 : Nat := 4983230072969 + 3 ^ 40 * 5517023 * 2
def baseEnd_5517023 : Nat := 2832884580910073355840179

theorem tailTrace_5517023 : CollatzResearch.WordTrace tailWord_5517023 prefixEnd_5517023 2832884580910073355840179 := by
  unfold tailWord_5517023
  simp only [CollatzResearch.WordTrace]
  refine ⟨201222359891775378358547723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134148239927850252239031815 201222359891775378358547723)
  ·
    refine ⟨301833539837663067537821585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201222359891775378358547723 301833539837663067537821585)
    ·
      refine ⟨226375154878247300653366189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301833539837663067537821585 226375154878247300653366189)
      ·
        refine ⟨84890683079342737745012321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226375154878247300653366189 84890683079342737745012321)
        ·
          refine ⟨63668012309507053308759241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84890683079342737745012321 63668012309507053308759241)
          ·
            refine ⟨47751009232130289981569431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63668012309507053308759241 47751009232130289981569431)
            ·
              refine ⟨71626513848195434972354147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47751009232130289981569431 71626513848195434972354147)
              ·
                refine ⟨107439770772293152458531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71626513848195434972354147 107439770772293152458531221)
                ·
                  refine ⟨5036239254951241521493651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107439770772293152458531221 5036239254951241521493651)
                  ·
                    refine ⟨7554358882426862282240477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036239254951241521493651 7554358882426862282240477)
                    ·
                      refine ⟨2832884580910073355840179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554358882426862282240477 2832884580910073355840179)
                      ·
                        rfl

theorem cell23_5517023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_5517023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517023 prefixEnd_5517023 := by exact prefixLift 5517023
  have htrace : WordTrace (prefixWord ++ tailWord_5517023) baseStart_5517023 baseEnd_5517023 := by
    simpa [prefixWord, tailWord_5517023, baseEnd_5517023] using wordTrace_append hprefix tailTrace_5517023
  have hstable : (prefixWord ++ tailWord_5517023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517023).length < 2 ^ (prefixWord ++ tailWord_5517023).sum := by decide
  have hdescent : baseEnd_5517023 < baseStart_5517023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517033 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 5, 3, 2]
def baseStart_5517033 : Nat := 118140960795 + 5517033 * 2 ^ 59
def prefixEnd_5517033 : Nat := 4983230072969 + 3 ^ 40 * 5517033 * 2
def baseEnd_5517033 : Nat := 2832889715716618316715133

theorem tailTrace_5517033 : CollatzResearch.WordTrace tailWord_5517033 prefixEnd_5517033 2832889715716618316715133 := by
  unfold tailWord_5517033
  simp only [CollatzResearch.WordTrace]
  refine ⟨201222724621739150066411753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134148483081159433377607835 201222724621739150066411753)
  ·
    refine ⟨150917043466304362549808815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201222724621739150066411753 150917043466304362549808815)
    ·
      refine ⟨226375565199456543824713223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150917043466304362549808815 226375565199456543824713223)
      ·
        refine ⟨339563347799184815737069835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226375565199456543824713223 339563347799184815737069835)
        ·
          refine ⟨509345021698777223605604753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339563347799184815737069835 509345021698777223605604753)
          ·
            refine ⟨382008766274082917704203565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509345021698777223605604753 382008766274082917704203565)
            ·
              refine ⟨143253287352781094139076337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382008766274082917704203565 143253287352781094139076337)
              ·
                refine ⟨107439965514585820604307253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143253287352781094139076337 107439965514585820604307253)
                ·
                  refine ⟨10072496766992420681653805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107439965514585820604307253 10072496766992420681653805)
                  ·
                    refine ⟨3777186287622157755620177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10072496766992420681653805 3777186287622157755620177)
                    ·
                      refine ⟨2832889715716618316715133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777186287622157755620177 2832889715716618316715133)
                      ·
                        rfl

theorem cell23_5517033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3, 2].length) (baseStart_5517033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517033 prefixEnd_5517033 := by exact prefixLift 5517033
  have htrace : WordTrace (prefixWord ++ tailWord_5517033) baseStart_5517033 baseEnd_5517033 := by
    simpa [prefixWord, tailWord_5517033, baseEnd_5517033] using wordTrace_append hprefix tailTrace_5517033
  have hstable : (prefixWord ++ tailWord_5517033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517033).length < 2 ^ (prefixWord ++ tailWord_5517033).sum := by decide
  have hdescent : baseEnd_5517033 < baseStart_5517033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517057 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_5517057 : Nat := 118140960795 + 5517057 * 2 ^ 59
def prefixEnd_5517057 : Nat := 4983230072969 + 3 ^ 40 * 5517057 * 2
def baseEnd_5517057 : Nat := 2832902039252326222815023

theorem tailTrace_5517057 : CollatzResearch.WordTrace tailWord_5517057 prefixEnd_5517057 2832902039252326222815023 := by
  unfold tailWord_5517057
  simp only [CollatzResearch.WordTrace]
  refine ⟨201223599973652202165285425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134149066649101468110190283 201223599973652202165285425)
  ·
    refine ⟨150917699980239151623964069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201223599973652202165285425 150917699980239151623964069)
    ·
      refine ⟨28297068746294840929493263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150917699980239151623964069 28297068746294840929493263)
      ·
        refine ⟨42445603119442261394239895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28297068746294840929493263 42445603119442261394239895)
        ·
          refine ⟨63668404679163392091359843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42445603119442261394239895 63668404679163392091359843)
          ·
            refine ⟨95502607018745088137039765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63668404679163392091359843 95502607018745088137039765)
            ·
              refine ⟨4476684704003676006423739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95502607018745088137039765 4476684704003676006423739)
              ·
                refine ⟨6715027056005514009635609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4476684704003676006423739 6715027056005514009635609)
                ·
                  refine ⟨5036270292004135507226707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715027056005514009635609 5036270292004135507226707)
                  ·
                    refine ⟨7554405438006203260840061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036270292004135507226707 7554405438006203260840061)
                    ·
                      refine ⟨2832902039252326222815023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554405438006203260840061 2832902039252326222815023)
                      ·
                        rfl

theorem cell23_5517057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_5517057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517057 prefixEnd_5517057 := by exact prefixLift 5517057
  have htrace : WordTrace (prefixWord ++ tailWord_5517057) baseStart_5517057 baseEnd_5517057 := by
    simpa [prefixWord, tailWord_5517057, baseEnd_5517057] using wordTrace_append hprefix tailTrace_5517057
  have hstable : (prefixWord ++ tailWord_5517057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517057).length < 2 ^ (prefixWord ++ tailWord_5517057).sum := by decide
  have hdescent : baseEnd_5517057 < baseStart_5517057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517080 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5517080 : Nat := 118140960795 + 5517080 * 2 ^ 59
def prefixEnd_5517080 : Nat := 4983230072969 + 3 ^ 40 * 5517080 * 2
def baseEnd_5517080 : Nat := 2832913849307379632827417

theorem tailTrace_5517080 : CollatzResearch.WordTrace tailWord_5517080 prefixEnd_5517080 2832913849307379632827417 := by
  unfold tailWord_5517080
  simp only [CollatzResearch.WordTrace]
  refine ⟨100612219426284438546686347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134149625901712584728915129 100612219426284438546686347)
  ·
    refine ⟨150918329139426657820029521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100612219426284438546686347 150918329139426657820029521)
    ·
      refine ⟨113188746854569993365022141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150918329139426657820029521 113188746854569993365022141)
      ·
        refine ⟨42445780070463747511883303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113188746854569993365022141 42445780070463747511883303)
        ·
          refine ⟨63668670105695621267824955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42445780070463747511883303 63668670105695621267824955)
          ·
            refine ⟨95503005158543431901737433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63668670105695621267824955 95503005158543431901737433)
            ·
              refine ⟨71627253868907573926303075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95503005158543431901737433 71627253868907573926303075)
              ·
                refine ⟨107440880803361360889454613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71627253868907573926303075 107440880803361360889454613)
                ·
                  refine ⟨5036291287657563791693185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107440880803361360889454613 5036291287657563791693185)
                  ·
                    refine ⟨3777218465743172843769889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036291287657563791693185 3777218465743172843769889)
                    ·
                      refine ⟨2832913849307379632827417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777218465743172843769889 2832913849307379632827417)
                      ·
                        rfl

theorem cell23_5517080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5517080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517080 prefixEnd_5517080 := by exact prefixLift 5517080
  have htrace : WordTrace (prefixWord ++ tailWord_5517080) baseStart_5517080 baseEnd_5517080 := by
    simpa [prefixWord, tailWord_5517080, baseEnd_5517080] using wordTrace_append hprefix tailTrace_5517080
  have hstable : (prefixWord ++ tailWord_5517080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517080).length < 2 ^ (prefixWord ++ tailWord_5517080).sum := by decide
  have hdescent : baseEnd_5517080 < baseStart_5517080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517103 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 5]
def baseStart_5517103 : Nat := 118140960795 + 5517103 * 2 ^ 59
def prefixEnd_5517103 : Nat := 4983230072969 + 3 ^ 40 * 5517103 * 2
def baseEnd_5517103 : Nat := 314769517706937004759979

theorem tailTrace_5517103 : CollatzResearch.WordTrace tailWord_5517103 prefixEnd_5517103 314769517706937004759979 := by
  unfold tailWord_5517103
  simp only [CollatzResearch.WordTrace]
  refine ⟨201225277731485552021459963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134150185154323701347639975 201225277731485552021459963)
  ·
    refine ⟨301837916597228328032189945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201225277731485552021459963 301837916597228328032189945)
    ·
      refine ⟨226378437447921246024142459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301837916597228328032189945 226378437447921246024142459)
      ·
        refine ⟨339567656171881869036213689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226378437447921246024142459 339567656171881869036213689)
        ·
          refine ⟨254675742128911401777160267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339567656171881869036213689 254675742128911401777160267)
          ·
            refine ⟨382013613193367102665740401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254675742128911401777160267 382013613193367102665740401)
            ·
              refine ⟨286510209895025326999305301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382013613193367102665740401 286510209895025326999305301)
              ·
                refine ⟨3357541522207328050773109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 286510209895025326999305301 3357541522207328050773109)
                ·
                  refine ⟨314769517706937004759979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357541522207328050773109 314769517706937004759979)
                  ·
                    rfl

theorem cell23_5517103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 5].length) (baseStart_5517103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517103 prefixEnd_5517103 := by exact prefixLift 5517103
  have htrace : WordTrace (prefixWord ++ tailWord_5517103) baseStart_5517103 baseEnd_5517103 := by
    simpa [prefixWord, tailWord_5517103, baseEnd_5517103] using wordTrace_append hprefix tailTrace_5517103
  have hstable : (prefixWord ++ tailWord_5517103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517103).length < 2 ^ (prefixWord ++ tailWord_5517103).sum := by decide
  have hdescent : baseEnd_5517103 < baseStart_5517103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517110 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5517110 : Nat := 118140960795 + 5517110 * 2 ^ 59
def prefixEnd_5517110 : Nat := 4983230072969 + 3 ^ 40 * 5517110 * 2
def baseEnd_5517110 : Nat := 2832929253727014515452279

theorem tailTrace_5517110 : CollatzResearch.WordTrace tailWord_5517110 prefixEnd_5517110 2832929253727014515452279 := by
  unfold tailWord_5517110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12576595815153762013560299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134150355361640128144643189 12576595815153762013560299)
  ·
    refine ⟨18864893722730643020340449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12576595815153762013560299 18864893722730643020340449)
    ·
      refine ⟨14148670292047982265255337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18864893722730643020340449 14148670292047982265255337)
      ·
        refine ⟨10611502719035986698941503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14148670292047982265255337 10611502719035986698941503)
        ·
          refine ⟨15917254078553980048412255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611502719035986698941503 15917254078553980048412255)
          ·
            refine ⟨23875881117830970072618383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15917254078553980048412255 23875881117830970072618383)
            ·
              refine ⟨35813821676746455108927575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23875881117830970072618383 35813821676746455108927575)
              ·
                refine ⟨53720732515119682663391363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35813821676746455108927575 53720732515119682663391363)
                ·
                  refine ⟨80581098772679523995087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53720732515119682663391363 80581098772679523995087045)
                  ·
                    refine ⟨15108956019877410749078821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80581098772679523995087045 15108956019877410749078821)
                    ·
                      refine ⟨2832929253727014515452279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15108956019877410749078821 2832929253727014515452279)
                      ·
                        rfl

theorem cell23_5517110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5517110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517110 prefixEnd_5517110 := by exact prefixLift 5517110
  have htrace : WordTrace (prefixWord ++ tailWord_5517110) baseStart_5517110 baseEnd_5517110 := by
    simpa [prefixWord, tailWord_5517110, baseEnd_5517110] using wordTrace_append hprefix tailTrace_5517110
  have hstable : (prefixWord ++ tailWord_5517110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517110).length < 2 ^ (prefixWord ++ tailWord_5517110).sum := by decide
  have hdescent : baseEnd_5517110 < baseStart_5517110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517148 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5517148 : Nat := 118140960795 + 5517148 * 2 ^ 59
def prefixEnd_5517148 : Nat := 4983230072969 + 3 ^ 40 * 5517148 * 2
def baseEnd_5517148 : Nat := 2832948765991885366777105

theorem tailTrace_5517148 : CollatzResearch.WordTrace tailWord_5517148 prefixEnd_5517148 2832948765991885366777105 := by
  unfold tailWord_5517148
  simp only [CollatzResearch.WordTrace]
  refine ⟨100613459508161262353424049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134151279344215016471232065 100613459508161262353424049)
  ·
    refine ⟨75460094631120946765068037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100613459508161262353424049 75460094631120946765068037)
    ·
      refine ⟨14148767743335177518450257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75460094631120946765068037 14148767743335177518450257)
      ·
        refine ⟨10611575807501383138837693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14148767743335177518450257 10611575807501383138837693)
        ·
          refine ⟨3979340927813018677064135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10611575807501383138837693 3979340927813018677064135)
          ·
            refine ⟨5969011391719528015596203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979340927813018677064135 5969011391719528015596203)
            ·
              refine ⟨8953517087579292023394305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5969011391719528015596203 8953517087579292023394305)
              ·
                refine ⟨6715137815684469017545729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8953517087579292023394305 6715137815684469017545729)
                ·
                  refine ⟨5036353361763351763159297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715137815684469017545729 5036353361763351763159297)
                  ·
                    refine ⟨3777265021322513822369473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036353361763351763159297 3777265021322513822369473)
                    ·
                      refine ⟨2832948765991885366777105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777265021322513822369473 2832948765991885366777105)
                      ·
                        rfl

theorem cell23_5517148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5517148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517148 prefixEnd_5517148 := by exact prefixLift 5517148
  have htrace : WordTrace (prefixWord ++ tailWord_5517148) baseStart_5517148 baseEnd_5517148 := by
    simpa [prefixWord, tailWord_5517148, baseEnd_5517148] using wordTrace_append hprefix tailTrace_5517148
  have hstable : (prefixWord ++ tailWord_5517148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517148).length < 2 ^ (prefixWord ++ tailWord_5517148).sum := by decide
  have hdescent : baseEnd_5517148 < baseStart_5517148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517153 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_5517153 : Nat := 118140960795 + 5517153 * 2 ^ 59
def prefixEnd_5517153 : Nat := 4983230072969 + 3 ^ 40 * 5517153 * 2
def baseEnd_5517153 : Nat := 2832951333395157847214581

theorem tailTrace_5517153 : CollatzResearch.WordTrace tailWord_5517153 prefixEnd_5517153 2832951333395157847214581 := by
  unfold tailWord_5517153
  simp only [CollatzResearch.WordTrace]
  refine ⟨201227101381304410560780113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134151400920869607040520075 201227101381304410560780113)
  ·
    refine ⟨150920326035978307920585085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201227101381304410560780113 150920326035978307920585085)
    ·
      refine ⟨56595122263491865470219407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150920326035978307920585085 56595122263491865470219407)
      ·
        refine ⟨84892683395237798205329111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56595122263491865470219407 84892683395237798205329111)
        ·
          refine ⟨127339025092856697307993667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84892683395237798205329111 127339025092856697307993667)
          ·
            refine ⟨191008537639285045961990501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127339025092856697307993667 191008537639285045961990501)
            ·
              refine ⟨35814100807365946117873219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191008537639285045961990501 35814100807365946117873219)
              ·
                refine ⟨53721151211048919176809829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35814100807365946117873219 53721151211048919176809829)
                ·
                  refine ⟨10072715852071672345651843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53721151211048919176809829 10072715852071672345651843)
                  ·
                    refine ⟨15109073778107508518477765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10072715852071672345651843 15109073778107508518477765)
                    ·
                      refine ⟨2832951333395157847214581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15109073778107508518477765 2832951333395157847214581)
                      ·
                        rfl

theorem cell23_5517153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_5517153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517153 prefixEnd_5517153 := by exact prefixLift 5517153
  have htrace : WordTrace (prefixWord ++ tailWord_5517153) baseStart_5517153 baseEnd_5517153 := by
    simpa [prefixWord, tailWord_5517153, baseEnd_5517153] using wordTrace_append hprefix tailTrace_5517153
  have hstable : (prefixWord ++ tailWord_5517153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517153).length < 2 ^ (prefixWord ++ tailWord_5517153).sum := by decide
  have hdescent : baseEnd_5517153 < baseStart_5517153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517247 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 2, 3, 2]
def baseStart_5517247 : Nat := 118140960795 + 5517247 * 2 ^ 59
def prefixEnd_5517247 : Nat := 4983230072969 + 3 ^ 40 * 5517247 * 2
def baseEnd_5517247 : Nat := 2832999600576680479439149

theorem tailTrace_5517247 : CollatzResearch.WordTrace tailWord_5517247 prefixEnd_5517247 2832999600576680479439149 := by
  unfold tailWord_5517247
  simp only [CollatzResearch.WordTrace]
  refine ⟨201230529842963864614701995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134153686561975909743134663 201230529842963864614701995)
  ·
    refine ⟨301845794764445796922052993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201230529842963864614701995 301845794764445796922052993)
    ·
      refine ⟨226384346073334347691539745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301845794764445796922052993 226384346073334347691539745)
      ·
        refine ⟨169788259555000760768654809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226384346073334347691539745 169788259555000760768654809)
        ·
          refine ⟨127341194666250570576491107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169788259555000760768654809 127341194666250570576491107)
          ·
            refine ⟨191011791999375855864736661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127341194666250570576491107 191011791999375855864736661)
            ·
              refine ⟨8953677749970743243659531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191011791999375855864736661 8953677749970743243659531)
              ·
                refine ⟨13430516624956114865489297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8953677749970743243659531 13430516624956114865489297)
                ·
                  refine ⟨10072887468717086149116973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13430516624956114865489297 10072887468717086149116973)
                  ·
                    refine ⟨3777332800768907305918865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10072887468717086149116973 3777332800768907305918865)
                    ·
                      refine ⟨2832999600576680479439149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777332800768907305918865 2832999600576680479439149)
                      ·
                        rfl

theorem cell23_5517247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_5517247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517247 prefixEnd_5517247 := by exact prefixLift 5517247
  have htrace : WordTrace (prefixWord ++ tailWord_5517247) baseStart_5517247 baseEnd_5517247 := by
    simpa [prefixWord, tailWord_5517247, baseEnd_5517247] using wordTrace_append hprefix tailTrace_5517247
  have hstable : (prefixWord ++ tailWord_5517247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517247).length < 2 ^ (prefixWord ++ tailWord_5517247).sum := by decide
  have hdescent : baseEnd_5517247 < baseStart_5517247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517287 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 1, 6]
def baseStart_5517287 : Nat := 118140960795 + 5517287 * 2 ^ 59
def prefixEnd_5517287 : Nat := 4983230072969 + 3 ^ 40 * 5517287 * 2
def baseEnd_5517287 : Nat := 944340046600953440979655

theorem tailTrace_5517287 : CollatzResearch.WordTrace tailWord_5517287 prefixEnd_5517287 944340046600953440979655 := by
  unfold tailWord_5517287
  simp only [CollatzResearch.WordTrace]
  refine ⟨201231988762818951446158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134154659175212634297438743 201231988762818951446158115)
  ·
    refine ⟨301847983144228427169237173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201231988762818951446158115 301847983144228427169237173)
    ·
      refine ⟨28298248419771415047115985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301847983144228427169237173 28298248419771415047115985)
      ·
        refine ⟨21223686314828561285336989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28298248419771415047115985 21223686314828561285336989)
        ·
          refine ⟨7958882368060710482001371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21223686314828561285336989 7958882368060710482001371)
          ·
            refine ⟨11938323552091065723002057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958882368060710482001371 11938323552091065723002057)
            ·
              refine ⟨8953742664068299292251543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11938323552091065723002057 8953742664068299292251543)
              ·
                refine ⟨13430613996102448938377315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8953742664068299292251543 13430613996102448938377315)
                ·
                  refine ⟨20145920994153673407565973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13430613996102448938377315 20145920994153673407565973)
                  ·
                    refine ⟨944340046600953440979655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20145920994153673407565973 944340046600953440979655)
                    ·
                      rfl

theorem cell23_5517287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_5517287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517287 prefixEnd_5517287 := by exact prefixLift 5517287
  have htrace : WordTrace (prefixWord ++ tailWord_5517287) baseStart_5517287 baseEnd_5517287 := by
    simpa [prefixWord, tailWord_5517287, baseEnd_5517287] using wordTrace_append hprefix tailTrace_5517287
  have hstable : (prefixWord ++ tailWord_5517287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517287).length < 2 ^ (prefixWord ++ tailWord_5517287).sum := by decide
  have hdescent : baseEnd_5517287 < baseStart_5517287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517294 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_5517294 : Nat := 118140960795 + 5517294 * 2 ^ 59
def prefixEnd_5517294 : Nat := 4983230072969 + 3 ^ 40 * 5517294 * 2
def baseEnd_5517294 : Nat := 2833023734167441795551433

theorem tailTrace_5517294 : CollatzResearch.WordTrace tailWord_5517294 prefixEnd_5517294 2833023734167441795551433 := by
  unfold tailWord_5517294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25154030509224198955207867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134154829382529061094441957 25154030509224198955207867)
  ·
    refine ⟨37731045763836298432811801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25154030509224198955207867 37731045763836298432811801)
    ·
      refine ⟨28298284322877223824608851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37731045763836298432811801 28298284322877223824608851)
      ·
        refine ⟨42447426484315835736913277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28298284322877223824608851 42447426484315835736913277)
        ·
          refine ⟨15917784931618438401342479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42447426484315835736913277 15917784931618438401342479)
          ·
            refine ⟨23876677397427657602013719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15917784931618438401342479 23876677397427657602013719)
            ·
              refine ⟨35815016096141486403020579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23876677397427657602013719 35815016096141486403020579)
              ·
                refine ⟨53722524144212229604530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35815016096141486403020579 53722524144212229604530869)
                ·
                  refine ⟨5036486638519896525424769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53722524144212229604530869 5036486638519896525424769)
                  ·
                    refine ⟨3777364978889922394068577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036486638519896525424769 3777364978889922394068577)
                    ·
                      refine ⟨2833023734167441795551433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777364978889922394068577 2833023734167441795551433)
                      ·
                        rfl

theorem cell23_5517294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_5517294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517294 prefixEnd_5517294 := by exact prefixLift 5517294
  have htrace : WordTrace (prefixWord ++ tailWord_5517294) baseStart_5517294 baseEnd_5517294 := by
    simpa [prefixWord, tailWord_5517294, baseEnd_5517294] using wordTrace_append hprefix tailTrace_5517294
  have hstable : (prefixWord ++ tailWord_5517294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517294).length < 2 ^ (prefixWord ++ tailWord_5517294).sum := by decide
  have hdescent : baseEnd_5517294 < baseStart_5517294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517351 : List Nat := [1, 1, 7, 1, 3, 1, 2, 7]
def baseStart_5517351 : Nat := 118140960795 + 5517351 * 2 ^ 59
def prefixEnd_5517351 : Nat := 4983230072969 + 3 ^ 40 * 5517351 * 2
def baseEnd_5517351 : Nat := 104927888983879558242173

theorem tailTrace_5517351 : CollatzResearch.WordTrace tailWord_5517351 prefixEnd_5517351 104927888983879558242173 := by
  unfold tailWord_5517351
  simp only [CollatzResearch.WordTrace]
  refine ⟨201234323034587090376487907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134156215356391393584325271 201234323034587090376487907)
  ·
    refine ⟨301851484551880635564731861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201234323034587090376487907 301851484551880635564731861)
    ·
      refine ⟨7074644169184702396048403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 301851484551880635564731861 7074644169184702396048403)
      ·
        refine ⟨10611966253777053594072605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7074644169184702396048403 10611966253777053594072605)
        ·
          refine ⟨3979487345166395097777227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10611966253777053594072605 3979487345166395097777227)
          ·
            refine ⟨5969231017749592646665841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979487345166395097777227 5969231017749592646665841)
            ·
              refine ⟨4476923263312194484999381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5969231017749592646665841 4476923263312194484999381)
              ·
                refine ⟨104927888983879558242173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4476923263312194484999381 104927888983879558242173)
                ·
                  rfl

theorem cell23_5517351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 7].length) (baseStart_5517351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517351 prefixEnd_5517351 := by exact prefixLift 5517351
  have htrace : WordTrace (prefixWord ++ tailWord_5517351) baseStart_5517351 baseEnd_5517351 := by
    simpa [prefixWord, tailWord_5517351, baseEnd_5517351] using wordTrace_append hprefix tailTrace_5517351
  have hstable : (prefixWord ++ tailWord_5517351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517351).length < 2 ^ (prefixWord ++ tailWord_5517351).sum := by decide
  have hdescent : baseEnd_5517351 < baseStart_5517351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517367 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_5517367 : Nat := 118140960795 + 5517367 * 2 ^ 59
def prefixEnd_5517367 : Nat := 4983230072969 + 3 ^ 40 * 5517367 * 2
def baseEnd_5517367 : Nat := 2833061218255220009938597

theorem tailTrace_5517367 : CollatzResearch.WordTrace tailWord_5517367 prefixEnd_5517367 2833061218255220009938597 := by
  unfold tailWord_5517367
  simp only [CollatzResearch.WordTrace]
  refine ⟨201234906602529125109070355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134156604401686083406046903 201234906602529125109070355)
  ·
    refine ⟨301852359903793687663605533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201234906602529125109070355 301852359903793687663605533)
    ·
      refine ⟨113194634963922632873852075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301852359903793687663605533 113194634963922632873852075)
      ·
        refine ⟨169791952445883949310778113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113194634963922632873852075 169791952445883949310778113)
        ·
          refine ⟨127343964334412961983083585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169791952445883949310778113 127343964334412961983083585)
          ·
            refine ⟨95507973250809721487312689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127343964334412961983083585 95507973250809721487312689)
            ·
              refine ⟨71630979938107291115484517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95507973250809721487312689 71630979938107291115484517)
              ·
                refine ⟨13430808738395117084153347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71630979938107291115484517 13430808738395117084153347)
                ·
                  refine ⟨20146213107592675626230021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13430808738395117084153347 20146213107592675626230021)
                  ·
                    refine ⟨3777414957673626679918129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20146213107592675626230021 3777414957673626679918129)
                    ·
                      refine ⟨2833061218255220009938597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777414957673626679918129 2833061218255220009938597)
                      ·
                        rfl

theorem cell23_5517367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_5517367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517367 prefixEnd_5517367 := by exact prefixLift 5517367
  have htrace : WordTrace (prefixWord ++ tailWord_5517367) baseStart_5517367 baseEnd_5517367 := by
    simpa [prefixWord, tailWord_5517367, baseEnd_5517367] using wordTrace_append hprefix tailTrace_5517367
  have hstable : (prefixWord ++ tailWord_5517367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517367).length < 2 ^ (prefixWord ++ tailWord_5517367).sum := by decide
  have hdescent : baseEnd_5517367 < baseStart_5517367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517370 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_5517370 : Nat := 118140960795 + 5517370 * 2 ^ 59
def prefixEnd_5517370 : Nat := 4983230072969 + 3 ^ 40 * 5517370 * 2
def baseEnd_5517370 : Nat := 2833062758697183498201083

theorem tailTrace_5517370 : CollatzResearch.WordTrace tailWord_5517370 prefixEnd_5517370 2833062758697183498201083 := by
  unfold tailWord_5517370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50308754005379564155357391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134156677347678837747619709 50308754005379564155357391)
  ·
    refine ⟨75463131008069346233036087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50308754005379564155357391 75463131008069346233036087)
    ·
      refine ⟨113194696512104019349554131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75463131008069346233036087 113194696512104019349554131)
      ·
        refine ⟨169792044768156029024331197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113194696512104019349554131 169792044768156029024331197)
        ·
          refine ⟨63672016788058510884124199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169792044768156029024331197 63672016788058510884124199)
          ·
            refine ⟨95508025182087766326186299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63672016788058510884124199 95508025182087766326186299)
            ·
              refine ⟨143262037773131649489279449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95508025182087766326186299 143262037773131649489279449)
              ·
                refine ⟨107446528329848737116959587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143262037773131649489279449 107446528329848737116959587)
                ·
                  refine ⟨161169792494773105675439381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107446528329848737116959587 161169792494773105675439381)
                  ·
                    refine ⟨7554834023192489328536221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161169792494773105675439381 7554834023192489328536221)
                    ·
                      refine ⟨2833062758697183498201083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554834023192489328536221 2833062758697183498201083)
                      ·
                        rfl

theorem cell23_5517370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_5517370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517370 prefixEnd_5517370 := by exact prefixLift 5517370
  have htrace : WordTrace (prefixWord ++ tailWord_5517370) baseStart_5517370 baseEnd_5517370 := by
    simpa [prefixWord, tailWord_5517370, baseEnd_5517370] using wordTrace_append hprefix tailTrace_5517370
  have hstable : (prefixWord ++ tailWord_5517370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517370).length < 2 ^ (prefixWord ++ tailWord_5517370).sum := by decide
  have hdescent : baseEnd_5517370 < baseStart_5517370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517437 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_5517437 : Nat := 118140960795 + 5517437 * 2 ^ 59
def prefixEnd_5517437 : Nat := 4983230072969 + 3 ^ 40 * 5517437 * 2
def baseEnd_5517437 : Nat := 944365720633678245354425

theorem tailTrace_5517437 : CollatzResearch.WordTrace tailWord_5517437 prefixEnd_5517437 944365720633678245354425 := by
  unfold tailWord_5517437
  simp only [CollatzResearch.WordTrace]
  refine ⟨201237459712275527064118565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134158306474850351376079043 201237459712275527064118565)
  ·
    refine ⟨37732023696051661324522231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201237459712275527064118565 37732023696051661324522231)
    ·
      refine ⟨56598035544077491986783347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37732023696051661324522231 56598035544077491986783347)
      ·
        refine ⟨84897053316116237980175021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56598035544077491986783347 84897053316116237980175021)
        ·
          refine ⟨31836394993543589242565633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84897053316116237980175021 31836394993543589242565633)
          ·
            refine ⟨23877296245157691931924225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31836394993543589242565633 23877296245157691931924225)
            ·
              refine ⟨17907972183868268948943169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23877296245157691931924225 17907972183868268948943169)
              ·
                refine ⟨13430979137901201711707377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17907972183868268948943169 13430979137901201711707377)
                ·
                  refine ⟨10073234353425901283780533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13430979137901201711707377 10073234353425901283780533)
                  ·
                    refine ⟨944365720633678245354425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10073234353425901283780533 944365720633678245354425)
                    ·
                      rfl

theorem cell23_5517437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_5517437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517437 prefixEnd_5517437 := by exact prefixLift 5517437
  have htrace : WordTrace (prefixWord ++ tailWord_5517437) baseStart_5517437 baseEnd_5517437 := by
    simpa [prefixWord, tailWord_5517437, baseEnd_5517437] using wordTrace_append hprefix tailTrace_5517437
  have hstable : (prefixWord ++ tailWord_5517437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517437).length < 2 ^ (prefixWord ++ tailWord_5517437).sum := by decide
  have hdescent : baseEnd_5517437 < baseStart_5517437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517440 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_5517440 : Nat := 118140960795 + 5517440 * 2 ^ 59
def prefixEnd_5517440 : Nat := 4983230072969 + 3 ^ 40 * 5517440 * 2
def baseEnd_5517440 : Nat := 2833098702342998224325761

theorem tailTrace_5517440 : CollatzResearch.WordTrace tailWord_5517440 prefixEnd_5517440 2833098702342998224325761 := by
  unfold tailWord_5517440
  simp only [CollatzResearch.WordTrace]
  refine ⟨100618784565632329288238887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134158379420843105717651849 100618784565632329288238887)
  ·
    refine ⟨150928176848448493932358331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100618784565632329288238887 150928176848448493932358331)
    ·
      refine ⟨226392265272672740898537497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150928176848448493932358331 226392265272672740898537497)
      ·
        refine ⟨169794198954504555673903123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226392265272672740898537497 169794198954504555673903123)
        ·
          refine ⟨254691298431756833510854685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169794198954504555673903123 254691298431756833510854685)
          ·
            refine ⟨95509236911908812566570507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254691298431756833510854685 95509236911908812566570507)
            ·
              refine ⟨143263855367863218849855761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95509236911908812566570507 143263855367863218849855761)
              ·
                refine ⟨107447891525897414137391821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143263855367863218849855761 107447891525897414137391821)
                ·
                  refine ⟨40292959322211530301521933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107447891525897414137391821 40292959322211530301521933)
                  ·
                    refine ⟨15109859745829323863070725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40292959322211530301521933 15109859745829323863070725)
                    ·
                      refine ⟨2833098702342998224325761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15109859745829323863070725 2833098702342998224325761)
                      ·
                        rfl

theorem cell23_5517440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_5517440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517440 prefixEnd_5517440 := by exact prefixLift 5517440
  have htrace : WordTrace (prefixWord ++ tailWord_5517440) baseStart_5517440 baseEnd_5517440 := by
    simpa [prefixWord, tailWord_5517440, baseEnd_5517440] using wordTrace_append hprefix tailTrace_5517440
  have hstable : (prefixWord ++ tailWord_5517440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517440).length < 2 ^ (prefixWord ++ tailWord_5517440).sum := by decide
  have hdescent : baseEnd_5517440 < baseStart_5517440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517474 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_5517474 : Nat := 118140960795 + 5517474 * 2 ^ 59
def prefixEnd_5517474 : Nat := 4983230072969 + 3 ^ 40 * 5517474 * 2
def baseEnd_5517474 : Nat := 2833116160685251091300605

theorem tailTrace_5517474 : CollatzResearch.WordTrace tailWord_5517474 prefixEnd_5517474 2833116160685251091300605 := by
  unfold tailWord_5517474
  simp only [CollatzResearch.WordTrace]
  refine ⟨50309702303285370595803869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134159206142094321588810317 50309702303285370595803869)
  ·
    refine ⟨18866138363732013973426451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50309702303285370595803869 18866138363732013973426451)
    ·
      refine ⟨28299207545598020960139677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18866138363732013973426451 28299207545598020960139677)
      ·
        refine ⟨10612202829599257860052379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28299207545598020960139677 10612202829599257860052379)
        ·
          refine ⟨15918304244398886790078569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10612202829599257860052379 15918304244398886790078569)
          ·
            refine ⟨11938728183299165092558927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15918304244398886790078569 11938728183299165092558927)
            ·
              refine ⟨17908092274948747638838391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11938728183299165092558927 17908092274948747638838391)
              ·
                refine ⟨26862138412423121458257587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17908092274948747638838391 26862138412423121458257587)
                ·
                  refine ⟨40293207618634682187386381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26862138412423121458257587 40293207618634682187386381)
                  ·
                    refine ⟨15109952856988005820269893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40293207618634682187386381 15109952856988005820269893)
                    ·
                      refine ⟨2833116160685251091300605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15109952856988005820269893 2833116160685251091300605)
                      ·
                        rfl

theorem cell23_5517474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_5517474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517474 prefixEnd_5517474 := by exact prefixLift 5517474
  have htrace : WordTrace (prefixWord ++ tailWord_5517474) baseStart_5517474 baseEnd_5517474 := by
    simpa [prefixWord, tailWord_5517474, baseEnd_5517474] using wordTrace_append hprefix tailTrace_5517474
  have hstable : (prefixWord ++ tailWord_5517474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517474).length < 2 ^ (prefixWord ++ tailWord_5517474).sum := by decide
  have hdescent : baseEnd_5517474 < baseStart_5517474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517477 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_5517477 : Nat := 118140960795 + 5517477 * 2 ^ 59
def prefixEnd_5517477 : Nat := 4983230072969 + 3 ^ 40 * 5517477 * 2
def baseEnd_5517477 : Nat := 2833117701127214579563091

theorem tailTrace_5517477 : CollatzResearch.WordTrace tailWord_5517477 prefixEnd_5517477 2833117701127214579563091 := by
  unfold tailWord_5517477
  simp only [CollatzResearch.WordTrace]
  refine ⟨201238918632130613895574685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134159279088087075930383123 201238918632130613895574685)
  ·
    refine ⟨75464594487048980210840507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201238918632130613895574685 75464594487048980210840507)
    ·
      refine ⟨113196891730573470316260761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75464594487048980210840507 113196891730573470316260761)
      ·
        refine ⟨84897668797930102737195571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113196891730573470316260761 84897668797930102737195571)
        ·
          refine ⟨127346503196895154105793357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84897668797930102737195571 127346503196895154105793357)
          ·
            refine ⟨47754938698835682789672509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127346503196895154105793357 47754938698835682789672509)
            ·
              refine ⟨17908102012063381046127191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47754938698835682789672509 17908102012063381046127191)
              ·
                refine ⟨26862153018095071569190787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17908102012063381046127191 26862153018095071569190787)
                ·
                  refine ⟨40293229527142607353786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26862153018095071569190787 40293229527142607353786181)
                  ·
                    refine ⟨7554980536339238878834909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40293229527142607353786181 7554980536339238878834909)
                    ·
                      refine ⟨2833117701127214579563091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7554980536339238878834909 2833117701127214579563091)
                      ·
                        rfl

theorem cell23_5517477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_5517477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517477 prefixEnd_5517477 := by exact prefixLift 5517477
  have htrace : WordTrace (prefixWord ++ tailWord_5517477) baseStart_5517477 baseEnd_5517477 := by
    simpa [prefixWord, tailWord_5517477, baseEnd_5517477] using wordTrace_append hprefix tailTrace_5517477
  have hstable : (prefixWord ++ tailWord_5517477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517477).length < 2 ^ (prefixWord ++ tailWord_5517477).sum := by decide
  have hdescent : baseEnd_5517477 < baseStart_5517477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517514 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_5517514 : Nat := 118140960795 + 5517514 * 2 ^ 59
def prefixEnd_5517514 : Nat := 4983230072969 + 3 ^ 40 * 5517514 * 2
def baseEnd_5517514 : Nat := 314792966656825659422269

theorem tailTrace_5517514 : CollatzResearch.WordTrace tailWord_5517514 prefixEnd_5517514 314792966656825659422269 := by
  unfold tailWord_5517514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50310067033249142303667899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134160178755331046143114397 50310067033249142303667899)
  ·
    refine ⟨75465100549873713455501849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50310067033249142303667899 75465100549873713455501849)
    ·
      refine ⟨56598825412405285091626387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75465100549873713455501849 56598825412405285091626387)
      ·
        refine ⟨84898238118607927637439581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56598825412405285091626387 84898238118607927637439581)
        ·
          refine ⟨31836839294477972864039843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84898238118607927637439581 31836839294477972864039843)
          ·
            refine ⟨47755258941716959296059765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31836839294477972864039843 47755258941716959296059765)
            ·
              refine ⟨4477055525785964934005603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47755258941716959296059765 4477055525785964934005603)
              ·
                refine ⟨6715583288678947401008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477055525785964934005603 6715583288678947401008405)
                ·
                  refine ⟨314792966656825659422269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6715583288678947401008405 314792966656825659422269)
                  ·
                    rfl

theorem cell23_5517514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_5517514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517514 prefixEnd_5517514 := by exact prefixLift 5517514
  have htrace : WordTrace (prefixWord ++ tailWord_5517514) baseStart_5517514 baseEnd_5517514 := by
    simpa [prefixWord, tailWord_5517514, baseEnd_5517514] using wordTrace_append hprefix tailTrace_5517514
  have hstable : (prefixWord ++ tailWord_5517514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517514).length < 2 ^ (prefixWord ++ tailWord_5517514).sum := by decide
  have hdescent : baseEnd_5517514 < baseStart_5517514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517544 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_5517544 : Nat := 118140960795 + 5517544 * 2 ^ 59
def prefixEnd_5517544 : Nat := 4983230072969 + 3 ^ 40 * 5517544 * 2
def baseEnd_5517544 : Nat := 944384034777021939141761

theorem tailTrace_5517544 : CollatzResearch.WordTrace tailWord_5517544 prefixEnd_5517544 944384034777021939141761 := by
  unfold tailWord_5517544
  simp only [CollatzResearch.WordTrace]
  refine ⟨100620681161443942169131843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134160908215258589558842457 100620681161443942169131843)
  ·
    refine ⟨150931021742165913253697765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100620681161443942169131843 150931021742165913253697765)
    ·
      refine ⟨28299566576656108735068331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150931021742165913253697765 28299566576656108735068331)
      ·
        refine ⟨42449349864984163102602497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28299566576656108735068331 42449349864984163102602497)
        ·
          refine ⟨31837012398738122326951873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42449349864984163102602497 31837012398738122326951873)
          ·
            refine ⟨23877759299053591745213905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31837012398738122326951873 23877759299053591745213905)
            ·
              refine ⟨17908319474290193808910429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23877759299053591745213905 17908319474290193808910429)
              ·
                refine ⟨6715619802858822678341411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17908319474290193808910429 6715619802858822678341411)
                ·
                  refine ⟨10073429704288234017512117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715619802858822678341411 10073429704288234017512117)
                  ·
                    refine ⟨944384034777021939141761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10073429704288234017512117 944384034777021939141761)
                    ·
                      rfl

theorem cell23_5517544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_5517544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517544 prefixEnd_5517544 := by exact prefixLift 5517544
  have htrace : WordTrace (prefixWord ++ tailWord_5517544) baseStart_5517544 baseEnd_5517544 := by
    simpa [prefixWord, tailWord_5517544, baseEnd_5517544] using wordTrace_append hprefix tailTrace_5517544
  have hstable : (prefixWord ++ tailWord_5517544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517544).length < 2 ^ (prefixWord ++ tailWord_5517544).sum := by decide
  have hdescent : baseEnd_5517544 < baseStart_5517544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517551 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 2, 3, 2]
def baseStart_5517551 : Nat := 118140960795 + 5517551 * 2 ^ 59
def prefixEnd_5517551 : Nat := 4983230072969 + 3 ^ 40 * 5517551 * 2
def baseEnd_5517551 : Nat := 2833155698695647290037751

theorem tailTrace_5517551 : CollatzResearch.WordTrace tailWord_5517551 prefixEnd_5517551 2833155698695647290037751 := by
  unfold tailWord_5517551
  simp only [CollatzResearch.WordTrace]
  refine ⟨201241617633862524533768507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134161078422575016355845671 201241617633862524533768507)
  ·
    refine ⟨301862426450793786800652761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201241617633862524533768507 301862426450793786800652761)
    ·
      refine ⟨226396819838095340100489571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301862426450793786800652761 226396819838095340100489571)
      ·
        refine ⟨339595229757143010150734357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226396819838095340100489571 339595229757143010150734357)
        ·
          refine ⟨15918526394866078600815673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 339595229757143010150734357 15918526394866078600815673)
          ·
            refine ⟨11938894796149558950611755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15918526394866078600815673 11938894796149558950611755)
            ·
              refine ⟨17908342194224338425917633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11938894796149558950611755 17908342194224338425917633)
              ·
                refine ⟨13431256645668253819438225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17908342194224338425917633 13431256645668253819438225)
                ·
                  refine ⟨10073442484251190364578669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13431256645668253819438225 10073442484251190364578669)
                  ·
                    refine ⟨3777540931594196386717001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10073442484251190364578669 3777540931594196386717001)
                    ·
                      refine ⟨2833155698695647290037751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777540931594196386717001 2833155698695647290037751)
                      ·
                        rfl

theorem cell23_5517551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 3, 2].length) (baseStart_5517551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517551 prefixEnd_5517551 := by exact prefixLift 5517551
  have htrace : WordTrace (prefixWord ++ tailWord_5517551) baseStart_5517551 baseEnd_5517551 := by
    simpa [prefixWord, tailWord_5517551, baseEnd_5517551] using wordTrace_append hprefix tailTrace_5517551
  have hstable : (prefixWord ++ tailWord_5517551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517551).length < 2 ^ (prefixWord ++ tailWord_5517551).sum := by decide
  have hdescent : baseEnd_5517551 < baseStart_5517551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517558 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5517558 : Nat := 118140960795 + 5517558 * 2 ^ 59
def prefixEnd_5517558 : Nat := 4983230072969 + 3 ^ 40 * 5517558 * 2
def baseEnd_5517558 : Nat := 2833159293060228762650219

theorem tailTrace_5517558 : CollatzResearch.WordTrace tailWord_5517558 prefixEnd_5517558 2833159293060228762650219 := by
  unfold tailWord_5517558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577617059052322795579583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134161248629891443152848885 12577617059052322795579583)
  ·
    refine ⟨18866425588578484193369375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12577617059052322795579583 18866425588578484193369375)
    ·
      refine ⟨28299638382867726290054063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18866425588578484193369375 28299638382867726290054063)
      ·
        refine ⟨42449457574301589435081095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28299638382867726290054063 42449457574301589435081095)
        ·
          refine ⟨63674186361452384152621643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42449457574301589435081095 63674186361452384152621643)
          ·
            refine ⟨95511279542178576228932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63674186361452384152621643 95511279542178576228932465)
            ·
              refine ⟨71633459656633932171699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95511279542178576228932465 71633459656633932171699349)
              ·
                refine ⟨3357818421404715570548407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71633459656633932171699349 3357818421404715570548407)
                ·
                  refine ⟨5036727632107073355822611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357818421404715570548407 5036727632107073355822611)
                  ·
                    refine ⟨7555091448160610033733917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036727632107073355822611 7555091448160610033733917)
                    ·
                      refine ⟨2833159293060228762650219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7555091448160610033733917 2833159293060228762650219)
                      ·
                        rfl

theorem cell23_5517558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5517558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517558 prefixEnd_5517558 := by exact prefixLift 5517558
  have htrace : WordTrace (prefixWord ++ tailWord_5517558) baseStart_5517558 baseEnd_5517558 := by
    simpa [prefixWord, tailWord_5517558, baseEnd_5517558] using wordTrace_append hprefix tailTrace_5517558
  have hstable : (prefixWord ++ tailWord_5517558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517558).length < 2 ^ (prefixWord ++ tailWord_5517558).sum := by decide
  have hdescent : baseEnd_5517558 < baseStart_5517558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517567 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_5517567 : Nat := 118140960795 + 5517567 * 2 ^ 59
def prefixEnd_5517567 : Nat := 4983230072969 + 3 ^ 40 * 5517567 * 2
def baseEnd_5517567 : Nat := 2833163914386119227437677

theorem tailTrace_5517567 : CollatzResearch.WordTrace tailWord_5517567 prefixEnd_5517567 2833163914386119227437677 := by
  unfold tailWord_5517567
  simp only [CollatzResearch.WordTrace]
  refine ⟨201242201201804559266350955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134161467467869706177567303 201242201201804559266350955)
  ·
    refine ⟨301863301802706838899526433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201242201201804559266350955 301863301802706838899526433)
    ·
      refine ⟨226397476352030129174644825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301863301802706838899526433 226397476352030129174644825)
      ·
        refine ⟨169798107264022596880983619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226397476352030129174644825 169798107264022596880983619)
        ·
          refine ⟨254697160896033895321475429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169798107264022596880983619 254697160896033895321475429)
          ·
            refine ⟨47755717668006355372776643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254697160896033895321475429 47755717668006355372776643)
            ·
              refine ⟨71633576502009533059164965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47755717668006355372776643 71633576502009533059164965)
              ·
                refine ⟨13431295594126787448593431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71633576502009533059164965 13431295594126787448593431)
                ·
                  refine ⟨20146943391190181172890147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13431295594126787448593431 20146943391190181172890147)
                  ·
                    refine ⟨30220415086785271759335221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20146943391190181172890147 30220415086785271759335221)
                    ·
                      refine ⟨2833163914386119227437677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30220415086785271759335221 2833163914386119227437677)
                      ·
                        rfl

theorem cell23_5517567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_5517567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517567 prefixEnd_5517567 := by exact prefixLift 5517567
  have htrace : WordTrace (prefixWord ++ tailWord_5517567) baseStart_5517567 baseEnd_5517567 := by
    simpa [prefixWord, tailWord_5517567, baseEnd_5517567] using wordTrace_append hprefix tailTrace_5517567
  have hstable : (prefixWord ++ tailWord_5517567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517567).length < 2 ^ (prefixWord ++ tailWord_5517567).sum := by decide
  have hdescent : baseEnd_5517567 < baseStart_5517567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517577 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_5517577 : Nat := 118140960795 + 5517577 * 2 ^ 59
def prefixEnd_5517577 : Nat := 4983230072969 + 3 ^ 40 * 5517577 * 2
def baseEnd_5517577 : Nat := 2833169049192664188312631

theorem tailTrace_5517577 : CollatzResearch.WordTrace tailWord_5517577 prefixEnd_5517577 2833169049192664188312631 := by
  unfold tailWord_5517577
  simp only [CollatzResearch.WordTrace]
  refine ⟨201242565931768330974214985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134161710621178887316143323 201242565931768330974214985)
  ·
    refine ⟨150931924448826248230661239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201242565931768330974214985 150931924448826248230661239)
    ·
      refine ⟨226397886673239372345991859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150931924448826248230661239 226397886673239372345991859)
      ·
        refine ⟨339596830009859058518987789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226397886673239372345991859 339596830009859058518987789)
        ·
          refine ⟨127348811253697146944620421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339596830009859058518987789 127348811253697146944620421)
          ·
            refine ⟨23877902110068215052116329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127348811253697146944620421 23877902110068215052116329)
            ·
              refine ⟨17908426582551161289087247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23877902110068215052116329 17908426582551161289087247)
              ·
                refine ⟨26862639873826741933630871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17908426582551161289087247 26862639873826741933630871)
                ·
                  refine ⟨40293959810740112900446307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26862639873826741933630871 40293959810740112900446307)
                  ·
                    refine ⟨60440939716110169350669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40293959810740112900446307 60440939716110169350669461)
                    ·
                      refine ⟨2833169049192664188312631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60440939716110169350669461 2833169049192664188312631)
                      ·
                        rfl

theorem cell23_5517577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_5517577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517577 prefixEnd_5517577 := by exact prefixLift 5517577
  have htrace : WordTrace (prefixWord ++ tailWord_5517577) baseStart_5517577 baseEnd_5517577 := by
    simpa [prefixWord, tailWord_5517577, baseEnd_5517577] using wordTrace_append hprefix tailTrace_5517577
  have hstable : (prefixWord ++ tailWord_5517577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517577).length < 2 ^ (prefixWord ++ tailWord_5517577).sum := by decide
  have hdescent : baseEnd_5517577 < baseStart_5517577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517608 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5517608 : Nat := 118140960795 + 5517608 * 2 ^ 59
def prefixEnd_5517608 : Nat := 4983230072969 + 3 ^ 40 * 5517608 * 2
def baseEnd_5517608 : Nat := 944394989030984522341663

theorem tailTrace_5517608 : CollatzResearch.WordTrace tailWord_5517608 prefixEnd_5517608 944394989030984522341663 := by
  unfold tailWord_5517608
  simp only [CollatzResearch.WordTrace]
  refine ⟨100621848297328011634296739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134162464396437348845728985 100621848297328011634296739)
  ·
    refine ⟨150932772445992017451445109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100621848297328011634296739 150932772445992017451445109)
    ·
      refine ⟨14149947416811751636072979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150932772445992017451445109 14149947416811751636072979)
      ·
        refine ⟨21224921125217627454109469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14149947416811751636072979 21224921125217627454109469)
        ·
          refine ⟨7959345421956610295291051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21224921125217627454109469 7959345421956610295291051)
          ·
            refine ⟨11939018132934915442936577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959345421956610295291051 11939018132934915442936577)
            ·
              refine ⟨8954263599701186582202433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11939018132934915442936577 8954263599701186582202433)
              ·
                refine ⟨6715697699775889936651825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8954263599701186582202433 6715697699775889936651825)
                ·
                  refine ⟨5036773274831917452488869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715697699775889936651825 5036773274831917452488869)
                  ·
                    refine ⟨944394989030984522341663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5036773274831917452488869 944394989030984522341663)
                    ·
                      rfl

theorem cell23_5517608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5517608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517608 prefixEnd_5517608 := by exact prefixLift 5517608
  have htrace : WordTrace (prefixWord ++ tailWord_5517608) baseStart_5517608 baseEnd_5517608 := by
    simpa [prefixWord, tailWord_5517608, baseEnd_5517608] using wordTrace_append hprefix tailTrace_5517608
  have hstable : (prefixWord ++ tailWord_5517608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517608).length < 2 ^ (prefixWord ++ tailWord_5517608).sum := by decide
  have hdescent : baseEnd_5517608 < baseStart_5517608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517615 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 1, 2, 2]
def baseStart_5517615 : Nat := 118140960795 + 5517615 * 2 ^ 59
def prefixEnd_5517615 : Nat := 4983230072969 + 3 ^ 40 * 5517615 * 2
def baseEnd_5517615 : Nat := 2833188561457535039637457

theorem tailTrace_5517615 : CollatzResearch.WordTrace tailWord_5517615 prefixEnd_5517615 2833188561457535039637457 := by
  unfold tailWord_5517615
  simp only [CollatzResearch.WordTrace]
  refine ⟨201243951905630663464098299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134162634603753775642732199 201243951905630663464098299)
  ·
    refine ⟨301865927858445995196147449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201243951905630663464098299 301865927858445995196147449)
    ·
      refine ⟨226399445893834496397110587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301865927858445995196147449 226399445893834496397110587)
      ·
        refine ⟨339599168840751744595665881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226399445893834496397110587 339599168840751744595665881)
        ·
          refine ⟨254699376630563808446749411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339599168840751744595665881 254699376630563808446749411)
          ·
            refine ⟨382049064945845712670124117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254699376630563808446749411 382049064945845712670124117)
            ·
              refine ⟨4477137479834129445353017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 382049064945845712670124117 4477137479834129445353017)
              ·
                refine ⟨3357853109875597084014763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477137479834129445353017 3357853109875597084014763)
                ·
                  refine ⟨5036779664813395626022145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357853109875597084014763 5036779664813395626022145)
                  ·
                    refine ⟨3777584748610046719516609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036779664813395626022145 3777584748610046719516609)
                    ·
                      refine ⟨2833188561457535039637457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777584748610046719516609 2833188561457535039637457)
                      ·
                        rfl

theorem cell23_5517615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 2, 2].length) (baseStart_5517615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517615 prefixEnd_5517615 := by exact prefixLift 5517615
  have htrace : WordTrace (prefixWord ++ tailWord_5517615) baseStart_5517615 baseEnd_5517615 := by
    simpa [prefixWord, tailWord_5517615, baseEnd_5517615] using wordTrace_append hprefix tailTrace_5517615
  have hstable : (prefixWord ++ tailWord_5517615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517615).length < 2 ^ (prefixWord ++ tailWord_5517615).sum := by decide
  have hdescent : baseEnd_5517615 < baseStart_5517615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517631 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_5517631 : Nat := 118140960795 + 5517631 * 2 ^ 59
def prefixEnd_5517631 : Nat := 4983230072969 + 3 ^ 40 * 5517631 * 2
def baseEnd_5517631 : Nat := 2833196777148006977037383

theorem tailTrace_5517631 : CollatzResearch.WordTrace tailWord_5517631 prefixEnd_5517631 2833196777148006977037383 := by
  unfold tailWord_5517631
  simp only [CollatzResearch.WordTrace]
  refine ⟨201244535473572698196680747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134163023649048465464453831 201244535473572698196680747)
  ·
    refine ⟨301866803210359047295021121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201244535473572698196680747 301866803210359047295021121)
    ·
      refine ⟨226400102407769285471265841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301866803210359047295021121 226400102407769285471265841)
      ·
        refine ⟨169800076805826964103449381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226400102407769285471265841 169800076805826964103449381)
        ·
          refine ⟨31837514401092555769396759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169800076805826964103449381 31837514401092555769396759)
          ·
            refine ⟨47756271601638833654095139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31837514401092555769396759 47756271601638833654095139)
            ·
              refine ⟨71634407402458250481142709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47756271601638833654095139 71634407402458250481142709)
              ·
                refine ⟨6715725693980460982607129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71634407402458250481142709 6715725693980460982607129)
                ·
                  refine ⟨5036794270485345736955347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715725693980460982607129 5036794270485345736955347)
                  ·
                    refine ⟨7555191405728018605433021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036794270485345736955347 7555191405728018605433021)
                    ·
                      refine ⟨2833196777148006977037383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7555191405728018605433021 2833196777148006977037383)
                      ·
                        rfl

theorem cell23_5517631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_5517631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517631 prefixEnd_5517631 := by exact prefixLift 5517631
  have htrace : WordTrace (prefixWord ++ tailWord_5517631) baseStart_5517631 baseEnd_5517631 := by
    simpa [prefixWord, tailWord_5517631, baseEnd_5517631] using wordTrace_append hprefix tailTrace_5517631
  have hstable : (prefixWord ++ tailWord_5517631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517631).length < 2 ^ (prefixWord ++ tailWord_5517631).sum := by decide
  have hdescent : baseEnd_5517631 < baseStart_5517631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517641 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 1, 3, 2]
def baseStart_5517641 : Nat := 118140960795 + 5517641 * 2 ^ 59
def prefixEnd_5517641 : Nat := 4983230072969 + 3 ^ 40 * 5517641 * 2
def baseEnd_5517641 : Nat := 2833201911954551937912337

theorem tailTrace_5517641 : CollatzResearch.WordTrace tailWord_5517641 prefixEnd_5517641 2833201911954551937912337 := by
  unfold tailWord_5517641
  simp only [CollatzResearch.WordTrace]
  refine ⟨201244900203536469904544777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134163266802357646603029851 201244900203536469904544777)
  ·
    refine ⟨150933675152652352428408583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201244900203536469904544777 150933675152652352428408583)
    ·
      refine ⟨226400512728978528642612875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150933675152652352428408583 226400512728978528642612875)
      ·
        refine ⟨339600769093467792963919313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226400512728978528642612875 339600769093467792963919313)
        ·
          refine ⟨254700576820100844722939485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339600769093467792963919313 254700576820100844722939485)
          ·
            refine ⟨95512716307537816771102307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254700576820100844722939485 95512716307537816771102307)
            ·
              refine ⟨143269074461306725156653461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95512716307537816771102307 143269074461306725156653461)
              ·
                refine ⟨6715737865373752741718131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143269074461306725156653461 6715737865373752741718131)
                ·
                  refine ⟨10073606798060629112577197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6715737865373752741718131 10073606798060629112577197)
                  ·
                    refine ⟨3777602549272735917216449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10073606798060629112577197 3777602549272735917216449)
                    ·
                      refine ⟨2833201911954551937912337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777602549272735917216449 2833201911954551937912337)
                      ·
                        rfl

theorem cell23_5517641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 3, 2].length) (baseStart_5517641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517641 prefixEnd_5517641 := by exact prefixLift 5517641
  have htrace : WordTrace (prefixWord ++ tailWord_5517641) baseStart_5517641 baseEnd_5517641 := by
    simpa [prefixWord, tailWord_5517641, baseEnd_5517641] using wordTrace_append hprefix tailTrace_5517641
  have hstable : (prefixWord ++ tailWord_5517641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517641).length < 2 ^ (prefixWord ++ tailWord_5517641).sum := by decide
  have hdescent : baseEnd_5517641 < baseStart_5517641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517657 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_5517657 : Nat := 118140960795 + 5517657 * 2 ^ 59
def prefixEnd_5517657 : Nat := 4983230072969 + 3 ^ 40 * 5517657 * 2
def baseEnd_5517657 : Nat := 2833210127645023875312263

theorem tailTrace_5517657 : CollatzResearch.WordTrace tailWord_5517657 prefixEnd_5517657 2833210127645023875312263 := by
  unfold tailWord_5517657
  simp only [CollatzResearch.WordTrace]
  refine ⟨201245483771478504637127225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134163655847652336424751483 201245483771478504637127225)
  ·
    refine ⟨150934112828608878477845419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201245483771478504637127225 150934112828608878477845419)
    ·
      refine ⟨226401169242913317716768129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150934112828608878477845419 226401169242913317716768129)
      ·
        refine ⟨169800876932184988287576097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226401169242913317716768129 169800876932184988287576097)
        ·
          refine ⟨127350657699138741215682073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169800876932184988287576097 127350657699138741215682073)
          ·
            refine ⟨95512993274354055911761555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127350657699138741215682073 95512993274354055911761555)
            ·
              refine ⟨143269489911531083867642333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95512993274354055911761555 143269489911531083867642333)
              ·
                refine ⟨53726058716824156450365875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143269489911531083867642333 53726058716824156450365875)
                ·
                  refine ⟨80589088075236234675548813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53726058716824156450365875 80589088075236234675548813)
                  ·
                    refine ⟨30220908028213588003330805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80589088075236234675548813 30220908028213588003330805)
                    ·
                      refine ⟨2833210127645023875312263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30220908028213588003330805 2833210127645023875312263)
                      ·
                        rfl

theorem cell23_5517657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_5517657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517657 prefixEnd_5517657 := by exact prefixLift 5517657
  have htrace : WordTrace (prefixWord ++ tailWord_5517657) baseStart_5517657 baseEnd_5517657 := by
    simpa [prefixWord, tailWord_5517657, baseEnd_5517657] using wordTrace_append hprefix tailTrace_5517657
  have hstable : (prefixWord ++ tailWord_5517657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517657).length < 2 ^ (prefixWord ++ tailWord_5517657).sum := by decide
  have hdescent : baseEnd_5517657 < baseStart_5517657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517728 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 5]
def baseStart_5517728 : Nat := 118140960795 + 5517728 * 2 ^ 59
def prefixEnd_5517728 : Nat := 4983230072969 + 3 ^ 40 * 5517728 * 2
def baseEnd_5517728 : Nat := 314805176085721455280493

theorem tailTrace_5517728 : CollatzResearch.WordTrace tailWord_5517728 prefixEnd_5517728 314805176085721455280493 := by
  unfold tailWord_5517728
  simp only [CollatzResearch.WordTrace]
  refine ⟨100624036677110641881480919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134165382236147522508641225 100624036677110641881480919)
  ·
    refine ⟨150936055015665962822221379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100624036677110641881480919 150936055015665962822221379)
    ·
      refine ⟨226404082523498944233332069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150936055015665962822221379 226404082523498944233332069)
      ·
        refine ⟨42450765473156052043749763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226404082523498944233332069 42450765473156052043749763)
        ·
          refine ⟨63676148209734078065624645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42450765473156052043749763 63676148209734078065624645)
          ·
            refine ⟨11939277789325139637304621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63676148209734078065624645 11939277789325139637304621)
            ·
              refine ⟨4477229170996927363989233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11939277789325139637304621 4477229170996927363989233)
              ·
                refine ⟨3357921878247695522991925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477229170996927363989233 3357921878247695522991925)
                ·
                  refine ⟨314805176085721455280493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357921878247695522991925 314805176085721455280493)
                  ·
                    rfl

theorem cell23_5517728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 5].length) (baseStart_5517728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517728 prefixEnd_5517728 := by exact prefixLift 5517728
  have htrace : WordTrace (prefixWord ++ tailWord_5517728) baseStart_5517728 baseEnd_5517728 := by
    simpa [prefixWord, tailWord_5517728, baseEnd_5517728] using wordTrace_append hprefix tailTrace_5517728
  have hstable : (prefixWord ++ tailWord_5517728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517728).length < 2 ^ (prefixWord ++ tailWord_5517728).sum := by decide
  have hdescent : baseEnd_5517728 < baseStart_5517728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517774 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5517774 : Nat := 118140960795 + 5517774 * 2 ^ 59
def prefixEnd_5517774 : Nat := 4983230072969 + 3 ^ 40 * 5517774 * 2
def baseEnd_5517774 : Nat := 2833270204881599917549225

theorem tailTrace_5517774 : CollatzResearch.WordTrace tailWord_5517774 prefixEnd_5517774 2833270204881599917549225 := by
  unfold tailWord_5517774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25156218889006829202392047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134166500741369755746090917 25156218889006829202392047)
  ·
    refine ⟨37734328333510243803588071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25156218889006829202392047 37734328333510243803588071)
    ·
      refine ⟨56601492500265365705382107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37734328333510243803588071 56601492500265365705382107)
      ·
        refine ⟨84902238750398048558073161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56601492500265365705382107 84902238750398048558073161)
        ·
          refine ⟨63676679062798536418554871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84902238750398048558073161 63676679062798536418554871)
          ·
            refine ⟨95515018594197804627832307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63676679062798536418554871 95515018594197804627832307)
            ·
              refine ⟨143272527891296706941748461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95515018594197804627832307 143272527891296706941748461)
              ·
                refine ⟨53727197959236265103155673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143272527891296706941748461 53727197959236265103155673)
                ·
                  refine ⟨40295398469427198827366755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53727197959236265103155673 40295398469427198827366755)
                  ·
                    refine ⟨60443097704140798241050133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40295398469427198827366755 60443097704140798241050133)
                    ·
                      refine ⟨2833270204881599917549225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60443097704140798241050133 2833270204881599917549225)
                      ·
                        rfl

theorem cell23_5517774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5517774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517774 prefixEnd_5517774 := by exact prefixLift 5517774
  have htrace : WordTrace (prefixWord ++ tailWord_5517774) baseStart_5517774 baseEnd_5517774 := by
    simpa [prefixWord, tailWord_5517774, baseEnd_5517774] using wordTrace_append hprefix tailTrace_5517774
  have hstable : (prefixWord ++ tailWord_5517774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517774).length < 2 ^ (prefixWord ++ tailWord_5517774).sum := by decide
  have hdescent : baseEnd_5517774 < baseStart_5517774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517845 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_5517845 : Nat := 118140960795 + 5517845 * 2 ^ 59
def prefixEnd_5517845 : Nat := 4983230072969 + 3 ^ 40 * 5517845 * 2
def baseEnd_5517845 : Nat := 2833306662008069139761399

theorem tailTrace_5517845 : CollatzResearch.WordTrace tailWord_5517845 prefixEnd_5517845 2833306662008069139761399 := by
  unfold tailWord_5517845
  simp only [CollatzResearch.WordTrace]
  refine ⟨201252340694797412744970989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134168227129864941829980659 201252340694797412744970989)
  ·
    refine ⟨75469627760549029779364121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201252340694797412744970989 75469627760549029779364121)
    ·
      refine ⟨56602220820411772334523091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75469627760549029779364121 56602220820411772334523091)
      ·
        refine ⟨84903331230617658501784637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56602220820411772334523091 84903331230617658501784637)
        ·
          refine ⟨31838749211481621938169239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84903331230617658501784637 31838749211481621938169239)
          ·
            refine ⟨47758123817222432907253859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31838749211481621938169239 47758123817222432907253859)
            ·
              refine ⟨71637185725833649360880789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47758123817222432907253859 71637185725833649360880789)
              ·
                refine ⟨3357993080898452313791287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71637185725833649360880789 3357993080898452313791287)
                ·
                  refine ⟨5036989621347678470686931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3357993080898452313791287 5036989621347678470686931)
                  ·
                    refine ⟨7555484432021517706030397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5036989621347678470686931 7555484432021517706030397)
                    ·
                      refine ⟨2833306662008069139761399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7555484432021517706030397 2833306662008069139761399)
                      ·
                        rfl

theorem cell23_5517845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_5517845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517845 prefixEnd_5517845 := by exact prefixLift 5517845
  have htrace : WordTrace (prefixWord ++ tailWord_5517845) baseStart_5517845 baseEnd_5517845 := by
    simpa [prefixWord, tailWord_5517845, baseEnd_5517845] using wordTrace_append hprefix tailTrace_5517845
  have hstable : (prefixWord ++ tailWord_5517845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517845).length < 2 ^ (prefixWord ++ tailWord_5517845).sum := by decide
  have hdescent : baseEnd_5517845 < baseStart_5517845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517861 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_5517861 : Nat := 118140960795 + 5517861 * 2 ^ 59
def prefixEnd_5517861 : Nat := 4983230072969 + 3 ^ 40 * 5517861 * 2
def baseEnd_5517861 : Nat := 944438292566180359053775

theorem tailTrace_5517861 : CollatzResearch.WordTrace tailWord_5517861 prefixEnd_5517861 944438292566180359053775 := by
  unfold tailWord_5517861
  simp only [CollatzResearch.WordTrace]
  refine ⟨201252924262739447477553437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134168616175159631651702291 201252924262739447477553437)
  ·
    refine ⟨75469846598527292804082539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201252924262739447477553437 75469846598527292804082539)
    ·
      refine ⟨113204769897790939206123809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75469846598527292804082539 113204769897790939206123809)
      ·
        refine ⟨84903577423343204404592857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113204769897790939206123809 84903577423343204404592857)
        ·
          refine ⟨63677683067507403303444643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84903577423343204404592857 63677683067507403303444643)
          ·
            refine ⟨95516524601261104955166965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63677683067507403303444643 95516524601261104955166965)
            ·
              refine ⟨8954674181368228589546903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95516524601261104955166965 8954674181368228589546903)
              ·
                refine ⟨13432011272052342884320355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8954674181368228589546903 13432011272052342884320355)
                ·
                  refine ⟨20148016908078514326480533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13432011272052342884320355 20148016908078514326480533)
                  ·
                    refine ⟨944438292566180359053775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20148016908078514326480533 944438292566180359053775)
                    ·
                      rfl

theorem cell23_5517861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_5517861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517861 prefixEnd_5517861 := by exact prefixLift 5517861
  have htrace : WordTrace (prefixWord ++ tailWord_5517861) baseStart_5517861 baseEnd_5517861 := by
    simpa [prefixWord, tailWord_5517861, baseEnd_5517861] using wordTrace_append hprefix tailTrace_5517861
  have hstable : (prefixWord ++ tailWord_5517861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517861).length < 2 ^ (prefixWord ++ tailWord_5517861).sum := by decide
  have hdescent : baseEnd_5517861 < baseStart_5517861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517881 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5517881 : Nat := 118140960795 + 5517881 * 2 ^ 59
def prefixEnd_5517881 : Nat := 4983230072969 + 3 ^ 40 * 5517881 * 2
def baseEnd_5517881 : Nat := 2833325147311630998911233

theorem tailTrace_5517881 : CollatzResearch.WordTrace tailWord_5517881 prefixEnd_5517881 2833325147311630998911233 := by
  unfold tailWord_5517881
  simp only [CollatzResearch.WordTrace]
  refine ⟨201253653722666990893281497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134169102481777993928854331 201253653722666990893281497)
  ·
    refine ⟨150940240292000243169961123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201253653722666990893281497 150940240292000243169961123)
    ·
      refine ⟨226410360438000364754941685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150940240292000243169961123 226410360438000364754941685)
      ·
        refine ⟨21225971291062534195775783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226410360438000364754941685 21225971291062534195775783)
        ·
          refine ⟨31838956936593801293663675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21225971291062534195775783 31838956936593801293663675)
          ·
            refine ⟨47758435404890701940495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31838956936593801293663675 47758435404890701940495513)
            ·
              refine ⟨35818826553668026455371635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47758435404890701940495513 35818826553668026455371635)
              ·
                refine ⟨53728239830502039683057453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35818826553668026455371635 53728239830502039683057453)
                ·
                  refine ⟨20148089936438264881146545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53728239830502039683057453 20148089936438264881146545)
                  ·
                    refine ⟨15111067452328698660859909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20148089936438264881146545 15111067452328698660859909)
                    ·
                      refine ⟨2833325147311630998911233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15111067452328698660859909 2833325147311630998911233)
                      ·
                        rfl

theorem cell23_5517881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5517881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517881 prefixEnd_5517881 := by exact prefixLift 5517881
  have htrace : WordTrace (prefixWord ++ tailWord_5517881) baseStart_5517881 baseEnd_5517881 := by
    simpa [prefixWord, tailWord_5517881, baseEnd_5517881] using wordTrace_append hprefix tailTrace_5517881
  have hstable : (prefixWord ++ tailWord_5517881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517881).length < 2 ^ (prefixWord ++ tailWord_5517881).sum := by decide
  have hdescent : baseEnd_5517881 < baseStart_5517881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517888 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_5517888 : Nat := 118140960795 + 5517888 * 2 ^ 59
def prefixEnd_5517888 : Nat := 4983230072969 + 3 ^ 40 * 5517888 * 2
def baseEnd_5517888 : Nat := 2833328741676212471523701

theorem tailTrace_5517888 : CollatzResearch.WordTrace tailWord_5517888 prefixEnd_5517888 2833328741676212471523701 := by
  unfold tailWord_5517888
  simp only [CollatzResearch.WordTrace]
  refine ⟨100626954516820815544393159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134169272689094420725857545 100626954516820815544393159)
  ·
    refine ⟨150940431775231223316589739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100626954516820815544393159 150940431775231223316589739)
    ·
      refine ⟨226410647662846834974884609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150940431775231223316589739 226410647662846834974884609)
      ·
        refine ⟨169807985747135126231163457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226410647662846834974884609 169807985747135126231163457)
        ·
          refine ⟨127355989310351344673372593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169807985747135126231163457 127355989310351344673372593)
          ·
            refine ⟨95516991982763508505029445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127355989310351344673372593 95516991982763508505029445)
            ·
              refine ⟨17909435996768157844693021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95516991982763508505029445 17909435996768157844693021)
              ·
                refine ⟨6716038498788059191759883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17909435996768157844693021 6716038498788059191759883)
                ·
                  refine ⟨10074057748182088787639825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716038498788059191759883 10074057748182088787639825)
                  ·
                    refine ⟨7555543311136566590729869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10074057748182088787639825 7555543311136566590729869)
                    ·
                      refine ⟨2833328741676212471523701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7555543311136566590729869 2833328741676212471523701)
                      ·
                        rfl

theorem cell23_5517888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_5517888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517888 prefixEnd_5517888 := by exact prefixLift 5517888
  have htrace : WordTrace (prefixWord ++ tailWord_5517888) baseStart_5517888 baseEnd_5517888 := by
    simpa [prefixWord, tailWord_5517888, baseEnd_5517888] using wordTrace_append hprefix tailTrace_5517888
  have hstable : (prefixWord ++ tailWord_5517888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517888).length < 2 ^ (prefixWord ++ tailWord_5517888).sum := by decide
  have hdescent : baseEnd_5517888 < baseStart_5517888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517902 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_5517902 : Nat := 118140960795 + 5517902 * 2 ^ 59
def prefixEnd_5517902 : Nat := 4983230072969 + 3 ^ 40 * 5517902 * 2
def baseEnd_5517902 : Nat := 2833335930405375416748637

theorem tailTrace_5517902 : CollatzResearch.WordTrace tailWord_5517902 prefixEnd_5517902 2833335930405375416748637 := by
  unfold tailWord_5517902
  simp only [CollatzResearch.WordTrace]
  refine ⟨25156802456948863934974495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134169613103727274319863973 25156802456948863934974495)
  ·
    refine ⟨37735203685423295902461743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25156802456948863934974495 37735203685423295902461743)
    ·
      refine ⟨56602805528134943853692615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37735203685423295902461743 56602805528134943853692615)
      ·
        refine ⟨84904208292202415780538923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56602805528134943853692615 84904208292202415780538923)
        ·
          refine ⟨127356312438303623670808385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84904208292202415780538923 127356312438303623670808385)
          ·
            refine ⟨95517234328727717753106289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127356312438303623670808385 95517234328727717753106289)
            ·
              refine ⟨71637925746545788314829717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95517234328727717753106289 71637925746545788314829717)
              ·
                refine ⟨3358027769369333827257643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71637925746545788314829717 3358027769369333827257643)
                ·
                  refine ⟨5037041654054000740886465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358027769369333827257643 5037041654054000740886465)
                  ·
                    refine ⟨3777781240540500555664849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5037041654054000740886465 3777781240540500555664849)
                    ·
                      refine ⟨2833335930405375416748637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777781240540500555664849 2833335930405375416748637)
                      ·
                        rfl

theorem cell23_5517902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_5517902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517902 prefixEnd_5517902 := by exact prefixLift 5517902
  have htrace : WordTrace (prefixWord ++ tailWord_5517902) baseStart_5517902 baseEnd_5517902 := by
    simpa [prefixWord, tailWord_5517902, baseEnd_5517902] using wordTrace_append hprefix tailTrace_5517902
  have hstable : (prefixWord ++ tailWord_5517902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517902).length < 2 ^ (prefixWord ++ tailWord_5517902).sum := by decide
  have hdescent : baseEnd_5517902 < baseStart_5517902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517922 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5517922 : Nat := 118140960795 + 5517922 * 2 ^ 59
def prefixEnd_5517922 : Nat := 4983230072969 + 3 ^ 40 * 5517922 * 2
def baseEnd_5517922 : Nat := 2833346200018465338498545

theorem tailTrace_5517922 : CollatzResearch.WordTrace tailWord_5517922 prefixEnd_5517922 2833346200018465338498545 := by
  unfold tailWord_5517922
  simp only [CollatzResearch.WordTrace]
  refine ⟨50313787278879613723881005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134170099410345636597016013 50313787278879613723881005)
  ·
    refine ⟨18867670229579855146455377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50313787278879613723881005 18867670229579855146455377)
    ·
      refine ⟨14150752672184891359841533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18867670229579855146455377 14150752672184891359841533)
      ·
        refine ⟨5306532252069334259940575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14150752672184891359841533 5306532252069334259940575)
        ·
          refine ⟨7959798378104001389910863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306532252069334259940575 7959798378104001389910863)
          ·
            refine ⟨11939697567156002084866295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7959798378104001389910863 11939697567156002084866295)
            ·
              refine ⟨17909546350734003127299443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11939697567156002084866295 17909546350734003127299443)
              ·
                refine ⟨26864319526101004690949165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17909546350734003127299443 26864319526101004690949165)
                ·
                  refine ⟨10074119822287876759105937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26864319526101004690949165 10074119822287876759105937)
                  ·
                    refine ⟨7555589866715907569329453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10074119822287876759105937 7555589866715907569329453)
                    ·
                      refine ⟨2833346200018465338498545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7555589866715907569329453 2833346200018465338498545)
                      ·
                        rfl

theorem cell23_5517922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5517922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517922 prefixEnd_5517922 := by exact prefixLift 5517922
  have htrace : WordTrace (prefixWord ++ tailWord_5517922) baseStart_5517922 baseEnd_5517922 := by
    simpa [prefixWord, tailWord_5517922, baseEnd_5517922] using wordTrace_append hprefix tailTrace_5517922
  have hstable : (prefixWord ++ tailWord_5517922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517922).length < 2 ^ (prefixWord ++ tailWord_5517922).sum := by decide
  have hdescent : baseEnd_5517922 < baseStart_5517922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517971 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_5517971 : Nat := 118140960795 + 5517971 * 2 ^ 59
def prefixEnd_5517971 : Nat := 4983230072969 + 3 ^ 40 * 5517971 * 2
def baseEnd_5517971 : Nat := 2833371360570535646785819

theorem tailTrace_5517971 : CollatzResearch.WordTrace tailWord_5517971 prefixEnd_5517971 2833371360570535646785819 := by
  unfold tailWord_5517971
  simp only [CollatzResearch.WordTrace]
  refine ⟨201256936292340936264057767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134171290861560624176038511 201256936292340936264057767)
  ·
    refine ⟨301885404438511404396086651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201256936292340936264057767 301885404438511404396086651)
    ·
      refine ⟨452828106657767106594129977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301885404438511404396086651 452828106657767106594129977)
      ·
        refine ⟨339621079993325329945597483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452828106657767106594129977 339621079993325329945597483)
        ·
          refine ⟨509431619989987994918396225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339621079993325329945597483 509431619989987994918396225)
          ·
            refine ⟨382073714992490996188797169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509431619989987994918396225 382073714992490996188797169)
            ·
              refine ⟨286555286244368247141597877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382073714992490996188797169 286555286244368247141597877)
              ·
                refine ⟨26864558085409523169524801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286555286244368247141597877 26864558085409523169524801)
                ·
                  refine ⟨20148418564057142377143601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26864558085409523169524801 20148418564057142377143601)
                  ·
                    refine ⟨15111313923042856782857701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20148418564057142377143601 15111313923042856782857701)
                    ·
                      refine ⟨2833371360570535646785819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15111313923042856782857701 2833371360570535646785819)
                      ·
                        rfl

theorem cell23_5517971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_5517971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517971 prefixEnd_5517971 := by exact prefixLift 5517971
  have htrace : WordTrace (prefixWord ++ tailWord_5517971) baseStart_5517971 baseEnd_5517971 := by
    simpa [prefixWord, tailWord_5517971, baseEnd_5517971] using wordTrace_append hprefix tailTrace_5517971
  have hstable : (prefixWord ++ tailWord_5517971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517971).length < 2 ^ (prefixWord ++ tailWord_5517971).sum := by decide
  have hdescent : baseEnd_5517971 < baseStart_5517971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517975 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_5517975 : Nat := 118140960795 + 5517975 * 2 ^ 59
def prefixEnd_5517975 : Nat := 4983230072969 + 3 ^ 40 * 5517975 * 2
def baseEnd_5517975 : Nat := 2833373414493153631135801

theorem tailTrace_5517975 : CollatzResearch.WordTrace tailWord_5517975 prefixEnd_5517975 2833373414493153631135801 := by
  unfold tailWord_5517975
  simp only [CollatzResearch.WordTrace]
  refine ⟨201257082184326444947203379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134171388122884296631468919 201257082184326444947203379)
  ·
    refine ⟨301885623276489667420805069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201257082184326444947203379 301885623276489667420805069)
    ·
      refine ⟨113207108728683625282801901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301885623276489667420805069 113207108728683625282801901)
      ·
        refine ⟨42452665773256359481050713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113207108728683625282801901 42452665773256359481050713)
        ·
          refine ⟨31839499329942269610788035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42452665773256359481050713 31839499329942269610788035)
          ·
            refine ⟨47759248994913404416182053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31839499329942269610788035 47759248994913404416182053)
            ·
              refine ⟨8954859186546263328034135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47759248994913404416182053 8954859186546263328034135)
              ·
                refine ⟨13432288779819394992051203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8954859186546263328034135 13432288779819394992051203)
                ·
                  refine ⟨20148433169729092488076805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13432288779819394992051203 20148433169729092488076805)
                  ·
                    refine ⟨3777831219324204841514401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20148433169729092488076805 3777831219324204841514401)
                    ·
                      refine ⟨2833373414493153631135801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3777831219324204841514401 2833373414493153631135801)
                      ·
                        rfl

theorem cell23_5517975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_5517975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517975 prefixEnd_5517975 := by exact prefixLift 5517975
  have htrace : WordTrace (prefixWord ++ tailWord_5517975) baseStart_5517975 baseEnd_5517975 := by
    simpa [prefixWord, tailWord_5517975, baseEnd_5517975] using wordTrace_append hprefix tailTrace_5517975
  have hstable : (prefixWord ++ tailWord_5517975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517975).length < 2 ^ (prefixWord ++ tailWord_5517975).sum := by decide
  have hdescent : baseEnd_5517975 < baseStart_5517975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5517981 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 9]
def baseStart_5517981 : Nat := 118140960795 + 5517981 * 2 ^ 59
def prefixEnd_5517981 : Nat := 4983230072969 + 3 ^ 40 * 5517981 * 2
def baseEnd_5517981 : Nat := 314819610597453400851197

theorem tailTrace_5517981 : CollatzResearch.WordTrace tailWord_5517981 prefixEnd_5517981 314819610597453400851197 := by
  unfold tailWord_5517981
  simp only [CollatzResearch.WordTrace]
  refine ⟨201257301022304707971921797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134171534014869805314614531 201257301022304707971921797)
  ·
    refine ⟨37735743941682132744735337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201257301022304707971921797 37735743941682132744735337)
    ·
      refine ⟨28301807956261599558551503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37735743941682132744735337 28301807956261599558551503)
      ·
        refine ⟨42452711934392399337827255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28301807956261599558551503 42452711934392399337827255)
        ·
          refine ⟨63679067901588599006740883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42452711934392399337827255 63679067901588599006740883)
          ·
            refine ⟨95518601852382898510111325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63679067901588599006740883 95518601852382898510111325)
            ·
              refine ⟨35819475694643586941291747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95518601852382898510111325 35819475694643586941291747)
              ·
                refine ⟨53729213541965380411937621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35819475694643586941291747 53729213541965380411937621)
                ·
                  refine ⟨314819610597453400851197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53729213541965380411937621 314819610597453400851197)
                  ·
                    rfl

theorem cell23_5517981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_5517981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5517981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5517981 prefixEnd_5517981 := by exact prefixLift 5517981
  have htrace : WordTrace (prefixWord ++ tailWord_5517981) baseStart_5517981 baseEnd_5517981 := by
    simpa [prefixWord, tailWord_5517981, baseEnd_5517981] using wordTrace_append hprefix tailTrace_5517981
  have hstable : (prefixWord ++ tailWord_5517981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5517981).length < 2 ^ (prefixWord ++ tailWord_5517981).sum := by decide
  have hdescent : baseEnd_5517981 < baseStart_5517981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5517981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518028 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_5518028 : Nat := 118140960795 + 5518028 * 2 ^ 59
def prefixEnd_5518028 : Nat := 4983230072969 + 3 ^ 40 * 5518028 * 2
def baseEnd_5518028 : Nat := 944466876322613974591019

theorem tailTrace_5518028 : CollatzResearch.WordTrace tailWord_5518028 prefixEnd_5518028 944466876322613974591019 := by
  unfold tailWord_5518028
  simp only [CollatzResearch.WordTrace]
  refine ⟨100629507626567217499441369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134172676835422956665921825 100629507626567217499441369)
  ·
    refine ⟨75472130719925413124581027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100629507626567217499441369 75472130719925413124581027)
    ·
      refine ⟨113208196079888119686871541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75472130719925413124581027 113208196079888119686871541)
      ·
        refine ⟨10613268382489511220644207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113208196079888119686871541 10613268382489511220644207)
        ·
          refine ⟨15919902573734266830966311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613268382489511220644207 15919902573734266830966311)
          ·
            refine ⟨23879853860601400246449467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15919902573734266830966311 23879853860601400246449467)
            ·
              refine ⟨35819780790902100369674201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23879853860601400246449467 35819780790902100369674201)
              ·
                refine ⟨26864835593176575277255651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35819780790902100369674201 26864835593176575277255651)
                ·
                  refine ⟨40297253389764862915883477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26864835593176575277255651 40297253389764862915883477)
                  ·
                    refine ⟨944466876322613974591019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40297253389764862915883477 944466876322613974591019)
                    ·
                      rfl

theorem cell23_5518028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_5518028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518028 prefixEnd_5518028 := by exact prefixLift 5518028
  have htrace : WordTrace (prefixWord ++ tailWord_5518028) baseStart_5518028 baseEnd_5518028 := by
    simpa [prefixWord, tailWord_5518028, baseEnd_5518028] using wordTrace_append hprefix tailTrace_5518028
  have hstable : (prefixWord ++ tailWord_5518028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518028).length < 2 ^ (prefixWord ++ tailWord_5518028).sum := by decide
  have hdescent : baseEnd_5518028 < baseStart_5518028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518041 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 2, 8]
def baseStart_5518041 : Nat := 118140960795 + 5518041 * 2 ^ 59
def prefixEnd_5518041 : Nat := 4983230072969 + 3 ^ 40 * 5518041 * 2
def baseEnd_5518041 : Nat := 944469101405450124303499

theorem tailTrace_5518041 : CollatzResearch.WordTrace tailWord_5518041 prefixEnd_5518041 944469101405450124303499 := by
  unfold tailWord_5518041
  simp only [CollatzResearch.WordTrace]
  refine ⟨201259489402087338219105977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134172992934724892146070651 201259489402087338219105977)
  ·
    refine ⟨150944617051565503664329483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201259489402087338219105977 150944617051565503664329483)
    ·
      refine ⟨226416925577348255496494225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150944617051565503664329483 226416925577348255496494225)
      ·
        refine ⟨169812694183011191622370669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226416925577348255496494225 169812694183011191622370669)
        ·
          refine ⟨63679760318629196858389001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169812694183011191622370669 63679760318629196858389001)
          ·
            refine ⟨47759820238971897643791751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63679760318629196858389001 47759820238971897643791751)
            ·
              refine ⟨71639730358457846465687627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47759820238971897643791751 71639730358457846465687627)
              ·
                refine ⟨107459595537686769698531441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71639730358457846465687627 107459595537686769698531441)
                ·
                  refine ⟨80594696653265077273898581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107459595537686769698531441 80594696653265077273898581)
                  ·
                    refine ⟨944469101405450124303499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80594696653265077273898581 944469101405450124303499)
                    ·
                      rfl

theorem cell23_5518041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_5518041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518041 prefixEnd_5518041 := by exact prefixLift 5518041
  have htrace : WordTrace (prefixWord ++ tailWord_5518041) baseStart_5518041 baseEnd_5518041 := by
    simpa [prefixWord, tailWord_5518041, baseEnd_5518041] using wordTrace_append hprefix tailTrace_5518041
  have hstable : (prefixWord ++ tailWord_5518041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518041).length < 2 ^ (prefixWord ++ tailWord_5518041).sum := by decide
  have hdescent : baseEnd_5518041 < baseStart_5518041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518048 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_5518048 : Nat := 118140960795 + 5518048 * 2 ^ 59
def prefixEnd_5518048 : Nat := 4983230072969 + 3 ^ 40 * 5518048 * 2
def baseEnd_5518048 : Nat := 2833410898580931845522965

theorem tailTrace_5518048 : CollatzResearch.WordTrace tailWord_5518048 prefixEnd_5518048 2833410898580931845522965 := by
  unfold tailWord_5518048
  simp only [CollatzResearch.WordTrace]
  refine ⟨100629872356530989207305399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134173163142041318943073865 100629872356530989207305399)
  ·
    refine ⟨150944808534796483810958099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100629872356530989207305399 150944808534796483810958099)
    ·
      refine ⟨226417212802194725716437149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150944808534796483810958099 226417212802194725716437149)
      ·
        refine ⟨84906454800823022143663931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226417212802194725716437149 84906454800823022143663931)
        ·
          refine ⟨127359682201234533215495897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84906454800823022143663931 127359682201234533215495897)
          ·
            refine ⟨95519761650925899911621923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127359682201234533215495897 95519761650925899911621923)
            ·
              refine ⟨143279642476388849867432885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95519761650925899911621923 143279642476388849867432885)
              ·
                refine ⟨13432466482161454675071833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143279642476388849867432885 13432466482161454675071833)
                ·
                  refine ⟨10074349861621091006303875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13432466482161454675071833 10074349861621091006303875)
                  ·
                    refine ⟨15111524792431636509455813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10074349861621091006303875 15111524792431636509455813)
                    ·
                      refine ⟨2833410898580931845522965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15111524792431636509455813 2833410898580931845522965)
                      ·
                        rfl

theorem cell23_5518048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_5518048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518048 prefixEnd_5518048 := by exact prefixLift 5518048
  have htrace : WordTrace (prefixWord ++ tailWord_5518048) baseStart_5518048 baseEnd_5518048 := by
    simpa [prefixWord, tailWord_5518048, baseEnd_5518048] using wordTrace_append hprefix tailTrace_5518048
  have hstable : (prefixWord ++ tailWord_5518048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518048).length < 2 ^ (prefixWord ++ tailWord_5518048).sum := by decide
  have hdescent : baseEnd_5518048 < baseStart_5518048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518126 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5518126 : Nat := 118140960795 + 5518126 * 2 ^ 59
def prefixEnd_5518126 : Nat := 4983230072969 + 3 ^ 40 * 5518126 * 2
def baseEnd_5518126 : Nat := 944483650023994180115869

theorem tailTrace_5518126 : CollatzResearch.WordTrace tailWord_5518126 prefixEnd_5518126 944483650023994180115869 := by
  unfold tailWord_5518126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157823700847424716993779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134175059737852931823966821 25157823700847424716993779)
  ·
    refine ⟨37736735551271137075490669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25157823700847424716993779 37736735551271137075490669)
    ·
      refine ⟨14151275831726676403309001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37736735551271137075490669 14151275831726676403309001)
      ·
        refine ⟨10613456873795007302481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14151275831726676403309001 10613456873795007302481751)
        ·
          refine ⟨15920185310692510953722627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613456873795007302481751 15920185310692510953722627)
          ·
            refine ⟨23880277966038766430583941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15920185310692510953722627 23880277966038766430583941)
            ·
              refine ⟨4477552118632268705734489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23880277966038766430583941 4477552118632268705734489)
              ·
                refine ⟨3358164088974201529300867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477552118632268705734489 3358164088974201529300867)
                ·
                  refine ⟨5037246133461302293951301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358164088974201529300867 5037246133461302293951301)
                  ·
                    refine ⟨944483650023994180115869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037246133461302293951301 944483650023994180115869)
                    ·
                      rfl

theorem cell23_5518126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5518126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518126 prefixEnd_5518126 := by exact prefixLift 5518126
  have htrace : WordTrace (prefixWord ++ tailWord_5518126) baseStart_5518126 baseEnd_5518126 := by
    simpa [prefixWord, tailWord_5518126, baseEnd_5518126] using wordTrace_append hprefix tailTrace_5518126
  have hstable : (prefixWord ++ tailWord_5518126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518126).length < 2 ^ (prefixWord ++ tailWord_5518126).sum := by decide
  have hdescent : baseEnd_5518126 < baseStart_5518126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518165 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_5518165 : Nat := 118140960795 + 5518165 * 2 ^ 59
def prefixEnd_5518165 : Nat := 4983230072969 + 3 ^ 40 * 5518165 * 2
def baseEnd_5518165 : Nat := 944490325272502629253309

theorem tailTrace_5518165 : CollatzResearch.WordTrace tailWord_5518165 prefixEnd_5518165 944490325272502629253309 := by
  unfold tailWord_5518165
  simp only [CollatzResearch.WordTrace]
  refine ⟨201264012053638107396619949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134176008035758738264413299 201264012053638107396619949)
  ·
    refine ⟨75474004520114290273732481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201264012053638107396619949 75474004520114290273732481)
    ·
      refine ⟨56605503390085717705299361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75474004520114290273732481 56605503390085717705299361)
      ·
        refine ⟨42454127542564288278974521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56605503390085717705299361 42454127542564288278974521)
        ·
          refine ⟨31840595656923216209230891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42454127542564288278974521 31840595656923216209230891)
          ·
            refine ⟨47760893485384824313846337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31840595656923216209230891 47760893485384824313846337)
            ·
              refine ⟨35820670114038618235384753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47760893485384824313846337 35820670114038618235384753)
              ·
                refine ⟨26865502585528963676538565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35820670114038618235384753 26865502585528963676538565)
                ·
                  refine ⟨5037281734786680689350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26865502585528963676538565 5037281734786680689350981)
                  ·
                    refine ⟨944490325272502629253309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037281734786680689350981 944490325272502629253309)
                    ·
                      rfl

theorem cell23_5518165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_5518165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518165 prefixEnd_5518165 := by exact prefixLift 5518165
  have htrace : WordTrace (prefixWord ++ tailWord_5518165) baseStart_5518165 baseEnd_5518165 := by
    simpa [prefixWord, tailWord_5518165, baseEnd_5518165] using wordTrace_append hprefix tailTrace_5518165
  have hstable : (prefixWord ++ tailWord_5518165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518165).length < 2 ^ (prefixWord ++ tailWord_5518165).sum := by decide
  have hdescent : baseEnd_5518165 < baseStart_5518165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518206 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5518206 : Nat := 118140960795 + 5518206 * 2 ^ 59
def prefixEnd_5518206 : Nat := 4983230072969 + 3 ^ 40 * 5518206 * 2
def baseEnd_5518206 : Nat := 2833492028524342227347239

theorem tailTrace_5518206 : CollatzResearch.WordTrace tailWord_5518206 prefixEnd_5518206 2833492028524342227347239 := by
  unfold tailWord_5518206
  simp only [CollatzResearch.WordTrace]
  refine ⟨25158188430811196424857809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134177004964326380932574981 25158188430811196424857809)
  ·
    refine ⟨18868641323108397318643357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25158188430811196424857809 18868641323108397318643357)
    ·
      refine ⟨7075740496165648994491259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18868641323108397318643357 7075740496165648994491259)
      ·
        refine ⟨10613610744248473491736889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7075740496165648994491259 10613610744248473491736889)
        ·
          refine ⟨7960208058186355118802667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10613610744248473491736889 7960208058186355118802667)
          ·
            refine ⟨11940312087279532678204001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960208058186355118802667 11940312087279532678204001)
            ·
              refine ⟨8955234065459649508653001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11940312087279532678204001 8955234065459649508653001)
              ·
                refine ⟨6716425549094737131489751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8955234065459649508653001 6716425549094737131489751)
                ·
                  refine ⟨10074638323642105697234627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716425549094737131489751 10074638323642105697234627)
                  ·
                    refine ⟨15111957485463158545851941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10074638323642105697234627 15111957485463158545851941)
                    ·
                      refine ⟨2833492028524342227347239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15111957485463158545851941 2833492028524342227347239)
                      ·
                        rfl

theorem cell23_5518206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5518206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518206 prefixEnd_5518206 := by exact prefixLift 5518206
  have htrace : WordTrace (prefixWord ++ tailWord_5518206) baseStart_5518206 baseEnd_5518206 := by
    simpa [prefixWord, tailWord_5518206, baseEnd_5518206] using wordTrace_append hprefix tailTrace_5518206
  have hstable : (prefixWord ++ tailWord_5518206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518206).length < 2 ^ (prefixWord ++ tailWord_5518206).sum := by decide
  have hdescent : baseEnd_5518206 < baseStart_5518206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518265 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5518265 : Nat := 118140960795 + 5518265 * 2 ^ 59
def prefixEnd_5518265 : Nat := 4983230072969 + 3 ^ 40 * 5518265 * 2
def baseEnd_5518265 : Nat := 2833522323882957496509467

theorem tailTrace_5518265 : CollatzResearch.WordTrace tailWord_5518265 prefixEnd_5518265 2833522323882957496509467 := by
  unfold tailWord_5518265
  simp only [CollatzResearch.WordTrace]
  refine ⟨201267659353275824475260249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134178439568850549650173499 201267659353275824475260249)
  ·
    refine ⟨150950744514956868356445187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201267659353275824475260249 150950744514956868356445187)
    ·
      refine ⟨226426116772435302534667781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150950744514956868356445187 226426116772435302534667781)
      ·
        refine ⟨42454896894831619225250209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226426116772435302534667781 42454896894831619225250209)
        ·
          refine ⟨31841172671123714418937657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42454896894831619225250209 31841172671123714418937657)
          ·
            refine ⟨23880879503342785814203243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31841172671123714418937657 23880879503342785814203243)
            ·
              refine ⟨35821319255014178721304865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23880879503342785814203243 35821319255014178721304865)
              ·
                refine ⟨26865989441260634040978649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35821319255014178721304865 26865989441260634040978649)
                ·
                  refine ⟨20149492080945475530733987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26865989441260634040978649 20149492080945475530733987)
                  ·
                    refine ⟨30224238121418213296100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20149492080945475530733987 30224238121418213296100981)
                    ·
                      refine ⟨2833522323882957496509467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30224238121418213296100981 2833522323882957496509467)
                      ·
                        rfl

theorem cell23_5518265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5518265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518265 prefixEnd_5518265 := by exact prefixLift 5518265
  have htrace : WordTrace (prefixWord ++ tailWord_5518265) baseStart_5518265 baseEnd_5518265 := by
    simpa [prefixWord, tailWord_5518265, baseEnd_5518265] using wordTrace_append hprefix tailTrace_5518265
  have hstable : (prefixWord ++ tailWord_5518265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518265).length < 2 ^ (prefixWord ++ tailWord_5518265).sum := by decide
  have hdescent : baseEnd_5518265 < baseStart_5518265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518296 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_5518296 : Nat := 118140960795 + 5518296 * 2 ^ 59
def prefixEnd_5518296 : Nat := 4983230072969 + 3 ^ 40 * 5518296 * 2
def baseEnd_5518296 : Nat := 2833538241783246875221825

theorem tailTrace_5518296 : CollatzResearch.WordTrace tailWord_5518296 prefixEnd_5518296 2833538241783246875221825 := by
  unfold tailWord_5518296
  simp only [CollatzResearch.WordTrace]
  refine ⟨100634395008081758384819371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134179193344109011179759161 100634395008081758384819371)
  ·
    refine ⟨150951592512122637577229057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100634395008081758384819371 150951592512122637577229057)
    ·
      refine ⟨113213694384091978182921793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150951592512122637577229057 113213694384091978182921793)
      ·
        refine ⟨84910270788068983637191345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113213694384091978182921793 84910270788068983637191345)
        ·
          refine ⟨63682703091051737727893509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84910270788068983637191345 63682703091051737727893509)
          ·
            refine ⟨11940506829572200823980033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63682703091051737727893509 11940506829572200823980033)
            ·
              refine ⟨8955380122179150617985025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11940506829572200823980033 8955380122179150617985025)
              ·
                refine ⟨6716535091634362963488769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8955380122179150617985025 6716535091634362963488769)
                ·
                  refine ⟨5037401318725772222616577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6716535091634362963488769 5037401318725772222616577)
                  ·
                    refine ⟨3778050989044329166962433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5037401318725772222616577 3778050989044329166962433)
                    ·
                      refine ⟨2833538241783246875221825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778050989044329166962433 2833538241783246875221825)
                      ·
                        rfl

theorem cell23_5518296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_5518296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518296 prefixEnd_5518296 := by exact prefixLift 5518296
  have htrace : WordTrace (prefixWord ++ tailWord_5518296) baseStart_5518296 baseEnd_5518296 := by
    simpa [prefixWord, tailWord_5518296, baseEnd_5518296] using wordTrace_append hprefix tailTrace_5518296
  have hstable : (prefixWord ++ tailWord_5518296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518296).length < 2 ^ (prefixWord ++ tailWord_5518296).sum := by decide
  have hdescent : baseEnd_5518296 < baseStart_5518296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518309 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5518309 : Nat := 118140960795 + 5518309 * 2 ^ 59
def prefixEnd_5518309 : Nat := 4983230072969 + 3 ^ 40 * 5518309 * 2
def baseEnd_5518309 : Nat := 2833544917031755324359265

theorem tailTrace_5518309 : CollatzResearch.WordTrace tailWord_5518309 prefixEnd_5518309 2833544917031755324359265 := by
  unfold tailWord_5518309
  simp only [CollatzResearch.WordTrace]
  refine ⟨201269264165116419989861981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134179509443410946659907987 201269264165116419989861981)
  ·
    refine ⟨75475974061918657496198243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201269264165116419989861981 75475974061918657496198243)
    ·
      refine ⟨113213961092877986244297365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75475974061918657496198243 113213961092877986244297365)
      ·
        refine ⟨5306904426228655605201439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113213961092877986244297365 5306904426228655605201439)
        ·
          refine ⟨7960356639342983407802159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306904426228655605201439 7960356639342983407802159)
          ·
            refine ⟨11940534959014475111703239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960356639342983407802159 11940534959014475111703239)
            ·
              refine ⟨17910802438521712667554859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11940534959014475111703239 17910802438521712667554859)
              ·
                refine ⟨26866203657782569001332289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17910802438521712667554859 26866203657782569001332289)
                ·
                  refine ⟨20149652743336926750999217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26866203657782569001332289 20149652743336926750999217)
                  ·
                    refine ⟨15112239557502695063249413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20149652743336926750999217 15112239557502695063249413)
                    ·
                      refine ⟨2833544917031755324359265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15112239557502695063249413 2833544917031755324359265)
                      ·
                        rfl

theorem cell23_5518309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5518309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518309 prefixEnd_5518309 := by exact prefixLift 5518309
  have htrace : WordTrace (prefixWord ++ tailWord_5518309) baseStart_5518309 baseEnd_5518309 := by
    simpa [prefixWord, tailWord_5518309, baseEnd_5518309] using wordTrace_append hprefix tailTrace_5518309
  have hstable : (prefixWord ++ tailWord_5518309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518309).length < 2 ^ (prefixWord ++ tailWord_5518309).sum := by decide
  have hdescent : baseEnd_5518309 < baseStart_5518309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518332 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5518332 : Nat := 118140960795 + 5518332 * 2 ^ 59
def prefixEnd_5518332 : Nat := 4983230072969 + 3 ^ 40 * 5518332 * 2
def baseEnd_5518332 : Nat := 944518909028936244790553

theorem tailTrace_5518332 : CollatzResearch.WordTrace tailWord_5518332 prefixEnd_5518332 944518909028936244790553 := by
  unfold tailWord_5518332
  simp only [CollatzResearch.WordTrace]
  refine ⟨100635051522016547458974625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134180068696022063278632833 100635051522016547458974625)
  ·
    refine ⟨75476288641512410594230969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100635051522016547458974625 75476288641512410594230969)
    ·
      refine ⟨56607216481134307945673227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75476288641512410594230969 56607216481134307945673227)
      ·
        refine ⟨84910824721701461918509841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56607216481134307945673227 84910824721701461918509841)
        ·
          refine ⟨63683118541276096438882381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84910824721701461918509841 63683118541276096438882381)
          ·
            refine ⟨23881169452978536164580893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63683118541276096438882381 23881169452978536164580893)
            ·
              refine ⟨8955438544866951061717835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23881169452978536164580893 8955438544866951061717835)
              ·
                refine ⟨13433157817300426592576753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8955438544866951061717835 13433157817300426592576753)
                ·
                  refine ⟨10074868362975319944432565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13433157817300426592576753 10074868362975319944432565)
                  ·
                    refine ⟨944518909028936244790553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10074868362975319944432565 944518909028936244790553)
                    ·
                      rfl

theorem cell23_5518332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5518332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518332 prefixEnd_5518332 := by exact prefixLift 5518332
  have htrace : WordTrace (prefixWord ++ tailWord_5518332) baseStart_5518332 baseEnd_5518332 := by
    simpa [prefixWord, tailWord_5518332, baseEnd_5518332] using wordTrace_append hprefix tailTrace_5518332
  have hstable : (prefixWord ++ tailWord_5518332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518332).length < 2 ^ (prefixWord ++ tailWord_5518332).sum := by decide
  have hdescent : baseEnd_5518332 < baseStart_5518332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518369 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5518369 : Nat := 118140960795 + 5518369 * 2 ^ 59
def prefixEnd_5518369 : Nat := 4983230072969 + 3 ^ 40 * 5518369 * 2
def baseEnd_5518369 : Nat := 2833575725871025089608989

theorem tailTrace_5518369 : CollatzResearch.WordTrace tailWord_5518369 prefixEnd_5518369 2833575725871025089608989 := by
  unfold tailWord_5518369
  simp only [CollatzResearch.WordTrace]
  refine ⟨201271452544899050237046161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134180968363266033491364107 201271452544899050237046161)
  ·
    refine ⟨150953589408674287677784621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201271452544899050237046161 150953589408674287677784621)
    ·
      refine ⟨56607596028252857879169233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150953589408674287677784621 56607596028252857879169233)
      ·
        refine ⟨42455697021189643409376925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56607596028252857879169233 42455697021189643409376925)
        ·
          refine ⟨15920886382946116278516347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42455697021189643409376925 15920886382946116278516347)
          ·
            refine ⟨23881329574419174417774521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15920886382946116278516347 23881329574419174417774521)
            ·
              refine ⟨17910997180814380813330891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23881329574419174417774521 17910997180814380813330891)
              ·
                refine ⟨26866495771221571219996337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17910997180814380813330891 26866495771221571219996337)
                ·
                  refine ⟨20149871828416178414997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26866495771221571219996337 20149871828416178414997253)
                  ·
                    refine ⟨3778100967828033452811985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20149871828416178414997253 3778100967828033452811985)
                    ·
                      refine ⟨2833575725871025089608989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778100967828033452811985 2833575725871025089608989)
                      ·
                        rfl

theorem cell23_5518369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5518369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518369 prefixEnd_5518369 := by exact prefixLift 5518369
  have htrace : WordTrace (prefixWord ++ tailWord_5518369) baseStart_5518369 baseEnd_5518369 := by
    simpa [prefixWord, tailWord_5518369, baseEnd_5518369] using wordTrace_append hprefix tailTrace_5518369
  have hstable : (prefixWord ++ tailWord_5518369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518369).length < 2 ^ (prefixWord ++ tailWord_5518369).sum := by decide
  have hdescent : baseEnd_5518369 < baseStart_5518369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518382 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5518382 : Nat := 118140960795 + 5518382 * 2 ^ 59
def prefixEnd_5518382 : Nat := 4983230072969 + 3 ^ 40 * 5518382 * 2
def baseEnd_5518382 : Nat := 2833582401119533538746429

theorem tailTrace_5518382 : CollatzResearch.WordTrace tailWord_5518382 prefixEnd_5518382 2833582401119533538746429 := by
  unfold tailWord_5518382
  simp only [CollatzResearch.WordTrace]
  refine ⟨25158990836731494182158675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134181284462567968971512933 25158990836731494182158675)
  ·
    refine ⟨37738486255097241273238013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25158990836731494182158675 37738486255097241273238013)
    ·
      refine ⟨14151932345661465477464255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37738486255097241273238013 14151932345661465477464255)
      ·
        refine ⟨21227898518492198216196383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151932345661465477464255 21227898518492198216196383)
        ·
          refine ⟨31841847777738297324294575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21227898518492198216196383 31841847777738297324294575)
          ·
            refine ⟨47762771666607445986441863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31841847777738297324294575 47762771666607445986441863)
            ·
              refine ⟨71644157499911168979662795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47762771666607445986441863 71644157499911168979662795)
              ·
                refine ⟨107466236249866753469494193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71644157499911168979662795 107466236249866753469494193)
                ·
                  refine ⟨80599677187400065102120645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107466236249866753469494193 80599677187400065102120645)
                  ·
                    refine ⟨15112439472637512206647621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80599677187400065102120645 15112439472637512206647621)
                    ·
                      refine ⟨2833582401119533538746429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15112439472637512206647621 2833582401119533538746429)
                      ·
                        rfl

theorem cell23_5518382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5518382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518382 prefixEnd_5518382 := by exact prefixLift 5518382
  have htrace : WordTrace (prefixWord ++ tailWord_5518382) baseStart_5518382 baseEnd_5518382 := by
    simpa [prefixWord, tailWord_5518382, baseEnd_5518382] using wordTrace_append hprefix tailTrace_5518382
  have hstable : (prefixWord ++ tailWord_5518382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518382).length < 2 ^ (prefixWord ++ tailWord_5518382).sum := by decide
  have hdescent : baseEnd_5518382 < baseStart_5518382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518396 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_5518396 : Nat := 118140960795 + 5518396 * 2 ^ 59
def prefixEnd_5518396 : Nat := 4983230072969 + 3 ^ 40 * 5518396 * 2
def baseEnd_5518396 : Nat := 944529863282898827990455

theorem tailTrace_5518396 : CollatzResearch.WordTrace tailWord_5518396 prefixEnd_5518396 944529863282898827990455 := by
  unfold tailWord_5518396
  simp only [CollatzResearch.WordTrace]
  refine ⟨100636218657900616924139521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134181624877200822565519361 100636218657900616924139521)
  ·
    refine ⟨75477163993425462693104641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100636218657900616924139521 75477163993425462693104641)
    ·
      refine ⟨56607872995069097019828481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75477163993425462693104641 56607872995069097019828481)
      ·
        refine ⟨42455904746301822764871361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56607872995069097019828481 42455904746301822764871361)
        ·
          refine ⟨31841928559726367073653521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42455904746301822764871361 31841928559726367073653521)
          ·
            refine ⟨23881446419794775305240141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31841928559726367073653521 23881446419794775305240141)
            ·
              refine ⟨8955542407423040739465053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23881446419794775305240141 8955542407423040739465053)
              ·
                refine ⟨3358328402783640277299395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8955542407423040739465053 3358328402783640277299395)
                ·
                  refine ⟨5037492604175460415949093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358328402783640277299395 5037492604175460415949093)
                  ·
                    refine ⟨944529863282898827990455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037492604175460415949093 944529863282898827990455)
                    ·
                      rfl

theorem cell23_5518396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_5518396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518396 prefixEnd_5518396 := by exact prefixLift 5518396
  have htrace : WordTrace (prefixWord ++ tailWord_5518396) baseStart_5518396 baseEnd_5518396 := by
    simpa [prefixWord, tailWord_5518396, baseEnd_5518396] using wordTrace_append hprefix tailTrace_5518396
  have hstable : (prefixWord ++ tailWord_5518396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518396).length < 2 ^ (prefixWord ++ tailWord_5518396).sum := by decide
  have hdescent : baseEnd_5518396 < baseStart_5518396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518406 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5518406 : Nat := 118140960795 + 5518406 * 2 ^ 59
def prefixEnd_5518406 : Nat := 4983230072969 + 3 ^ 40 * 5518406 * 2
def baseEnd_5518406 : Nat := 2833594724655241444846319

theorem tailTrace_5518406 : CollatzResearch.WordTrace tailWord_5518406 prefixEnd_5518406 2833594724655241444846319 := by
  unfold tailWord_5518406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6289775063930156423629471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134181868030510003704095381 6289775063930156423629471)
  ·
    refine ⟨9434662595895234635444207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6289775063930156423629471 9434662595895234635444207)
    ·
      refine ⟨14151993893842851953166311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434662595895234635444207 14151993893842851953166311)
      ·
        refine ⟨21227990840764277929749467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14151993893842851953166311 21227990840764277929749467)
        ·
          refine ⟨31841986261146416894624201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21227990840764277929749467 31841986261146416894624201)
          ·
            refine ⟨23881489695859812670968151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31841986261146416894624201 23881489695859812670968151)
            ·
              refine ⟨35822234543789719006452227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23881489695859812670968151 35822234543789719006452227)
              ·
                refine ⟨53733351815684578509678341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35822234543789719006452227 53733351815684578509678341)
                ·
                  refine ⟨10075003465440858470564689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53733351815684578509678341 10075003465440858470564689)
                  ·
                    refine ⟨7556252599080643852923517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10075003465440858470564689 7556252599080643852923517)
                    ·
                      refine ⟨2833594724655241444846319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556252599080643852923517 2833594724655241444846319)
                      ·
                        rfl

theorem cell23_5518406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5518406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518406 prefixEnd_5518406 := by exact prefixLift 5518406
  have htrace : WordTrace (prefixWord ++ tailWord_5518406) baseStart_5518406 baseEnd_5518406 := by
    simpa [prefixWord, tailWord_5518406, baseEnd_5518406] using wordTrace_append hprefix tailTrace_5518406
  have hstable : (prefixWord ++ tailWord_5518406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518406).length < 2 ^ (prefixWord ++ tailWord_5518406).sum := by decide
  have hdescent : baseEnd_5518406 < baseStart_5518406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518439 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 1, 5]
def baseStart_5518439 : Nat := 118140960795 + 5518439 * 2 ^ 59
def prefixEnd_5518439 : Nat := 4983230072969 + 3 ^ 40 * 5518439 * 2
def baseEnd_5518439 : Nat := 944537223172279938577889

theorem tailTrace_5518439 : CollatzResearch.WordTrace tailWord_5518439 prefixEnd_5518439 944537223172279938577889 := by
  unfold tailWord_5518439
  simp only [CollatzResearch.WordTrace]
  refine ⟨201274005654645452192094371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134182670436430301461396247 201274005654645452192094371)
  ·
    refine ⟨301911008481968178288141557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201274005654645452192094371 301911008481968178288141557)
    ·
      refine ⟨28304157045184516714513271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 301911008481968178288141557 28304157045184516714513271)
      ·
        refine ⟨42456235567776775071769907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28304157045184516714513271 42456235567776775071769907)
        ·
          refine ⟨63684353351665162607654861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42456235567776775071769907 63684353351665162607654861)
          ·
            refine ⟨23881632506874435977870573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63684353351665162607654861 23881632506874435977870573)
            ·
              refine ⟨8955612190077913491701465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23881632506874435977870573 8955612190077913491701465)
              ·
                refine ⟨6716709142558435118776099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8955612190077913491701465 6716709142558435118776099)
                ·
                  refine ⟨10075063713837652678164149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716709142558435118776099 10075063713837652678164149)
                  ·
                    refine ⟨944537223172279938577889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10075063713837652678164149 944537223172279938577889)
                    ·
                      rfl

theorem cell23_5518439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_5518439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518439 prefixEnd_5518439 := by exact prefixLift 5518439
  have htrace : WordTrace (prefixWord ++ tailWord_5518439) baseStart_5518439 baseEnd_5518439 := by
    simpa [prefixWord, tailWord_5518439, baseEnd_5518439] using wordTrace_append hprefix tailTrace_5518439
  have hstable : (prefixWord ++ tailWord_5518439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518439).length < 2 ^ (prefixWord ++ tailWord_5518439).sum := by decide
  have hdescent : baseEnd_5518439 < baseStart_5518439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518446 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5518446 : Nat := 118140960795 + 5518446 * 2 ^ 59
def prefixEnd_5518446 : Nat := 4983230072969 + 3 ^ 40 * 5518446 * 2
def baseEnd_5518446 : Nat := 2833615263881421288346135

theorem tailTrace_5518446 : CollatzResearch.WordTrace tailWord_5518446 prefixEnd_5518446 2833615263881421288346135 := by
  unfold tailWord_5518446
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159282620702511548449899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134182840643746728258399461 25159282620702511548449899)
  ·
    refine ⟨37738923931053767322674849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25159282620702511548449899 37738923931053767322674849)
    ·
      refine ⟨28304192948290325492006137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37738923931053767322674849 28304192948290325492006137)
      ·
        refine ⟨21228144711217744119004603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28304192948290325492006137 21228144711217744119004603)
        ·
          refine ⟨31842217066826616178506905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21228144711217744119004603 31842217066826616178506905)
          ·
            refine ⟨23881662800119962133880179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31842217066826616178506905 23881662800119962133880179)
            ·
              refine ⟨35822494200179943200820269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23881662800119962133880179 35822494200179943200820269)
              ·
                refine ⟨13433435325067478700307601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35822494200179943200820269 13433435325067478700307601)
                ·
                  refine ⟨10075076493800609025230701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13433435325067478700307601 10075076493800609025230701)
                  ·
                    refine ⟨3778153685175228384461513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10075076493800609025230701 3778153685175228384461513)
                    ·
                      refine ⟨2833615263881421288346135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778153685175228384461513 2833615263881421288346135)
                      ·
                        rfl

theorem cell23_5518446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5518446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518446 prefixEnd_5518446 := by exact prefixLift 5518446
  have htrace : WordTrace (prefixWord ++ tailWord_5518446) baseStart_5518446 baseEnd_5518446 := by
    simpa [prefixWord, tailWord_5518446, baseEnd_5518446] using wordTrace_append hprefix tailTrace_5518446
  have hstable : (prefixWord ++ tailWord_5518446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518446).length < 2 ^ (prefixWord ++ tailWord_5518446).sum := by decide
  have hdescent : baseEnd_5518446 < baseStart_5518446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518506 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5518506 : Nat := 118140960795 + 5518506 * 2 ^ 59
def prefixEnd_5518506 : Nat := 4983230072969 + 3 ^ 40 * 5518506 * 2
def baseEnd_5518506 : Nat := 2833646072720691053595859

theorem tailTrace_5518506 : CollatzResearch.WordTrace tailWord_5518506 prefixEnd_5518506 2833646072720691053595859 := by
  unfold tailWord_5518506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319112336350680658695843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134184299563601815089855581 50319112336350680658695843)
  ·
    refine ⟨75478668504526020988043765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50319112336350680658695843 75478668504526020988043765)
    ·
      refine ⟨7076125172299314467629103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75478668504526020988043765 7076125172299314467629103)
      ·
        refine ⟨10614187758448971701443655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7076125172299314467629103 10614187758448971701443655)
        ·
          refine ⟨15921281637673457552165483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614187758448971701443655 15921281637673457552165483)
          ·
            refine ⟨23881922456510186328248225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921281637673457552165483 23881922456510186328248225)
            ·
              refine ⟨17911441842382639746186169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23881922456510186328248225 17911441842382639746186169)
              ·
                refine ⟨13433581381786979809639627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17911441842382639746186169 13433581381786979809639627)
                ·
                  refine ⟨20150372072680469714459441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13433581381786979809639627 20150372072680469714459441)
                  ·
                    refine ⟨15112779054510352285844581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20150372072680469714459441 15112779054510352285844581)
                    ·
                      refine ⟨2833646072720691053595859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15112779054510352285844581 2833646072720691053595859)
                      ·
                        rfl

theorem cell23_5518506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5518506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518506 prefixEnd_5518506 := by exact prefixLift 5518506
  have htrace : WordTrace (prefixWord ++ tailWord_5518506) baseStart_5518506 baseEnd_5518506 := by
    simpa [prefixWord, tailWord_5518506, baseEnd_5518506] using wordTrace_append hprefix tailTrace_5518506
  have hstable : (prefixWord ++ tailWord_5518506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518506).length < 2 ^ (prefixWord ++ tailWord_5518506).sum := by decide
  have hdescent : baseEnd_5518506 < baseStart_5518506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518513 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5518513 : Nat := 118140960795 + 5518513 * 2 ^ 59
def prefixEnd_5518513 : Nat := 4983230072969 + 3 ^ 40 * 5518513 * 2
def baseEnd_5518513 : Nat := 2833649667085272526208327

theorem tailTrace_5518513 : CollatzResearch.WordTrace tailWord_5518513 prefixEnd_5518513 2833649667085272526208327 := by
  unfold tailWord_5518513
  simp only [CollatzResearch.WordTrace]
  refine ⟨201276704656377362830288193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134184469770918241886858795 201276704656377362830288193)
  ·
    refine ⟨150957528492283022122716145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201276704656377362830288193 150957528492283022122716145)
    ·
      refine ⟨113218146369212266592037109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150957528492283022122716145 113218146369212266592037109)
      ·
        refine ⟨10614201222113649993003479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113218146369212266592037109 10614201222113649993003479)
        ·
          refine ⟨15921301833170474989505219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614201222113649993003479 15921301833170474989505219)
          ·
            refine ⟨23881952749755712484257829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921301833170474989505219 23881952749755712484257829)
            ·
              refine ⟨4477866140579196090798343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23881952749755712484257829 4477866140579196090798343)
              ·
                refine ⟨6716799210868794136197515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477866140579196090798343 6716799210868794136197515)
                ·
                  refine ⟨10075198816303191204296273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716799210868794136197515 10075198816303191204296273)
                  ·
                    refine ⟨7556399112227393403222205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10075198816303191204296273 7556399112227393403222205)
                    ·
                      refine ⟨2833649667085272526208327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556399112227393403222205 2833649667085272526208327)
                      ·
                        rfl

theorem cell23_5518513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5518513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518513 prefixEnd_5518513 := by exact prefixLift 5518513
  have htrace : WordTrace (prefixWord ++ tailWord_5518513) baseStart_5518513 baseEnd_5518513 := by
    simpa [prefixWord, tailWord_5518513, baseEnd_5518513] using wordTrace_append hprefix tailTrace_5518513
  have hstable : (prefixWord ++ tailWord_5518513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518513).length < 2 ^ (prefixWord ++ tailWord_5518513).sum := by decide
  have hdescent : baseEnd_5518513 < baseStart_5518513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518550 : List Nat := [5, 2, 1, 2, 3, 1, 2, 7]
def baseStart_5518550 : Nat := 118140960795 + 5518550 * 2 ^ 59
def prefixEnd_5518550 : Nat := 4983230072969 + 3 ^ 40 * 5518550 * 2
def baseEnd_5518550 : Nat := 104950691328499588201691

theorem tailTrace_5518550 : CollatzResearch.WordTrace tailWord_5518550 prefixEnd_5518550 104950691328499588201691 := by
  unfold tailWord_5518550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12579878384827707384336569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134185369438162212099590069 12579878384827707384336569)
  ·
    refine ⟨9434908788620780538252427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12579878384827707384336569 9434908788620780538252427)
    ·
      refine ⟨14152363182931170807378641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434908788620780538252427 14152363182931170807378641)
      ·
        refine ⟨10614272387198378105533981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14152363182931170807378641 10614272387198378105533981)
        ·
          refine ⟨3980352145199391789575243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10614272387198378105533981 3980352145199391789575243)
          ·
            refine ⟨5970528217799087684362865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980352145199391789575243 5970528217799087684362865)
            ·
              refine ⟨4477896163349315763272149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970528217799087684362865 4477896163349315763272149)
              ·
                refine ⟨104950691328499588201691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4477896163349315763272149 104950691328499588201691)
                ·
                  rfl

theorem cell23_5518550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_5518550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518550 prefixEnd_5518550 := by exact prefixLift 5518550
  have htrace : WordTrace (prefixWord ++ tailWord_5518550) baseStart_5518550 baseEnd_5518550 := by
    simpa [prefixWord, tailWord_5518550, baseEnd_5518550] using wordTrace_append hprefix tailTrace_5518550
  have hstable : (prefixWord ++ tailWord_5518550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518550).length < 2 ^ (prefixWord ++ tailWord_5518550).sum := by decide
  have hdescent : baseEnd_5518550 < baseStart_5518550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518594 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_5518594 : Nat := 118140960795 + 5518594 * 2 ^ 59
def prefixEnd_5518594 : Nat := 4983230072969 + 3 ^ 40 * 5518594 * 2
def baseEnd_5518594 : Nat := 2833691259018286709295455

theorem tailTrace_5518594 : CollatzResearch.WordTrace tailWord_5518594 prefixEnd_5518594 2833691259018286709295455 := by
  unfold tailWord_5518594
  simp only [CollatzResearch.WordTrace]
  refine ⟨50319914742270978415996709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134186439312722609109324557 50319914742270978415996709)
  ·
    refine ⟨9434984014175808452999383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50319914742270978415996709 9434984014175808452999383)
    ·
      refine ⟨14152476021263712679499075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434984014175808452999383 14152476021263712679499075)
      ·
        refine ⟨21228714031895569019248613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14152476021263712679499075 21228714031895569019248613)
        ·
          refine ⟨3980383880980419191109115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21228714031895569019248613 3980383880980419191109115)
          ·
            refine ⟨5970575821470628786663673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980383880980419191109115 5970575821470628786663673)
            ·
              refine ⟨4477931866102971589997755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5970575821470628786663673 4477931866102971589997755)
              ·
                refine ⟨6716897799154457384996633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477931866102971589997755 6716897799154457384996633)
                ·
                  refine ⟨5037673349365843038747475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6716897799154457384996633 5037673349365843038747475)
                  ·
                    refine ⟨7556510024048764558121213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5037673349365843038747475 7556510024048764558121213)
                    ·
                      refine ⟨2833691259018286709295455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556510024048764558121213 2833691259018286709295455)
                      ·
                        rfl

theorem cell23_5518594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_5518594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518594 prefixEnd_5518594 := by exact prefixLift 5518594
  have htrace : WordTrace (prefixWord ++ tailWord_5518594) baseStart_5518594 baseEnd_5518594 := by
    simpa [prefixWord, tailWord_5518594, baseEnd_5518594] using wordTrace_append hprefix tailTrace_5518594
  have hstable : (prefixWord ++ tailWord_5518594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518594).length < 2 ^ (prefixWord ++ tailWord_5518594).sum := by decide
  have hdescent : baseEnd_5518594 < baseStart_5518594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518600 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_5518600 : Nat := 118140960795 + 5518600 * 2 ^ 59
def prefixEnd_5518600 : Nat := 4983230072969 + 3 ^ 40 * 5518600 * 2
def baseEnd_5518600 : Nat := 2833694339902213685820427

theorem tailTrace_5518600 : CollatzResearch.WordTrace tailWord_5518600 prefixEnd_5518600 2833694339902213685820427 := by
  unfold tailWord_5518600
  simp only [CollatzResearch.WordTrace]
  refine ⟨100639938903531088344352627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134186585204708117792470169 100639938903531088344352627)
  ·
    refine ⟨150959908355296632516528941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100639938903531088344352627 150959908355296632516528941)
    ·
      refine ⟨56609965633236237193698353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150959908355296632516528941 56609965633236237193698353)
      ·
        refine ⟨42457474224927177895273765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56609965633236237193698353 42457474224927177895273765)
        ·
          refine ⟨7960776417173845855363831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42457474224927177895273765 7960776417173845855363831)
          ·
            refine ⟨11941164625760768783045747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960776417173845855363831 11941164625760768783045747)
            ·
              refine ⟨17911746938641153174568621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11941164625760768783045747 17911746938641153174568621)
              ·
                refine ⟨6716905101990432440463233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17911746938641153174568621 6716905101990432440463233)
                ·
                  refine ⟨5037678826492824330347425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6716905101990432440463233 5037678826492824330347425)
                  ·
                    refine ⟨3778259119869618247760569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5037678826492824330347425 3778259119869618247760569)
                    ·
                      refine ⟨2833694339902213685820427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778259119869618247760569 2833694339902213685820427)
                      ·
                        rfl

theorem cell23_5518600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_5518600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518600 prefixEnd_5518600 := by exact prefixLift 5518600
  have htrace : WordTrace (prefixWord ++ tailWord_5518600) baseStart_5518600 baseEnd_5518600 := by
    simpa [prefixWord, tailWord_5518600, baseEnd_5518600] using wordTrace_append hprefix tailTrace_5518600
  have hstable : (prefixWord ++ tailWord_5518600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518600).length < 2 ^ (prefixWord ++ tailWord_5518600).sum := by decide
  have hdescent : baseEnd_5518600 < baseStart_5518600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518629 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_5518629 : Nat := 118140960795 + 5518629 * 2 ^ 59
def prefixEnd_5518629 : Nat := 4983230072969 + 3 ^ 40 * 5518629 * 2
def baseEnd_5518629 : Nat := 2833709230841194072357793

theorem tailTrace_5518629 : CollatzResearch.WordTrace tailWord_5518629 prefixEnd_5518629 2833709230841194072357793 := by
  unfold tailWord_5518629
  simp only [CollatzResearch.WordTrace]
  refine ⟨201280935523957114641510941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134187290349304743094340627 201280935523957114641510941)
  ·
    refine ⟨75480350821483917990566603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201280935523957114641510941 75480350821483917990566603)
    ·
      refine ⟨113220526232225876985849905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75480350821483917990566603 113220526232225876985849905)
      ·
        refine ⟨84915394674169407739387429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113220526232225876985849905 84915394674169407739387429)
        ·
          refine ⟨15921636501406763951135143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84915394674169407739387429 15921636501406763951135143)
          ·
            refine ⟨23882454752110145926702715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921636501406763951135143 23882454752110145926702715)
            ·
              refine ⟨35823682128165218890054073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23882454752110145926702715 35823682128165218890054073)
              ·
                refine ⟨26867761596123914167540555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35823682128165218890054073 26867761596123914167540555)
                ·
                  refine ⟨40301642394185871251310833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26867761596123914167540555 40301642394185871251310833)
                  ·
                    refine ⟨30226231795639403438483125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40301642394185871251310833 30226231795639403438483125)
                    ·
                      refine ⟨2833709230841194072357793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30226231795639403438483125 2833709230841194072357793)
                      ·
                        rfl

theorem cell23_5518629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_5518629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518629 prefixEnd_5518629 := by exact prefixLift 5518629
  have htrace : WordTrace (prefixWord ++ tailWord_5518629) baseStart_5518629 baseEnd_5518629 := by
    simpa [prefixWord, tailWord_5518629, baseEnd_5518629] using wordTrace_append hprefix tailTrace_5518629
  have hstable : (prefixWord ++ tailWord_5518629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518629).length < 2 ^ (prefixWord ++ tailWord_5518629).sum := by decide
  have hdescent : baseEnd_5518629 < baseStart_5518629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518656 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2]
def baseStart_5518656 : Nat := 118140960795 + 5518656 * 2 ^ 59
def prefixEnd_5518656 : Nat := 4983230072969 + 3 ^ 40 * 5518656 * 2
def baseEnd_5518656 : Nat := 2833723094818865466720169

theorem tailTrace_5518656 : CollatzResearch.WordTrace tailWord_5518656 prefixEnd_5518656 2833723094818865466720169 := by
  unfold tailWord_5518656
  simp only [CollatzResearch.WordTrace]
  refine ⟨100640960147429649126371911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134187946863239532168495881 100640960147429649126371911)
  ·
    refine ⟨150961440221144473689557867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100640960147429649126371911 150961440221144473689557867)
    ·
      refine ⟨226442160331716710534336801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150961440221144473689557867 226442160331716710534336801)
      ·
        refine ⟨169831620248787532900752601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226442160331716710534336801 169831620248787532900752601)
        ·
          refine ⟨127373715186590649675564451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169831620248787532900752601 127373715186590649675564451)
          ·
            refine ⟨191060572779885974513346677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127373715186590649675564451 191060572779885974513346677)
            ·
              refine ⟨17911928698114310110626251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191060572779885974513346677 17911928698114310110626251)
              ·
                refine ⟨26867893047171465165939377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17911928698114310110626251 26867893047171465165939377)
                ·
                  refine ⟨20150919785378598874454533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26867893047171465165939377 20150919785378598874454533)
                  ·
                    refine ⟨3778297459758487288960225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20150919785378598874454533 3778297459758487288960225)
                    ·
                      refine ⟨2833723094818865466720169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778297459758487288960225 2833723094818865466720169)
                      ·
                        rfl

theorem cell23_5518656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_5518656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518656 prefixEnd_5518656 := by exact prefixLift 5518656
  have htrace : WordTrace (prefixWord ++ tailWord_5518656) baseStart_5518656 baseEnd_5518656 := by
    simpa [prefixWord, tailWord_5518656, baseEnd_5518656] using wordTrace_append hprefix tailTrace_5518656
  have hstable : (prefixWord ++ tailWord_5518656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518656).length < 2 ^ (prefixWord ++ tailWord_5518656).sum := by decide
  have hdescent : baseEnd_5518656 < baseStart_5518656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518659 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3]
def baseStart_5518659 : Nat := 118140960795 + 5518659 * 2 ^ 59
def prefixEnd_5518659 : Nat := 4983230072969 + 3 ^ 40 * 5518659 * 2
def baseEnd_5518659 : Nat := 2833724635260828954982655

theorem tailTrace_5518659 : CollatzResearch.WordTrace tailWord_5518659 prefixEnd_5518659 2833724635260828954982655 := by
  unfold tailWord_5518659
  simp only [CollatzResearch.WordTrace]
  refine ⟨201282029713848429765103031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134188019809232286510068687 201282029713848429765103031)
  ·
    refine ⟨301923044570772644647654547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201282029713848429765103031 301923044570772644647654547)
    ·
      refine ⟨452884566856158966971481821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301923044570772644647654547 452884566856158966971481821)
      ·
        refine ⟨169831712571059612614305683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452884566856158966971481821 169831712571059612614305683)
        ·
          refine ⟨254747568856589418921458525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169831712571059612614305683 254747568856589418921458525)
          ·
            refine ⟨95530338321221032095546947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254747568856589418921458525 95530338321221032095546947)
            ·
              refine ⟨143295507481831548143320421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95530338321221032095546947 143295507481831548143320421)
              ·
                refine ⟨26867907652843415276872579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143295507481831548143320421 26867907652843415276872579)
                ·
                  refine ⟨40301861479265122915308869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26867907652843415276872579 40301861479265122915308869)
                  ·
                    refine ⟨7556599027362210546620413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40301861479265122915308869 7556599027362210546620413)
                    ·
                      refine ⟨2833724635260828954982655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556599027362210546620413 2833724635260828954982655)
                      ·
                        rfl

theorem cell23_5518659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_5518659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518659 prefixEnd_5518659 := by exact prefixLift 5518659
  have htrace : WordTrace (prefixWord ++ tailWord_5518659) baseStart_5518659 baseEnd_5518659 := by
    simpa [prefixWord, tailWord_5518659, baseEnd_5518659] using wordTrace_append hprefix tailTrace_5518659
  have hstable : (prefixWord ++ tailWord_5518659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518659).length < 2 ^ (prefixWord ++ tailWord_5518659).sum := by decide
  have hdescent : baseEnd_5518659 < baseStart_5518659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518676 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_5518676 : Nat := 118140960795 + 5518676 * 2 ^ 59
def prefixEnd_5518676 : Nat := 4983230072969 + 3 ^ 40 * 5518676 * 2
def baseEnd_5518676 : Nat := 2833733364431955388470077

theorem tailTrace_5518676 : CollatzResearch.WordTrace tailWord_5518676 prefixEnd_5518676 2833733364431955388470077 := by
  unfold tailWord_5518676
  simp only [CollatzResearch.WordTrace]
  refine ⟨100641324877393420834235941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134188433169857894445647921 100641324877393420834235941)
  ·
    refine ⟨18870248414511266406419239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100641324877393420834235941 18870248414511266406419239)
    ·
      refine ⟨28305372621766899609628859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18870248414511266406419239 28305372621766899609628859)
      ·
        refine ⟨42458058932650349414443289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28305372621766899609628859 42458058932650349414443289)
        ·
          refine ⟨31843544199487762060832467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42458058932650349414443289 31843544199487762060832467)
          ·
            refine ⟨47765316299231643091248701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31843544199487762060832467 47765316299231643091248701)
            ·
              refine ⟨17911993612211866159218263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47765316299231643091248701 17911993612211866159218263)
              ·
                refine ⟨26867990418317799238827395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17911993612211866159218263 26867990418317799238827395)
                ·
                  refine ⟨40301985627476698858241093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26867990418317799238827395 40301985627476698858241093)
                  ·
                    refine ⟨7556622305151881035920205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40301985627476698858241093 7556622305151881035920205)
                    ·
                      refine ⟨2833733364431955388470077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556622305151881035920205 2833733364431955388470077)
                      ·
                        rfl

theorem cell23_5518676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_5518676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518676 prefixEnd_5518676 := by exact prefixLift 5518676
  have htrace : WordTrace (prefixWord ++ tailWord_5518676) baseStart_5518676 baseEnd_5518676 := by
    simpa [prefixWord, tailWord_5518676, baseEnd_5518676] using wordTrace_append hprefix tailTrace_5518676
  have hstable : (prefixWord ++ tailWord_5518676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518676).length < 2 ^ (prefixWord ++ tailWord_5518676).sum := by decide
  have hdescent : baseEnd_5518676 < baseStart_5518676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518689 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_5518689 : Nat := 118140960795 + 5518689 * 2 ^ 59
def prefixEnd_5518689 : Nat := 4983230072969 + 3 ^ 40 * 5518689 * 2
def baseEnd_5518689 : Nat := 2833740039680463837607517

theorem tailTrace_5518689 : CollatzResearch.WordTrace tailWord_5518689 prefixEnd_5518689 2833740039680463837607517 := by
  unfold tailWord_5518689
  simp only [CollatzResearch.WordTrace]
  refine ⟨201283123903739744888695121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134188749269159829925796747 201283123903739744888695121)
  ·
    refine ⟨150962342927804808666521341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201283123903739744888695121 150962342927804808666521341)
    ·
      refine ⟨56610878597926803249945503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150962342927804808666521341 56610878597926803249945503)
      ·
        refine ⟨84916317896890204874918255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56610878597926803249945503 84916317896890204874918255)
        ·
          refine ⟨127374476845335307312377383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84916317896890204874918255 127374476845335307312377383)
          ·
            refine ⟨191061715268002960968566075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127374476845335307312377383 191061715268002960968566075)
            ·
              refine ⟨286592572902004441452849113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191061715268002960968566075 286592572902004441452849113)
              ·
                refine ⟨214944429676503331089636835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286592572902004441452849113 214944429676503331089636835)
                ·
                  refine ⟨322416644514754996634455253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214944429676503331089636835 322416644514754996634455253)
                  ·
                    refine ⟨7556640105814570233620045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 322416644514754996634455253 7556640105814570233620045)
                    ·
                      refine ⟨2833740039680463837607517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556640105814570233620045 2833740039680463837607517)
                      ·
                        rfl

theorem cell23_5518689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_5518689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518689 prefixEnd_5518689 := by exact prefixLift 5518689
  have htrace : WordTrace (prefixWord ++ tailWord_5518689) baseStart_5518689 baseEnd_5518689 := by
    simpa [prefixWord, tailWord_5518689, baseEnd_5518689] using wordTrace_append hprefix tailTrace_5518689
  have hstable : (prefixWord ++ tailWord_5518689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518689).length < 2 ^ (prefixWord ++ tailWord_5518689).sum := by decide
  have hdescent : baseEnd_5518689 < baseStart_5518689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518696 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 8]
def baseStart_5518696 : Nat := 118140960795 + 5518696 * 2 ^ 59
def prefixEnd_5518696 : Nat := 4983230072969 + 3 ^ 40 * 5518696 * 2
def baseEnd_5518696 : Nat := 314860403782782812246665

theorem tailTrace_5518696 : CollatzResearch.WordTrace tailWord_5518696 prefixEnd_5518696 314860403782782812246665 := by
  unfold tailWord_5518696
  simp only [CollatzResearch.WordTrace]
  refine ⟨100641689607357192542099971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134188919476476256722799961 100641689607357192542099971)
  ·
    refine ⟨150962534411035788813149957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100641689607357192542099971 150962534411035788813149957)
    ·
      refine ⟨28305475202069210402465617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150962534411035788813149957 28305475202069210402465617)
      ·
        refine ⟨21229106401551907801849213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28305475202069210402465617 21229106401551907801849213)
        ·
          refine ⟨7960914900581965425693455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21229106401551907801849213 7960914900581965425693455)
          ·
            refine ⟨11941372350872948138540183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7960914900581965425693455 11941372350872948138540183)
            ·
              refine ⟨17912058526309422207810275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11941372350872948138540183 17912058526309422207810275)
              ·
                refine ⟨26868087789464133311715413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17912058526309422207810275 26868087789464133311715413)
                ·
                  refine ⟨314860403782782812246665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26868087789464133311715413 314860403782782812246665)
                  ·
                    rfl

theorem cell23_5518696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_5518696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518696 prefixEnd_5518696 := by exact prefixLift 5518696
  have htrace : WordTrace (prefixWord ++ tailWord_5518696) baseStart_5518696 baseEnd_5518696 := by
    simpa [prefixWord, tailWord_5518696, baseEnd_5518696] using wordTrace_append hprefix tailTrace_5518696
  have hstable : (prefixWord ++ tailWord_5518696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518696).length < 2 ^ (prefixWord ++ tailWord_5518696).sum := by decide
  have hdescent : baseEnd_5518696 < baseStart_5518696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518716 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_5518716 : Nat := 118140960795 + 5518716 * 2 ^ 59
def prefixEnd_5518716 : Nat := 4983230072969 + 3 ^ 40 * 5518716 * 2
def baseEnd_5518716 : Nat := 2833753903658135231969893

theorem tailTrace_5518716 : CollatzResearch.WordTrace tailWord_5518716 prefixEnd_5518716 2833753903658135231969893 := by
  unfold tailWord_5518716
  simp only [CollatzResearch.WordTrace]
  refine ⟨100642054337320964249964001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134189405783094618999952001 100642054337320964249964001)
  ·
    refine ⟨75481540752990723187473001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100642054337320964249964001 75481540752990723187473001)
    ·
      refine ⟨56611155564743042390604751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75481540752990723187473001 56611155564743042390604751)
      ·
        refine ⟨84916733347114563585907127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56611155564743042390604751 84916733347114563585907127)
        ·
          refine ⟨127375100020671845378860691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84916733347114563585907127 127375100020671845378860691)
          ·
            refine ⟨191062650031007768068291037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127375100020671845378860691 191062650031007768068291037)
            ·
              refine ⟨71648493761627913025609139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191062650031007768068291037 71648493761627913025609139)
              ·
                refine ⟨107472740642441869538413709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71648493761627913025609139 107472740642441869538413709)
                ·
                  refine ⟨40302277740915701076905141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107472740642441869538413709 40302277740915701076905141)
                  ·
                    refine ⟨3778338538210846975959857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40302277740915701076905141 3778338538210846975959857)
                    ·
                      refine ⟨2833753903658135231969893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778338538210846975959857 2833753903658135231969893)
                      ·
                        rfl

theorem cell23_5518716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_5518716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518716 prefixEnd_5518716 := by exact prefixLift 5518716
  have htrace : WordTrace (prefixWord ++ tailWord_5518716) baseStart_5518716 baseEnd_5518716 := by
    simpa [prefixWord, tailWord_5518716, baseEnd_5518716] using wordTrace_append hprefix tailTrace_5518716
  have hstable : (prefixWord ++ tailWord_5518716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518716).length < 2 ^ (prefixWord ++ tailWord_5518716).sum := by decide
  have hdescent : baseEnd_5518716 < baseStart_5518716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518723 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 3]
def baseStart_5518723 : Nat := 118140960795 + 5518723 * 2 ^ 59
def prefixEnd_5518723 : Nat := 4983230072969 + 3 ^ 40 * 5518723 * 2
def baseEnd_5518723 : Nat := 2833757498022716704582361

theorem tailTrace_5518723 : CollatzResearch.WordTrace tailWord_5518723 prefixEnd_5518723 2833757498022716704582361 := by
  unfold tailWord_5518723
  simp only [CollatzResearch.WordTrace]
  refine ⟨201284363985616568695432823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134189575990411045796955215 201284363985616568695432823)
  ·
    refine ⟨301926545978424853043149235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201284363985616568695432823 301926545978424853043149235)
    ·
      refine ⟨452889818967637279564723853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301926545978424853043149235 452889818967637279564723853)
      ·
        refine ⟨169833682112863979836771445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 452889818967637279564723853 169833682112863979836771445)
        ·
          refine ⟨15921907698080998109697323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169833682112863979836771445 15921907698080998109697323)
          ·
            refine ⟨23882861547121497164545985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921907698080998109697323 23882861547121497164545985)
            ·
              refine ⟨17912146160341122873409489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23882861547121497164545985 17912146160341122873409489)
              ·
                refine ⟨13434109620255842155057117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17912146160341122873409489 13434109620255842155057117)
                ·
                  refine ⟨5037791107595940808146419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13434109620255842155057117 5037791107595940808146419)
                  ·
                    refine ⟨7556686661393911212219629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5037791107595940808146419 7556686661393911212219629)
                    ·
                      refine ⟨2833757498022716704582361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556686661393911212219629 2833757498022716704582361)
                      ·
                        rfl

theorem cell23_5518723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_5518723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518723 prefixEnd_5518723 := by exact prefixLift 5518723
  have htrace : WordTrace (prefixWord ++ tailWord_5518723) baseStart_5518723 baseEnd_5518723 := by
    simpa [prefixWord, tailWord_5518723, baseEnd_5518723] using wordTrace_append hprefix tailTrace_5518723
  have hstable : (prefixWord ++ tailWord_5518723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518723).length < 2 ^ (prefixWord ++ tailWord_5518723).sum := by decide
  have hdescent : baseEnd_5518723 < baseStart_5518723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518734 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_5518734 : Nat := 118140960795 + 5518734 * 2 ^ 59
def prefixEnd_5518734 : Nat := 4983230072969 + 3 ^ 40 * 5518734 * 2
def baseEnd_5518734 : Nat := 944587715436638720514937

theorem tailTrace_5518734 : CollatzResearch.WordTrace tailWord_5518734 prefixEnd_5518734 944587715436638720514937 := by
  unfold tailWord_5518734
  simp only [CollatzResearch.WordTrace]
  refine ⟨25160595648572089696760407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134189843459051145049388837 25160595648572089696760407)
  ·
    refine ⟨37740893472858134545140611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25160595648572089696760407 37740893472858134545140611)
    ·
      refine ⟨56611340209287201817710917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37740893472858134545140611 56611340209287201817710917)
      ·
        refine ⟨10614626289241350340820797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56611340209287201817710917 10614626289241350340820797)
        ·
          refine ⟨3980484858465506377807799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10614626289241350340820797 3980484858465506377807799)
          ·
            refine ⟨5970727287698259566711699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980484858465506377807799 5970727287698259566711699)
            ·
              refine ⟨8956090931547389350067549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5970727287698259566711699 8956090931547389350067549)
              ·
                refine ⟨3358534099330271006275331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8956090931547389350067549 3358534099330271006275331)
                ·
                  refine ⟨5037801148995406509412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358534099330271006275331 5037801148995406509412997)
                  ·
                    refine ⟨944587715436638720514937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5037801148995406509412997 944587715436638720514937)
                    ·
                      rfl

theorem cell23_5518734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_5518734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518734 prefixEnd_5518734 := by exact prefixLift 5518734
  have htrace : WordTrace (prefixWord ++ tailWord_5518734) baseStart_5518734 baseEnd_5518734 := by
    simpa [prefixWord, tailWord_5518734, baseEnd_5518734] using wordTrace_append hprefix tailTrace_5518734
  have hstable : (prefixWord ++ tailWord_5518734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518734).length < 2 ^ (prefixWord ++ tailWord_5518734).sum := by decide
  have hdescent : baseEnd_5518734 < baseStart_5518734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518830 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_5518830 : Nat := 118140960795 + 5518830 * 2 ^ 59
def prefixEnd_5518830 : Nat := 4983230072969 + 3 ^ 40 * 5518830 * 2
def baseEnd_5518830 : Nat := 2833812440452747785944369

theorem tailTrace_5518830 : CollatzResearch.WordTrace tailWord_5518830 prefixEnd_5518830 2833812440452747785944369 := by
  unfold tailWord_5518830
  simp only [CollatzResearch.WordTrace]
  refine ⟨25161033324528615746197243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134192177730819283979718629 25161033324528615746197243)
  ·
    refine ⟨37741549986792923619295865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25161033324528615746197243 37741549986792923619295865)
    ·
      refine ⟨28306162490094692714471899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37741549986792923619295865 28306162490094692714471899)
      ·
        refine ⟨42459243735142039071707849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28306162490094692714471899 42459243735142039071707849)
        ·
          refine ⟨31844432801356529303780887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42459243735142039071707849 31844432801356529303780887)
          ·
            refine ⟨47766649202034793955671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31844432801356529303780887 47766649202034793955671331)
            ·
              refine ⟨71649973803052190933506997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47766649202034793955671331 71649973803052190933506997)
              ·
                refine ⟨6717185044036142900016281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71649973803052190933506997 6717185044036142900016281)
                ·
                  refine ⟨5037888783027107175012211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717185044036142900016281 5037888783027107175012211)
                  ·
                    refine ⟨7556833174540660762518317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5037888783027107175012211 7556833174540660762518317)
                    ·
                      refine ⟨2833812440452747785944369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7556833174540660762518317 2833812440452747785944369)
                      ·
                        rfl

theorem cell23_5518830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_5518830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518830 prefixEnd_5518830 := by exact prefixLift 5518830
  have htrace : WordTrace (prefixWord ++ tailWord_5518830) baseStart_5518830 baseEnd_5518830 := by
    simpa [prefixWord, tailWord_5518830, baseEnd_5518830] using wordTrace_append hprefix tailTrace_5518830
  have hstable : (prefixWord ++ tailWord_5518830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518830).length < 2 ^ (prefixWord ++ tailWord_5518830).sum := by decide
  have hdescent : baseEnd_5518830 < baseStart_5518830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518856 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5518856 : Nat := 118140960795 + 5518856 * 2 ^ 59
def prefixEnd_5518856 : Nat := 4983230072969 + 3 ^ 40 * 5518856 * 2
def baseEnd_5518856 : Nat := 2833825790949764684219249

theorem tailTrace_5518856 : CollatzResearch.WordTrace tailWord_5518856 prefixEnd_5518856 2833825790949764684219249 := by
  unfold tailWord_5518856
  simp only [CollatzResearch.WordTrace]
  refine ⟨100644607447067366205012211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134192809929423154940016281 100644607447067366205012211)
  ·
    refine ⟨150966911170601049307518317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100644607447067366205012211 150966911170601049307518317)
    ·
      refine ⟨56612591688975393490319369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150966911170601049307518317 56612591688975393490319369)
      ·
        refine ⟨42459443766731545117739527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56612591688975393490319369 42459443766731545117739527)
        ·
          refine ⟨63689165650097317676609291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42459443766731545117739527 63689165650097317676609291)
          ·
            refine ⟨95533748475145976514913937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63689165650097317676609291 95533748475145976514913937)
            ·
              refine ⟨71650311356359482386185453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95533748475145976514913937 71650311356359482386185453)
              ·
                refine ⟨26868866758634805894819545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71650311356359482386185453 26868866758634805894819545)
                ·
                  refine ⟨20151650068976104421114659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26868866758634805894819545 20151650068976104421114659)
                  ·
                    refine ⟨30227475103464156631671989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20151650068976104421114659 30227475103464156631671989)
                    ·
                      refine ⟨2833825790949764684219249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30227475103464156631671989 2833825790949764684219249)
                      ·
                        rfl

theorem cell23_5518856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5518856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518856 prefixEnd_5518856 := by exact prefixLift 5518856
  have htrace : WordTrace (prefixWord ++ tailWord_5518856) baseStart_5518856 baseEnd_5518856 := by
    simpa [prefixWord, tailWord_5518856, baseEnd_5518856] using wordTrace_append hprefix tailTrace_5518856
  have hstable : (prefixWord ++ tailWord_5518856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518856).length < 2 ^ (prefixWord ++ tailWord_5518856).sum := by decide
  have hdescent : baseEnd_5518856 < baseStart_5518856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518906 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_5518906 : Nat := 118140960795 + 5518906 * 2 ^ 59
def prefixEnd_5518906 : Nat := 4983230072969 + 3 ^ 40 * 5518906 * 2
def baseEnd_5518906 : Nat := 944617154994163162864673

theorem tailTrace_5518906 : CollatzResearch.WordTrace tailWord_5518906 prefixEnd_5518906 944617154994163162864673 := by
  unfold tailWord_5518906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50322759635988397737336143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134194025695969060632896381 50322759635988397737336143)
  ·
    refine ⟨75484139453982596606004215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50322759635988397737336143 75484139453982596606004215)
    ·
      refine ⟨113226209180973894909006323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75484139453982596606004215 113226209180973894909006323)
      ·
        refine ⟨169839313771460842363509485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113226209180973894909006323 169839313771460842363509485)
        ·
          refine ⟨63689742664297815886316057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169839313771460842363509485 63689742664297815886316057)
          ·
            refine ⟨47767306998223361914737043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63689742664297815886316057 47767306998223361914737043)
            ·
              refine ⟨71650960497335042872105565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47767306998223361914737043 71650960497335042872105565)
              ·
                refine ⟨26869110186500641077039587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71650960497335042872105565 26869110186500641077039587)
                ·
                  refine ⟨40303665279750961615559381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26869110186500641077039587 40303665279750961615559381)
                  ·
                    refine ⟨944617154994163162864673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40303665279750961615559381 944617154994163162864673)
                    ·
                      rfl

theorem cell23_5518906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_5518906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518906 prefixEnd_5518906 := by exact prefixLift 5518906
  have htrace : WordTrace (prefixWord ++ tailWord_5518906) baseStart_5518906 baseEnd_5518906 := by
    simpa [prefixWord, tailWord_5518906, baseEnd_5518906] using wordTrace_append hprefix tailTrace_5518906
  have hstable : (prefixWord ++ tailWord_5518906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518906).length < 2 ^ (prefixWord ++ tailWord_5518906).sum := by decide
  have hdescent : baseEnd_5518906 < baseStart_5518906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518953 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 3, 4]
def baseStart_5518953 : Nat := 118140960795 + 5518953 * 2 ^ 59
def prefixEnd_5518953 : Nat := 4983230072969 + 3 ^ 40 * 5518953 * 2
def baseEnd_5518953 : Nat := 944625199524416934902101

theorem tailTrace_5518953 : CollatzResearch.WordTrace tailWord_5518953 prefixEnd_5518953 944625199524416934902101 := by
  unfold tailWord_5518953
  simp only [CollatzResearch.WordTrace]
  refine ⟨201292752774783317976305513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134195168516522211984203675 201292752774783317976305513)
  ·
    refine ⟨150969564581087488482229135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201292752774783317976305513 150969564581087488482229135)
    ·
      refine ⟨226454346871631232723343703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150969564581087488482229135 226454346871631232723343703)
      ·
        refine ⟨339681520307446849085015555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226454346871631232723343703 339681520307446849085015555)
        ·
          refine ⟨509522280461170273627523333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339681520307446849085015555 509522280461170273627523333)
          ·
            refine ⟨95535427586469426305160625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 509522280461170273627523333 95535427586469426305160625)
            ·
              refine ⟨71651570689852069728870469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95535427586469426305160625 71651570689852069728870469)
              ·
                refine ⟨13434669504347263074163213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71651570689852069728870469 13434669504347263074163213)
                ·
                  refine ⟨5038001064130223652811205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13434669504347263074163213 5038001064130223652811205)
                  ·
                    refine ⟨944625199524416934902101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038001064130223652811205 944625199524416934902101)
                    ·
                      rfl

theorem cell23_5518953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_5518953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518953 prefixEnd_5518953 := by exact prefixLift 5518953
  have htrace : WordTrace (prefixWord ++ tailWord_5518953) baseStart_5518953 baseEnd_5518953 := by
    simpa [prefixWord, tailWord_5518953, baseEnd_5518953] using wordTrace_append hprefix tailTrace_5518953
  have hstable : (prefixWord ++ tailWord_5518953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518953).length < 2 ^ (prefixWord ++ tailWord_5518953).sum := by decide
  have hdescent : baseEnd_5518953 < baseStart_5518953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518956 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_5518956 : Nat := 118140960795 + 5518956 * 2 ^ 59
def prefixEnd_5518956 : Nat := 4983230072969 + 3 ^ 40 * 5518956 * 2
def baseEnd_5518956 : Nat := 2833877139015214292968789

theorem tailTrace_5518956 : CollatzResearch.WordTrace tailWord_5518956 prefixEnd_5518956 2833877139015214292968789 := by
  unfold tailWord_5518956
  simp only [CollatzResearch.WordTrace]
  refine ⟨100646431096886224744332361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134195241462514966325776481 100646431096886224744332361)
  ·
    refine ⟨75484823322664668558249271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100646431096886224744332361 75484823322664668558249271)
    ·
      refine ⟨113227234983997002837373907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75484823322664668558249271 113227234983997002837373907)
      ·
        refine ⟨169840852475995504256060861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113227234983997002837373907 169840852475995504256060861)
        ·
          refine ⟨63690319678498314096022823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169840852475995504256060861 63690319678498314096022823)
          ·
            refine ⟨95535479517747471144034235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63690319678498314096022823 95535479517747471144034235)
            ·
              refine ⟨143303219276621206716051353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95535479517747471144034235 143303219276621206716051353)
              ·
                refine ⟨107477414457465905037038515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143303219276621206716051353 107477414457465905037038515)
                ·
                  refine ⟨161216121686198857555557773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107477414457465905037038515 161216121686198857555557773)
                  ·
                    refine ⟨60456045632324571583334165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161216121686198857555557773 60456045632324571583334165)
                    ·
                      refine ⟨2833877139015214292968789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60456045632324571583334165 2833877139015214292968789)
                      ·
                        rfl

theorem cell23_5518956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_5518956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518956 prefixEnd_5518956 := by exact prefixLift 5518956
  have htrace : WordTrace (prefixWord ++ tailWord_5518956) baseStart_5518956 baseEnd_5518956 := by
    simpa [prefixWord, tailWord_5518956, baseEnd_5518956] using wordTrace_append hprefix tailTrace_5518956
  have hstable : (prefixWord ++ tailWord_5518956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518956).length < 2 ^ (prefixWord ++ tailWord_5518956).sum := by decide
  have hdescent : baseEnd_5518956 < baseStart_5518956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518960 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_5518960 : Nat := 118140960795 + 5518960 * 2 ^ 59
def prefixEnd_5518960 : Nat := 4983230072969 + 3 ^ 40 * 5518960 * 2
def baseEnd_5518960 : Nat := 2833879192937832277318771

theorem tailTrace_5518960 : CollatzResearch.WordTrace tailWord_5518960 prefixEnd_5518960 2833879192937832277318771 := by
  unfold tailWord_5518960
  simp only [CollatzResearch.WordTrace]
  refine ⟨100646504042878979085905167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134195338723838638781206889 100646504042878979085905167)
  ·
    refine ⟨150969756064318468628857751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100646504042878979085905167 150969756064318468628857751)
    ·
      refine ⟨226454634096477702943286627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150969756064318468628857751 226454634096477702943286627)
      ·
        refine ⟨339681951144716554414929941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226454634096477702943286627 339681951144716554414929941)
        ·
          refine ⟨15922591459908588488199841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 339681951144716554414929941 15922591459908588488199841)
          ·
            refine ⟨11941943594931441366149881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15922591459908588488199841 11941943594931441366149881)
            ·
              refine ⟨8956457696198581024612411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11941943594931441366149881 8956457696198581024612411)
              ·
                refine ⟨13434686544297871536918617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8956457696198581024612411 13434686544297871536918617)
                ·
                  refine ⟨10076014908223403652688963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13434686544297871536918617 10076014908223403652688963)
                  ·
                    refine ⟨15114022362335105479033445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10076014908223403652688963 15114022362335105479033445)
                    ·
                      refine ⟨2833879192937832277318771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15114022362335105479033445 2833879192937832277318771)
                      ·
                        rfl

theorem cell23_5518960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_5518960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518960 prefixEnd_5518960 := by exact prefixLift 5518960
  have htrace : WordTrace (prefixWord ++ tailWord_5518960) baseStart_5518960 baseEnd_5518960 := by
    simpa [prefixWord, tailWord_5518960, baseEnd_5518960] using wordTrace_append hprefix tailTrace_5518960
  have hstable : (prefixWord ++ tailWord_5518960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518960).length < 2 ^ (prefixWord ++ tailWord_5518960).sum := by decide
  have hdescent : baseEnd_5518960 < baseStart_5518960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5518983 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 6]
def baseStart_5518983 : Nat := 118140960795 + 5518983 * 2 ^ 59
def prefixEnd_5518983 : Nat := 4983230072969 + 3 ^ 40 * 5518983 * 2
def baseEnd_5518983 : Nat := 314876778110320631925685

theorem tailTrace_5518983 : CollatzResearch.WordTrace tailWord_5518983 prefixEnd_5518983 314876778110320631925685 := by
  unfold tailWord_5518983
  simp only [CollatzResearch.WordTrace]
  refine ⟨201293846964674633099897603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134195897976449755399931735 201293846964674633099897603)
  ·
    refine ⟨301940770447011949649846405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201293846964674633099897603 301940770447011949649846405)
    ·
      refine ⟨56613894458814740559346201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301940770447011949649846405 56613894458814740559346201)
      ·
        refine ⟨42460420844111055419509651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56613894458814740559346201 42460420844111055419509651)
        ·
          refine ⟨63690631266166583129264477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42460420844111055419509651 63690631266166583129264477)
          ·
            refine ⟨23883986724812468673474179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63690631266166583129264477 23883986724812468673474179)
            ·
              refine ⟨35825980087218703010211269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23883986724812468673474179 35825980087218703010211269)
              ·
                refine ⟨6717371266353506814414613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35825980087218703010211269 6717371266353506814414613)
                ·
                  refine ⟨314876778110320631925685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6717371266353506814414613 314876778110320631925685)
                  ·
                    rfl

theorem cell23_5518983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 6].length) (baseStart_5518983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5518983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5518983 prefixEnd_5518983 := by exact prefixLift 5518983
  have htrace : WordTrace (prefixWord ++ tailWord_5518983) baseStart_5518983 baseEnd_5518983 := by
    simpa [prefixWord, tailWord_5518983, baseEnd_5518983] using wordTrace_append hprefix tailTrace_5518983
  have hstable : (prefixWord ++ tailWord_5518983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5518983).length < 2 ^ (prefixWord ++ tailWord_5518983).sum := by decide
  have hdescent : baseEnd_5518983 < baseStart_5518983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5518983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519013 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_5519013 : Nat := 118140960795 + 5519013 * 2 ^ 59
def prefixEnd_5519013 : Nat := 4983230072969 + 3 ^ 40 * 5519013 * 2
def baseEnd_5519013 : Nat := 944635469137506856652009

theorem tailTrace_5519013 : CollatzResearch.WordTrace tailWord_5519013 prefixEnd_5519013 944635469137506856652009 := by
  unfold tailWord_5519013
  simp only [CollatzResearch.WordTrace]
  refine ⟨201294941154565948223489693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134196627436377298815659795 201294941154565948223489693)
  ·
    refine ⟨75485602932962230583808635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201294941154565948223489693 75485602932962230583808635)
    ·
      refine ⟨113228404399443345875712953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75485602932962230583808635 113228404399443345875712953)
      ·
        refine ⟨84921303299582509406784715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113228404399443345875712953 84921303299582509406784715)
        ·
          refine ⟨127381954949373764110177073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84921303299582509406784715 127381954949373764110177073)
          ·
            refine ⟨95536466212030323082632805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127381954949373764110177073 95536466212030323082632805)
            ·
              refine ⟨17913087414755685577993651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95536466212030323082632805 17913087414755685577993651)
              ·
                refine ⟨26869631122133528366990477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17913087414755685577993651 26869631122133528366990477)
                ·
                  refine ⟨10076111670800073137621429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26869631122133528366990477 10076111670800073137621429)
                  ·
                    refine ⟨944635469137506856652009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10076111670800073137621429 944635469137506856652009)
                    ·
                      rfl

theorem cell23_5519013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_5519013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519013 prefixEnd_5519013 := by exact prefixLift 5519013
  have htrace : WordTrace (prefixWord ++ tailWord_5519013) baseStart_5519013 baseEnd_5519013 := by
    simpa [prefixWord, tailWord_5519013, baseEnd_5519013] using wordTrace_append hprefix tailTrace_5519013
  have hstable : (prefixWord ++ tailWord_5519013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519013).length < 2 ^ (prefixWord ++ tailWord_5519013).sum := by decide
  have hdescent : baseEnd_5519013 < baseStart_5519013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519044 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_5519044 : Nat := 118140960795 + 5519044 * 2 ^ 59
def prefixEnd_5519044 : Nat := 4983230072969 + 3 ^ 40 * 5519044 * 2
def baseEnd_5519044 : Nat := 2833922325312809948668385

theorem tailTrace_5519044 : CollatzResearch.WordTrace tailWord_5519044 prefixEnd_5519044 2833922325312809948668385 := by
  unfold tailWord_5519044
  simp only [CollatzResearch.WordTrace]
  refine ⟨100648035908726820258934093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134197381211635760345245457 100648035908726820258934093)
  ·
    refine ⟨37743013465772557597100285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100648035908726820258934093 37743013465772557597100285)
    ·
      refine ⟨14153630049664709098912607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37743013465772557597100285 14153630049664709098912607)
      ·
        refine ⟨21230445074497063648368911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14153630049664709098912607 21230445074497063648368911)
        ·
          refine ⟨31845667611745595472553367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21230445074497063648368911 31845667611745595472553367)
          ·
            refine ⟨47768501417618393208830051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31845667611745595472553367 47768501417618393208830051)
            ·
              refine ⟨71652752126427589813245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47768501417618393208830051 71652752126427589813245077)
              ·
                refine ⟨3358722755926293272495863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71652752126427589813245077 3358722755926293272495863)
                ·
                  refine ⟨5038084133889439908743795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358722755926293272495863 5038084133889439908743795)
                  ·
                    refine ⟨7557126200834159863115693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038084133889439908743795 7557126200834159863115693)
                    ·
                      refine ⟨2833922325312809948668385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557126200834159863115693 2833922325312809948668385)
                      ·
                        rfl

theorem cell23_5519044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_5519044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519044 prefixEnd_5519044 := by exact prefixLift 5519044
  have htrace : WordTrace (prefixWord ++ tailWord_5519044) baseStart_5519044 baseEnd_5519044 := by
    simpa [prefixWord, tailWord_5519044, baseEnd_5519044] using wordTrace_append hprefix tailTrace_5519044
  have hstable : (prefixWord ++ tailWord_5519044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519044).length < 2 ^ (prefixWord ++ tailWord_5519044).sum := by decide
  have hdescent : baseEnd_5519044 < baseStart_5519044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519063 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_5519063 : Nat := 118140960795 + 5519063 * 2 ^ 59
def prefixEnd_5519063 : Nat := 4983230072969 + 3 ^ 40 * 5519063 * 2
def baseEnd_5519063 : Nat := 2833932081445245374330797

theorem tailTrace_5519063 : CollatzResearch.WordTrace tailWord_5519063 prefixEnd_5519063 2833932081445245374330797 := by
  unfold tailWord_5519063
  simp only [CollatzResearch.WordTrace]
  refine ⟨201296764804384806762809843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134197843202923204508539895 201296764804384806762809843)
  ·
    refine ⟨301945147206577210144214765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201296764804384806762809843 301945147206577210144214765)
    ·
      refine ⟨113229430202466453804080537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301945147206577210144214765 113229430202466453804080537)
      ·
        refine ⟨84922072651849840353060403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113229430202466453804080537 84922072651849840353060403)
        ·
          refine ⟨127383108977774760529590605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84922072651849840353060403 127383108977774760529590605)
          ·
            refine ⟨47768665866665535198596477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127383108977774760529590605 47768665866665535198596477)
            ·
              refine ⟨17913249699999575699473679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47768665866665535198596477 17913249699999575699473679)
              ·
                refine ⟨26869874549999363549210519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17913249699999575699473679 26869874549999363549210519)
                ·
                  refine ⟨40304811824999045323815779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26869874549999363549210519 40304811824999045323815779)
                  ·
                    refine ⟨60457217737498567985723669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40304811824999045323815779 60457217737498567985723669)
                    ·
                      refine ⟨2833932081445245374330797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60457217737498567985723669 2833932081445245374330797)
                      ·
                        rfl

theorem cell23_5519063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_5519063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519063 prefixEnd_5519063 := by exact prefixLift 5519063
  have htrace : WordTrace (prefixWord ++ tailWord_5519063) baseStart_5519063 baseEnd_5519063 := by
    simpa [prefixWord, tailWord_5519063, baseEnd_5519063] using wordTrace_append hprefix tailTrace_5519063
  have hstable : (prefixWord ++ tailWord_5519063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519063).length < 2 ^ (prefixWord ++ tailWord_5519063).sum := by decide
  have hdescent : baseEnd_5519063 < baseStart_5519063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519111 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 2, 4]
def baseStart_5519111 : Nat := 118140960795 + 5519111 * 2 ^ 59
def prefixEnd_5519111 : Nat := 4983230072969 + 3 ^ 40 * 5519111 * 2
def baseEnd_5519111 : Nat := 944652242838887062176859

theorem tailTrace_5519111 : CollatzResearch.WordTrace tailWord_5519111 prefixEnd_5519111 944652242838887062176859 := by
  unfold tailWord_5519111
  simp only [CollatzResearch.WordTrace]
  refine ⟨201298515508210910960557187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134199010338807273973704791 201298515508210910960557187)
  ·
    refine ⟨301947773262316366440835781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201298515508210910960557187 301947773262316366440835781)
    ·
      refine ⟨56615207486684318707656709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301947773262316366440835781 56615207486684318707656709)
      ·
        refine ⟨10615351403753309757685633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56615207486684318707656709 10615351403753309757685633)
        ·
          refine ⟨7961513552814982318264225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10615351403753309757685633 7961513552814982318264225)
          ·
            refine ⟨5971135164611236738698169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7961513552814982318264225 5971135164611236738698169)
            ·
              refine ⟨4478351373458427554023627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971135164611236738698169 4478351373458427554023627)
              ·
                refine ⟨6717527060187641331035441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478351373458427554023627 6717527060187641331035441)
                ·
                  refine ⟨5038145295140730998276581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717527060187641331035441 5038145295140730998276581)
                  ·
                    refine ⟨944652242838887062176859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038145295140730998276581 944652242838887062176859)
                    ·
                      rfl

theorem cell23_5519111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_5519111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519111 prefixEnd_5519111 := by exact prefixLift 5519111
  have htrace : WordTrace (prefixWord ++ tailWord_5519111) baseStart_5519111 baseEnd_5519111 := by
    simpa [prefixWord, tailWord_5519111, baseEnd_5519111] using wordTrace_append hprefix tailTrace_5519111
  have hstable : (prefixWord ++ tailWord_5519111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519111).length < 2 ^ (prefixWord ++ tailWord_5519111).sum := by decide
  have hdescent : baseEnd_5519111 < baseStart_5519111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519123 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_5519123 : Nat := 118140960795 + 5519123 * 2 ^ 59
def prefixEnd_5519123 : Nat := 4983230072969 + 3 ^ 40 * 5519123 * 2
def baseEnd_5519123 : Nat := 2833962890284515139580521

theorem tailTrace_5519123 : CollatzResearch.WordTrace tailWord_5519123 prefixEnd_5519123 2833962890284515139580521 := by
  unfold tailWord_5519123
  simp only [CollatzResearch.WordTrace]
  refine ⟨201298953184167437009994023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134199302122778291339996015 201298953184167437009994023)
  ·
    refine ⟨301948429776251155514991035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201298953184167437009994023 301948429776251155514991035)
    ·
      refine ⟨452922644664376733272486553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301948429776251155514991035 452922644664376733272486553)
      ·
        refine ⟨339691983498282549954364915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452922644664376733272486553 339691983498282549954364915)
        ·
          refine ⟨509537975247423824931547373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339691983498282549954364915 509537975247423824931547373)
          ·
            refine ⟨191076740717783934349330265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509537975247423824931547373 191076740717783934349330265)
            ·
              refine ⟨143307555538337950761997699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191076740717783934349330265 143307555538337950761997699)
              ·
                refine ⟨214961333307506926142996549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143307555538337950761997699 214961333307506926142996549)
                ·
                  refine ⟨40305249995157548651811853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214961333307506926142996549 40305249995157548651811853)
                  ·
                    refine ⟨15114468748184080744429445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40305249995157548651811853 15114468748184080744429445)
                    ·
                      refine ⟨2833962890284515139580521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15114468748184080744429445 2833962890284515139580521)
                      ·
                        rfl

theorem cell23_5519123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_5519123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519123 prefixEnd_5519123 := by exact prefixLift 5519123
  have htrace : WordTrace (prefixWord ++ tailWord_5519123) baseStart_5519123 baseEnd_5519123 := by
    simpa [prefixWord, tailWord_5519123, baseEnd_5519123] using wordTrace_append hprefix tailTrace_5519123
  have hstable : (prefixWord ++ tailWord_5519123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519123).length < 2 ^ (prefixWord ++ tailWord_5519123).sum := by decide
  have hdescent : baseEnd_5519123 < baseStart_5519123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519160 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_5519160 : Nat := 118140960795 + 5519160 * 2 ^ 59
def prefixEnd_5519160 : Nat := 4983230072969 + 3 ^ 40 * 5519160 * 2
def baseEnd_5519160 : Nat := 2833981889068731494817851

theorem tailTrace_5519160 : CollatzResearch.WordTrace tailWord_5519160 prefixEnd_5519160 2833981889068731494817851 := by
  unfold tailWord_5519160
  simp only [CollatzResearch.WordTrace]
  refine ⟨100650151342516696164545467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134200201790022261552727289 100650151342516696164545467)
  ·
    refine ⟨150975227013775044246818201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100650151342516696164545467 150975227013775044246818201)
    ·
      refine ⟨113231420260331283185113651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150975227013775044246818201 113231420260331283185113651)
      ·
        refine ⟨169847130390496924777670477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113231420260331283185113651 169847130390496924777670477)
        ·
          refine ⟨63692673896436346791626429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169847130390496924777670477 63692673896436346791626429)
          ·
            refine ⟨23884752711163630046859911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63692673896436346791626429 23884752711163630046859911)
            ·
              refine ⟨35827129066745445070289867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23884752711163630046859911 35827129066745445070289867)
              ·
                refine ⟨53740693600118167605434801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35827129066745445070289867 53740693600118167605434801)
                ·
                  refine ⟨40305520200088625704076101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53740693600118167605434801 40305520200088625704076101)
                  ·
                    refine ⟨7557285037516617319514269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40305520200088625704076101 7557285037516617319514269)
                    ·
                      refine ⟨2833981889068731494817851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557285037516617319514269 2833981889068731494817851)
                      ·
                        rfl

theorem cell23_5519160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_5519160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519160 prefixEnd_5519160 := by exact prefixLift 5519160
  have htrace : WordTrace (prefixWord ++ tailWord_5519160) baseStart_5519160 baseEnd_5519160 := by
    simpa [prefixWord, tailWord_5519160, baseEnd_5519160] using wordTrace_append hprefix tailTrace_5519160
  have hstable : (prefixWord ++ tailWord_5519160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519160).length < 2 ^ (prefixWord ++ tailWord_5519160).sum := by decide
  have hdescent : baseEnd_5519160 < baseStart_5519160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519214 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_5519214 : Nat := 118140960795 + 5519214 * 2 ^ 59
def prefixEnd_5519214 : Nat := 4983230072969 + 3 ^ 40 * 5519214 * 2
def baseEnd_5519214 : Nat := 314889957447119364838067

theorem tailTrace_5519214 : CollatzResearch.WordTrace tailWord_5519214 prefixEnd_5519214 314889957447119364838067 := by
  unfold tailWord_5519214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25162784028354719943944587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134201514817891839701037797 25162784028354719943944587)
  ·
    refine ⟨37744176042532079915916881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25162784028354719943944587 37744176042532079915916881)
    ·
      refine ⟨28308132031899059936937661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37744176042532079915916881 28308132031899059936937661)
      ·
        refine ⟨10615549511962147476351623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28308132031899059936937661 10615549511962147476351623)
        ·
          refine ⟨15923324267943221214527435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10615549511962147476351623 15923324267943221214527435)
          ·
            refine ⟨23884986401914831821791153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15923324267943221214527435 23884986401914831821791153)
            ·
              refine ⟨17913739801436123866343365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23884986401914831821791153 17913739801436123866343365)
              ·
                refine ⟨3358826212769273224939381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17913739801436123866343365 3358826212769273224939381)
                ·
                  refine ⟨314889957447119364838067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3358826212769273224939381 314889957447119364838067)
                  ·
                    rfl

theorem cell23_5519214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_5519214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519214 prefixEnd_5519214 := by exact prefixLift 5519214
  have htrace : WordTrace (prefixWord ++ tailWord_5519214) baseStart_5519214 baseEnd_5519214 := by
    simpa [prefixWord, tailWord_5519214, baseEnd_5519214] using wordTrace_append hprefix tailTrace_5519214
  have hstable : (prefixWord ++ tailWord_5519214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519214).length < 2 ^ (prefixWord ++ tailWord_5519214).sum := by decide
  have hdescent : baseEnd_5519214 < baseStart_5519214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519325 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5519325 : Nat := 118140960795 + 5519325 * 2 ^ 59
def prefixEnd_5519325 : Nat := 4983230072969 + 3 ^ 40 * 5519325 * 2
def baseEnd_5519325 : Nat := 944688871125574449751531

theorem tailTrace_5519325 : CollatzResearch.WordTrace tailWord_5519325 prefixEnd_5519325 944688871125574449751531 := by
  unfold tailWord_5519325
  simp only [CollatzResearch.WordTrace]
  refine ⟨201306320729435625508847429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134204213819623750339231619 201306320729435625508847429)
  ·
    refine ⟨37744935136769179782908893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201306320729435625508847429 37744935136769179782908893)
    ·
      refine ⟨14154350676288442418590835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37744935136769179782908893 14154350676288442418590835)
      ·
        refine ⟨21231526014432663627886253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14154350676288442418590835 21231526014432663627886253)
        ·
          refine ⟨7961822255412248860457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21231526014432663627886253 7961822255412248860457345)
          ·
            refine ⟨5971366691559186645343009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7961822255412248860457345 5971366691559186645343009)
            ·
              refine ⟨4478525018669389984007257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971366691559186645343009 4478525018669389984007257)
              ·
                refine ⟨3358893764002042488005443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4478525018669389984007257 3358893764002042488005443)
                ·
                  refine ⟨5038340646003063732008165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3358893764002042488005443 5038340646003063732008165)
                  ·
                    refine ⟨944688871125574449751531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038340646003063732008165 944688871125574449751531)
                    ·
                      rfl

theorem cell23_5519325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5519325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519325 prefixEnd_5519325 := by exact prefixLift 5519325
  have htrace : WordTrace (prefixWord ++ tailWord_5519325) baseStart_5519325 baseEnd_5519325 := by
    simpa [prefixWord, tailWord_5519325, baseEnd_5519325] using wordTrace_append hprefix tailTrace_5519325
  have hstable : (prefixWord ++ tailWord_5519325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519325).length < 2 ^ (prefixWord ++ tailWord_5519325).sum := by decide
  have hdescent : baseEnd_5519325 < baseStart_5519325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519358 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5519358 : Nat := 118140960795 + 5519358 * 2 ^ 59
def prefixEnd_5519358 : Nat := 4983230072969 + 3 ^ 40 * 5519358 * 2
def baseEnd_5519358 : Nat := 2834083558238321720141941

theorem tailTrace_5519358 : CollatzResearch.WordTrace tailWord_5519358 prefixEnd_5519358 2834083558238321720141941 := by
  unfold tailWord_5519358
  simp only [CollatzResearch.WordTrace]
  refine ⟨25163440542289509018099841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134205016225544048096532485 25163440542289509018099841)
  ·
    refine ⟨18872580406717131763574881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25163440542289509018099841 18872580406717131763574881)
    ·
      refine ⟨14154435305037848822681161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18872580406717131763574881 14154435305037848822681161)
      ·
        refine ⟨10615826478778386617010871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14154435305037848822681161 10615826478778386617010871)
        ·
          refine ⟨15923739718167579925516307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10615826478778386617010871 15923739718167579925516307)
          ·
            refine ⟨23885609577251369888274461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15923739718167579925516307 23885609577251369888274461)
            ·
              refine ⟨8957103591469263708102923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23885609577251369888274461 8957103591469263708102923)
              ·
                refine ⟨13435655387203895562154385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957103591469263708102923 13435655387203895562154385)
                ·
                  refine ⟨10076741540402921671615789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13435655387203895562154385 10076741540402921671615789)
                  ·
                    refine ⟨3778778077651095626855921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10076741540402921671615789 3778778077651095626855921)
                    ·
                      refine ⟨2834083558238321720141941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778778077651095626855921 2834083558238321720141941)
                      ·
                        rfl

theorem cell23_5519358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5519358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519358 prefixEnd_5519358 := by exact prefixLift 5519358
  have htrace : WordTrace (prefixWord ++ tailWord_5519358) baseStart_5519358 baseEnd_5519358 := by
    simpa [prefixWord, tailWord_5519358, baseEnd_5519358] using wordTrace_append hprefix tailTrace_5519358
  have hstable : (prefixWord ++ tailWord_5519358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519358).length < 2 ^ (prefixWord ++ tailWord_5519358).sum := by decide
  have hdescent : baseEnd_5519358 < baseStart_5519358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519388 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5519388 : Nat := 118140960795 + 5519388 * 2 ^ 59
def prefixEnd_5519388 : Nat := 4983230072969 + 3 ^ 40 * 5519388 * 2
def baseEnd_5519388 : Nat := 2834098962657956602766803

theorem tailTrace_5519388 : CollatzResearch.WordTrace tailWord_5519388 prefixEnd_5519388 2834098962657956602766803 := by
  unfold tailWord_5519388
  simp only [CollatzResearch.WordTrace]
  refine ⟨100654309264103693634195409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134205745685471591512260545 100654309264103693634195409)
  ·
    refine ⟨75490731948077770225646557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100654309264103693634195409 75490731948077770225646557)
    ·
      refine ⟨28309024480529163834617459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75490731948077770225646557 28309024480529163834617459)
      ·
        refine ⟨42463536720793745751926189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28309024480529163834617459 42463536720793745751926189)
        ·
          refine ⟨15923826270297654656972321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42463536720793745751926189 15923826270297654656972321)
          ·
            refine ⟨11942869702723240992729241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15923826270297654656972321 11942869702723240992729241)
            ·
              refine ⟨8957152277042430744546931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11942869702723240992729241 8957152277042430744546931)
              ·
                refine ⟨13435728415563646116820397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957152277042430744546931 13435728415563646116820397)
                ·
                  refine ⟨5038398155836367293807649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13435728415563646116820397 5038398155836367293807649)
                  ·
                    refine ⟨3778798616877275470355737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038398155836367293807649 3778798616877275470355737)
                    ·
                      refine ⟨2834098962657956602766803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778798616877275470355737 2834098962657956602766803)
                      ·
                        rfl

theorem cell23_5519388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5519388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519388 prefixEnd_5519388 := by exact prefixLift 5519388
  have htrace : WordTrace (prefixWord ++ tailWord_5519388) baseStart_5519388 baseEnd_5519388 := by
    simpa [prefixWord, tailWord_5519388, baseEnd_5519388] using wordTrace_append hprefix tailTrace_5519388
  have hstable : (prefixWord ++ tailWord_5519388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519388).length < 2 ^ (prefixWord ++ tailWord_5519388).sum := by decide
  have hdescent : baseEnd_5519388 < baseStart_5519388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519431 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_5519431 : Nat := 118140960795 + 5519431 * 2 ^ 59
def prefixEnd_5519431 : Nat := 4983230072969 + 3 ^ 40 * 5519431 * 2
def baseEnd_5519431 : Nat := 2834121042326099934529105

theorem tailTrace_5519431 : CollatzResearch.WordTrace tailWord_5519431 prefixEnd_5519431 2834121042326099934529105 := by
  unfold tailWord_5519431
  simp only [CollatzResearch.WordTrace]
  refine ⟨201310186867051605612206147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134206791244701070408137431 201310186867051605612206147)
  ·
    refine ⟨301965280300577408418309221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201310186867051605612206147 301965280300577408418309221)
    ·
      refine ⟨56618490056358264078432979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301965280300577408418309221 56618490056358264078432979)
      ·
        refine ⟨84927735084537396117649469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56618490056358264078432979 84927735084537396117649469)
        ·
          refine ⟨31847900656701523544118551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84927735084537396117649469 31847900656701523544118551)
          ·
            refine ⟨47771850985052285316177827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31847900656701523544118551 47771850985052285316177827)
            ·
              refine ⟨71657776477578427974266741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47771850985052285316177827 71657776477578427974266741)
              ·
                refine ⟨6717916544772977622587507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71657776477578427974266741 6717916544772977622587507)
                ·
                  refine ⟨10076874817159466433881261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6717916544772977622587507 10076874817159466433881261)
                  ·
                    refine ⟨3778828056434799912705473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10076874817159466433881261 3778828056434799912705473)
                    ·
                      refine ⟨2834121042326099934529105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778828056434799912705473 2834121042326099934529105)
                      ·
                        rfl

theorem cell23_5519431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_5519431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519431 prefixEnd_5519431 := by exact prefixLift 5519431
  have htrace : WordTrace (prefixWord ++ tailWord_5519431) baseStart_5519431 baseEnd_5519431 := by
    simpa [prefixWord, tailWord_5519431, baseEnd_5519431] using wordTrace_append hprefix tailTrace_5519431
  have hstable : (prefixWord ++ tailWord_5519431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519431).length < 2 ^ (prefixWord ++ tailWord_5519431).sum := by decide
  have hdescent : baseEnd_5519431 < baseStart_5519431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519457 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_5519457 : Nat := 118140960795 + 5519457 * 2 ^ 59
def prefixEnd_5519457 : Nat := 4983230072969 + 3 ^ 40 * 5519457 * 2
def baseEnd_5519457 : Nat := 2834134392823116832803985

theorem tailTrace_5519457 : CollatzResearch.WordTrace tailWord_5519457 prefixEnd_5519457 2834134392823116832803985 := by
  unfold tailWord_5519457
  simp only [CollatzResearch.WordTrace]
  refine ⟨201311135164957412052652625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134207423443304941368435083 201311135164957412052652625)
  ·
    refine ⟨150983351373718059039489469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201311135164957412052652625 150983351373718059039489469)
    ·
      refine ⟨56618756765144272139808551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150983351373718059039489469 56618756765144272139808551)
      ·
        refine ⟨84928135147716408209712827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56618756765144272139808551 84928135147716408209712827)
        ·
          refine ⟨127392202721574612314569241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84928135147716408209712827 127392202721574612314569241)
          ·
            refine ⟨95544152041180959235926931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127392202721574612314569241 95544152041180959235926931)
            ·
              refine ⟨143316228061771438853890397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95544152041180959235926931 143316228061771438853890397)
              ·
                refine ⟨53743585523164289570208899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143316228061771438853890397 53743585523164289570208899)
                ·
                  refine ⟨80615378284746434355313349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53743585523164289570208899 80615378284746434355313349)
                  ·
                    refine ⟨15115383428389956441621253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80615378284746434355313349 15115383428389956441621253)
                    ·
                      refine ⟨2834134392823116832803985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15115383428389956441621253 2834134392823116832803985)
                      ·
                        rfl

theorem cell23_5519457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_5519457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519457 prefixEnd_5519457 := by exact prefixLift 5519457
  have htrace : WordTrace (prefixWord ++ tailWord_5519457) baseStart_5519457 baseEnd_5519457 := by
    simpa [prefixWord, tailWord_5519457, baseEnd_5519457] using wordTrace_append hprefix tailTrace_5519457
  have hstable : (prefixWord ++ tailWord_5519457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519457).length < 2 ^ (prefixWord ++ tailWord_5519457).sum := by decide
  have hdescent : baseEnd_5519457 < baseStart_5519457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519478 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5519478 : Nat := 118140960795 + 5519478 * 2 ^ 59
def prefixEnd_5519478 : Nat := 4983230072969 + 3 ^ 40 * 5519478 * 2
def baseEnd_5519478 : Nat := 2834145175916861250641389

theorem tailTrace_5519478 : CollatzResearch.WordTrace tailWord_5519478 prefixEnd_5519478 2834145175916861250641389 := by
  unfold tailWord_5519478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581993818617583289947943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134207934065254221759444725 12581993818617583289947943)
  ·
    refine ⟨18872990727926374934921915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12581993818617583289947943 18872990727926374934921915)
    ·
      refine ⟨28309486091889562402382873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18872990727926374934921915 28309486091889562402382873)
      ·
        refine ⟨21232114568917171801787155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28309486091889562402382873 21232114568917171801787155)
        ·
          refine ⟨31848171853375757702680733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21232114568917171801787155 31848171853375757702680733)
          ·
            refine ⟨11943064445015909138505275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31848171853375757702680733 11943064445015909138505275)
            ·
              refine ⟨17914596667523863707757913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943064445015909138505275 17914596667523863707757913)
              ·
                refine ⟨13435947500642897780818435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17914596667523863707757913 13435947500642897780818435)
                ·
                  refine ⟨20153921250964346671227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13435947500642897780818435 20153921250964346671227653)
                  ·
                    refine ⟨3778860234555815000855185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20153921250964346671227653 3778860234555815000855185)
                    ·
                      refine ⟨2834145175916861250641389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778860234555815000855185 2834145175916861250641389)
                      ·
                        rfl

theorem cell23_5519478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5519478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519478 prefixEnd_5519478 := by exact prefixLift 5519478
  have htrace : WordTrace (prefixWord ++ tailWord_5519478) baseStart_5519478 baseEnd_5519478 := by
    simpa [prefixWord, tailWord_5519478, baseEnd_5519478] using wordTrace_append hprefix tailTrace_5519478
  have hstable : (prefixWord ++ tailWord_5519478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519478).length < 2 ^ (prefixWord ++ tailWord_5519478).sum := by decide
  have hdescent : baseEnd_5519478 < baseStart_5519478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519504 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2]
def baseStart_5519504 : Nat := 118140960795 + 5519504 * 2 ^ 59
def prefixEnd_5519504 : Nat := 4983230072969 + 3 ^ 40 * 5519504 * 2
def baseEnd_5519504 : Nat := 2834158526413878148916269

theorem tailTrace_5519504 : CollatzResearch.WordTrace tailWord_5519504 prefixEnd_5519504 2834158526413878148916269 := by
  unfold tailWord_5519504
  simp only [CollatzResearch.WordTrace]
  refine ⟨100656424697893569539806783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134208566263858092719742377 100656424697893569539806783)
  ·
    refine ⟨150984637046840354309710175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100656424697893569539806783 150984637046840354309710175)
    ·
      refine ⟨226476955570260531464565263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150984637046840354309710175 226476955570260531464565263)
      ·
        refine ⟨339715433355390797196847895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226476955570260531464565263 339715433355390797196847895)
        ·
          refine ⟨509573150033086195795271843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339715433355390797196847895 509573150033086195795271843)
          ·
            refine ⟨764359725049629293692907765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509573150033086195795271843 764359725049629293692907765)
            ·
              refine ⟨71658724223402746283710103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 764359725049629293692907765 71658724223402746283710103)
              ·
                refine ⟨107488086335104119425565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71658724223402746283710103 107488086335104119425565155)
                ·
                  refine ⟨161232129502656179138347733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107488086335104119425565155 161232129502656179138347733)
                  ·
                    refine ⟨3778878035218504198555025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 161232129502656179138347733 3778878035218504198555025)
                    ·
                      refine ⟨2834158526413878148916269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3778878035218504198555025 2834158526413878148916269)
                      ·
                        rfl

theorem cell23_5519504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 7, 2].length) (baseStart_5519504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519504 prefixEnd_5519504 := by exact prefixLift 5519504
  have htrace : WordTrace (prefixWord ++ tailWord_5519504) baseStart_5519504 baseEnd_5519504 := by
    simpa [prefixWord, tailWord_5519504, baseEnd_5519504] using wordTrace_append hprefix tailTrace_5519504
  have hstable : (prefixWord ++ tailWord_5519504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519504).length < 2 ^ (prefixWord ++ tailWord_5519504).sum := by decide
  have hdescent : baseEnd_5519504 < baseStart_5519504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519508 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5519508 : Nat := 118140960795 + 5519508 * 2 ^ 59
def prefixEnd_5519508 : Nat := 4983230072969 + 3 ^ 40 * 5519508 * 2
def baseEnd_5519508 : Nat := 2834160580336496133266251

theorem tailTrace_5519508 : CollatzResearch.WordTrace tailWord_5519508 prefixEnd_5519508 2834160580336496133266251 := by
  unfold tailWord_5519508
  simp only [CollatzResearch.WordTrace]
  refine ⟨100656497643886323881379589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134208663525181765175172785 100656497643886323881379589)
  ·
    refine ⟨18873093308228685727758673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100656497643886323881379589 18873093308228685727758673)
    ·
      refine ⟨14154819981171514295819005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18873093308228685727758673 14154819981171514295819005)
      ·
        refine ⟨5308057492939317860932127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14154819981171514295819005 5308057492939317860932127)
        ·
          refine ⟨7962086239408976791398191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308057492939317860932127 7962086239408976791398191)
          ·
            refine ⟨11943129359113465187097287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7962086239408976791398191 11943129359113465187097287)
            ·
              refine ⟨17914694038670197780645931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943129359113465187097287 17914694038670197780645931)
              ·
                refine ⟨26872041058005296670968897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17914694038670197780645931 26872041058005296670968897)
                ·
                  refine ⟨20154030793503972503226673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26872041058005296670968897 20154030793503972503226673)
                  ·
                    refine ⟨15115523095127979377420005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20154030793503972503226673 15115523095127979377420005)
                    ·
                      refine ⟨2834160580336496133266251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15115523095127979377420005 2834160580336496133266251)
                      ·
                        rfl

theorem cell23_5519508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5519508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519508 prefixEnd_5519508 := by exact prefixLift 5519508
  have htrace : WordTrace (prefixWord ++ tailWord_5519508) baseStart_5519508 baseEnd_5519508 := by
    simpa [prefixWord, tailWord_5519508, baseEnd_5519508] using wordTrace_append hprefix tailTrace_5519508
  have hstable : (prefixWord ++ tailWord_5519508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519508).length < 2 ^ (prefixWord ++ tailWord_5519508).sum := by decide
  have hdescent : baseEnd_5519508 < baseStart_5519508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519511 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_5519511 : Nat := 118140960795 + 5519511 * 2 ^ 59
def prefixEnd_5519511 : Nat := 4983230072969 + 3 ^ 40 * 5519511 * 2
def baseEnd_5519511 : Nat := 2834162120778459621528737

theorem tailTrace_5519511 : CollatzResearch.WordTrace tailWord_5519511 prefixEnd_5519511 2834162120778459621528737 := by
  unfold tailWord_5519511
  simp only [CollatzResearch.WordTrace]
  refine ⟨201313104706761779275118387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134208736471174519516745591 201313104706761779275118387)
  ·
    refine ⟨301969657060142668912677581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201313104706761779275118387 301969657060142668912677581)
    ·
      refine ⟨113238621397553500842254093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301969657060142668912677581 113238621397553500842254093)
      ·
        refine ⟨42464483024082562815845285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113238621397553500842254093 42464483024082562815845285)
        ·
          refine ⟨7962090567015480527970991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42464483024082562815845285 7962090567015480527970991)
          ·
            refine ⟨11943135850523220791956487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7962090567015480527970991 11943135850523220791956487)
            ·
              refine ⟨17914703775784831187934731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943135850523220791956487 17914703775784831187934731)
              ·
                refine ⟨26872055663677246781902097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17914703775784831187934731 26872055663677246781902097)
                ·
                  refine ⟨20154041747757935086426573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26872055663677246781902097 20154041747757935086426573)
                  ·
                    refine ⟨7557765655409225657409965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20154041747757935086426573 7557765655409225657409965)
                    ·
                      refine ⟨2834162120778459621528737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557765655409225657409965 2834162120778459621528737)
                      ·
                        rfl

theorem cell23_5519511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_5519511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519511 prefixEnd_5519511 := by exact prefixLift 5519511
  have htrace : WordTrace (prefixWord ++ tailWord_5519511) baseStart_5519511 baseEnd_5519511 := by
    simpa [prefixWord, tailWord_5519511, baseEnd_5519511] using wordTrace_append hprefix tailTrace_5519511
  have hstable : (prefixWord ++ tailWord_5519511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519511).length < 2 ^ (prefixWord ++ tailWord_5519511).sum := by decide
  have hdescent : baseEnd_5519511 < baseStart_5519511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519544 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_5519544 : Nat := 118140960795 + 5519544 * 2 ^ 59
def prefixEnd_5519544 : Nat := 4983230072969 + 3 ^ 40 * 5519544 * 2
def baseEnd_5519544 : Nat := 944726355213352664138695

theorem tailTrace_5519544 : CollatzResearch.WordTrace tailWord_5519544 prefixEnd_5519544 944726355213352664138695 := by
  unfold tailWord_5519544
  simp only [CollatzResearch.WordTrace]
  refine ⟨100657154157821112955534843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134209538877094817274046457 100657154157821112955534843)
  ·
    refine ⟨150985731236731669433302265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100657154157821112955534843 150985731236731669433302265)
    ·
      refine ⟨113239298427548752074976699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150985731236731669433302265 113239298427548752074976699)
      ·
        refine ⟨169858947641323128112465049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113239298427548752074976699 169858947641323128112465049)
        ·
          refine ⟨127394210730992346084348787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169858947641323128112465049 127394210730992346084348787)
          ·
            refine ⟨191091316096488519126523181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127394210730992346084348787 191091316096488519126523181)
            ·
              refine ⟨71659243536183194672446193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191091316096488519126523181 71659243536183194672446193)
              ·
                refine ⟨53744432652137396004334645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71659243536183194672446193 53744432652137396004334645)
                ·
                  refine ⟨5038540561137880875406373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53744432652137396004334645 5038540561137880875406373)
                  ·
                    refine ⟨944726355213352664138695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038540561137880875406373 944726355213352664138695)
                    ·
                      rfl

theorem cell23_5519544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_5519544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519544 prefixEnd_5519544 := by exact prefixLift 5519544
  have htrace : WordTrace (prefixWord ++ tailWord_5519544) baseStart_5519544 baseEnd_5519544 := by
    simpa [prefixWord, tailWord_5519544, baseEnd_5519544] using wordTrace_append hprefix tailTrace_5519544
  have hstable : (prefixWord ++ tailWord_5519544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519544).length < 2 ^ (prefixWord ++ tailWord_5519544).sum := by decide
  have hdescent : baseEnd_5519544 < baseStart_5519544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519547 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_5519547 : Nat := 118140960795 + 5519547 * 2 ^ 59
def prefixEnd_5519547 : Nat := 4983230072969 + 3 ^ 40 * 5519547 * 2
def baseEnd_5519547 : Nat := 2834180606082021480678571

theorem tailTrace_5519547 : CollatzResearch.WordTrace tailWord_5519547 prefixEnd_5519547 2834180606082021480678571 := by
  unfold tailWord_5519547
  simp only [CollatzResearch.WordTrace]
  refine ⟨201314417734631357423428895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134209611823087571615619263 201314417734631357423428895)
  ·
    refine ⟨301971626601947036135143343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201314417734631357423428895 301971626601947036135143343)
    ·
      refine ⟨452957439902920554202715015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301971626601947036135143343 452957439902920554202715015)
      ·
        refine ⟨679436159854380831304072523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452957439902920554202715015 679436159854380831304072523)
        ·
          refine ⟨1019154239781571246956108785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679436159854380831304072523 1019154239781571246956108785)
          ·
            refine ⟨764365679836178435217081589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019154239781571246956108785 764365679836178435217081589)
            ·
              refine ⟨71659282484641728301601399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 764365679836178435217081589 71659282484641728301601399)
              ·
                refine ⟨107488923726962592452402099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71659282484641728301601399 107488923726962592452402099)
                ·
                  refine ⟨161233385590443888678603149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107488923726962592452402099 161233385590443888678603149)
                  ·
                    refine ⟨60462519596416458254476181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161233385590443888678603149 60462519596416458254476181)
                    ·
                      refine ⟨2834180606082021480678571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60462519596416458254476181 2834180606082021480678571)
                      ·
                        rfl

theorem cell23_5519547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_5519547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519547 prefixEnd_5519547 := by exact prefixLift 5519547
  have htrace : WordTrace (prefixWord ++ tailWord_5519547) baseStart_5519547 baseEnd_5519547 := by
    simpa [prefixWord, tailWord_5519547, baseEnd_5519547] using wordTrace_append hprefix tailTrace_5519547
  have hstable : (prefixWord ++ tailWord_5519547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519547).length < 2 ^ (prefixWord ++ tailWord_5519547).sum := by decide
  have hdescent : baseEnd_5519547 < baseStart_5519547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519584 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_5519584 : Nat := 118140960795 + 5519584 * 2 ^ 59
def prefixEnd_5519584 : Nat := 4983230072969 + 3 ^ 40 * 5519584 * 2
def baseEnd_5519584 : Nat := 2834199604866237835915901

theorem tailTrace_5519584 : CollatzResearch.WordTrace tailWord_5519584 prefixEnd_5519584 2834199604866237835915901 := by
  unfold tailWord_5519584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100657883617748656371262903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134210511490331541828350537 100657883617748656371262903)
  ·
    refine ⟨150986825426622984556894355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100657883617748656371262903 150986825426622984556894355)
    ·
      refine ⟨226480238139934476835341533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150986825426622984556894355 226480238139934476835341533)
      ·
        refine ⟨84930089302475428813253075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226480238139934476835341533 84930089302475428813253075)
        ·
          refine ⟨127395133953713143219879613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84930089302475428813253075 127395133953713143219879613)
          ·
            refine ⟨47773175232642428707454855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127395133953713143219879613 47773175232642428707454855)
            ·
              refine ⟨71659762848963643061182283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47773175232642428707454855 71659762848963643061182283)
              ·
                refine ⟨107489644273445464591773425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71659762848963643061182283 107489644273445464591773425)
                ·
                  refine ⟨80617233205084098443830069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107489644273445464591773425 80617233205084098443830069)
                  ·
                    refine ⟨7557865612976634229109069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80617233205084098443830069 7557865612976634229109069)
                    ·
                      refine ⟨2834199604866237835915901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557865612976634229109069 2834199604866237835915901)
                      ·
                        rfl

theorem cell23_5519584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_5519584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519584 prefixEnd_5519584 := by exact prefixLift 5519584
  have htrace : WordTrace (prefixWord ++ tailWord_5519584) baseStart_5519584 baseEnd_5519584 := by
    simpa [prefixWord, tailWord_5519584, baseEnd_5519584] using wordTrace_append hprefix tailTrace_5519584
  have hstable : (prefixWord ++ tailWord_5519584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519584).length < 2 ^ (prefixWord ++ tailWord_5519584).sum := by decide
  have hdescent : baseEnd_5519584 < baseStart_5519584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519601 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_5519601 : Nat := 118140960795 + 5519601 * 2 ^ 59
def prefixEnd_5519601 : Nat := 4983230072969 + 3 ^ 40 * 5519601 * 2
def baseEnd_5519601 : Nat := 2834208334037364269403323

theorem tailTrace_5519601 : CollatzResearch.WordTrace tailWord_5519601 prefixEnd_5519601 2834208334037364269403323 := by
  unfold tailWord_5519601
  simp only [CollatzResearch.WordTrace]
  refine ⟨201316387276435724645894657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134210924850957149763929771 201316387276435724645894657)
  ·
    refine ⟨150987290457326793484420993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201316387276435724645894657 150987290457326793484420993)
    ·
      refine ⟨113240467842995095113315745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150987290457326793484420993 113240467842995095113315745)
      ·
        refine ⟨84930350882246321334986809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113240467842995095113315745 84930350882246321334986809)
        ·
          refine ⟨63697763161684741001240107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84930350882246321334986809 63697763161684741001240107)
          ·
            refine ⟨95546644742527111501860161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63697763161684741001240107 95546644742527111501860161)
            ·
              refine ⟨71659983556895333626395121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95546644742527111501860161 71659983556895333626395121)
              ·
                refine ⟨53744987667671500219796341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71659983556895333626395121 53744987667671500219796341)
                ·
                  refine ⟨5038592593844203145605907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53744987667671500219796341 5038592593844203145605907)
                  ·
                    refine ⟨7557888890766304718408861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038592593844203145605907 7557888890766304718408861)
                    ·
                      refine ⟨2834208334037364269403323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557888890766304718408861 2834208334037364269403323)
                      ·
                        rfl

theorem cell23_5519601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_5519601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519601 prefixEnd_5519601 := by exact prefixLift 5519601
  have htrace : WordTrace (prefixWord ++ tailWord_5519601) baseStart_5519601 baseEnd_5519601 := by
    simpa [prefixWord, tailWord_5519601, baseEnd_5519601] using wordTrace_append hprefix tailTrace_5519601
  have hstable : (prefixWord ++ tailWord_5519601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519601).length < 2 ^ (prefixWord ++ tailWord_5519601).sum := by decide
  have hdescent : baseEnd_5519601 < baseStart_5519601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519678 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_5519678 : Nat := 118140960795 + 5519678 * 2 ^ 59
def prefixEnd_5519678 : Nat := 4983230072969 + 3 ^ 40 * 5519678 * 2
def baseEnd_5519678 : Nat := 2834247872047760468140469

theorem tailTrace_5519678 : CollatzResearch.WordTrace tailWord_5519678 prefixEnd_5519678 2834247872047760468140469 := by
  unfold tailWord_5519678
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164899462144595849555961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134212797131437844530965125 25164899462144595849555961)
  ·
    refine ⟨18873674596608446887166971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25164899462144595849555961 18873674596608446887166971)
    ·
      refine ⟨28310511894912670330750457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18873674596608446887166971 28310511894912670330750457)
      ·
        refine ⟨21232883921184502748062843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28310511894912670330750457 21232883921184502748062843)
        ·
          refine ⟨31849325881776754122094265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21232883921184502748062843 31849325881776754122094265)
          ·
            refine ⟨23886994411332565591570699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31849325881776754122094265 23886994411332565591570699)
            ·
              refine ⟨35830491616998848387356049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23886994411332565591570699 35830491616998848387356049)
              ·
                refine ⟨26872868712749136290517037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35830491616998848387356049 26872868712749136290517037)
                ·
                  refine ⟨10077325767280926108943889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26872868712749136290517037 10077325767280926108943889)
                  ·
                    refine ⟨7557994325460694581707917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10077325767280926108943889 7557994325460694581707917)
                    ·
                      refine ⟨2834247872047760468140469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7557994325460694581707917 2834247872047760468140469)
                      ·
                        rfl

theorem cell23_5519678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_5519678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519678 prefixEnd_5519678 := by exact prefixLift 5519678
  have htrace : WordTrace (prefixWord ++ tailWord_5519678) baseStart_5519678 baseEnd_5519678 := by
    simpa [prefixWord, tailWord_5519678, baseEnd_5519678] using wordTrace_append hprefix tailTrace_5519678
  have hstable : (prefixWord ++ tailWord_5519678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519678).length < 2 ^ (prefixWord ++ tailWord_5519678).sum := by decide
  have hdescent : baseEnd_5519678 < baseStart_5519678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519712 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3]
def baseStart_5519712 : Nat := 118140960795 + 5519712 * 2 ^ 59
def prefixEnd_5519712 : Nat := 4983230072969 + 3 ^ 40 * 5519712 * 2
def baseEnd_5519712 : Nat := 2834265330390013335115313

theorem tailTrace_5519712 : CollatzResearch.WordTrace tailWord_5519712 prefixEnd_5519712 2834265330390013335115313 := by
  unfold tailWord_5519712
  simp only [CollatzResearch.WordTrace]
  refine ⟨100660217889516795301592695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134213623852689060402123593 100660217889516795301592695)
  ·
    refine ⟨150990326834275192952389043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100660217889516795301592695 150990326834275192952389043)
    ·
      refine ⟨226485490251412789428583565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150990326834275192952389043 226485490251412789428583565)
      ·
        refine ⟨84932058844279796035718837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226485490251412789428583565 84932058844279796035718837)
        ·
          refine ⟨7962380516651230878348641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84932058844279796035718837 7962380516651230878348641)
          ·
            refine ⟨5971785387488423158761481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962380516651230878348641 5971785387488423158761481)
            ·
              refine ⟨4478839040616317369071111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971785387488423158761481 4478839040616317369071111)
              ·
                refine ⟨6718258560924476053606667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478839040616317369071111 6718258560924476053606667)
                ·
                  refine ⟨10077387841386714080410001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718258560924476053606667 10077387841386714080410001)
                  ·
                    refine ⟨7558040881040035560307501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10077387841386714080410001 7558040881040035560307501)
                    ·
                      refine ⟨2834265330390013335115313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558040881040035560307501 2834265330390013335115313)
                      ·
                        rfl

theorem cell23_5519712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_5519712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519712 prefixEnd_5519712 := by exact prefixLift 5519712
  have htrace : WordTrace (prefixWord ++ tailWord_5519712) baseStart_5519712 baseEnd_5519712 := by
    simpa [prefixWord, tailWord_5519712, baseEnd_5519712] using wordTrace_append hprefix tailTrace_5519712
  have hstable : (prefixWord ++ tailWord_5519712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519712).length < 2 ^ (prefixWord ++ tailWord_5519712).sum := by decide
  have hdescent : baseEnd_5519712 < baseStart_5519712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519741 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_5519741 : Nat := 118140960795 + 5519741 * 2 ^ 59
def prefixEnd_5519741 : Nat := 4983230072969 + 3 ^ 40 * 5519741 * 2
def baseEnd_5519741 : Nat := 944760073776331240550893

theorem tailTrace_5519741 : CollatzResearch.WordTrace tailWord_5519741 prefixEnd_5519741 944760073776331240550893 := by
  unfold tailWord_5519741
  simp only [CollatzResearch.WordTrace]
  refine ⟨201321493495928528555991077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134214328997285685703994051 201321493495928528555991077)
  ·
    refine ⟨37747780030486599104248327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201321493495928528555991077 37747780030486599104248327)
    ·
      refine ⟨56621670045729898656372491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37747780030486599104248327 56621670045729898656372491)
      ·
        refine ⟨84932505068594847984558737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56621670045729898656372491 84932505068594847984558737)
        ·
          refine ⟨63699378801446135988419053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84932505068594847984558737 63699378801446135988419053)
          ·
            refine ⟨23887267050542300995657145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63699378801446135988419053 23887267050542300995657145)
            ·
              refine ⟨17915450287906725746742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23887267050542300995657145 17915450287906725746742859)
              ·
                refine ⟨26873175431860088620114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17915450287906725746742859 26873175431860088620114289)
                ·
                  refine ⟨20154881573895066465085717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26873175431860088620114289 20154881573895066465085717)
                  ·
                    refine ⟨944760073776331240550893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20154881573895066465085717 944760073776331240550893)
                    ·
                      rfl

theorem cell23_5519741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_5519741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519741 prefixEnd_5519741 := by exact prefixLift 5519741
  have htrace : WordTrace (prefixWord ++ tailWord_5519741) baseStart_5519741 baseEnd_5519741 := by
    simpa [prefixWord, tailWord_5519741, baseEnd_5519741] using wordTrace_append hprefix tailTrace_5519741
  have hstable : (prefixWord ++ tailWord_5519741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519741).length < 2 ^ (prefixWord ++ tailWord_5519741).sum := by decide
  have hdescent : baseEnd_5519741 < baseStart_5519741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519751 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5519751 : Nat := 118140960795 + 5519751 * 2 ^ 59
def prefixEnd_5519751 : Nat := 4983230072969 + 3 ^ 40 * 5519751 * 2
def baseEnd_5519751 : Nat := 2834285356135538682527633

theorem tailTrace_5519751 : CollatzResearch.WordTrace tailWord_5519751 prefixEnd_5519751 2834285356135538682527633 := by
  unfold tailWord_5519751
  simp only [CollatzResearch.WordTrace]
  refine ⟨201321858225892300263855107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134214572150594866842570071 201321858225892300263855107)
  ·
    refine ⟨301982787338838450395782661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201321858225892300263855107 301982787338838450395782661)
    ·
      refine ⟨56621772626032209449209249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301982787338838450395782661 56621772626032209449209249)
      ·
        refine ⟨42466329469524157086906937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56621772626032209449209249 42466329469524157086906937)
        ·
          refine ⟨31849747102143117815180203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42466329469524157086906937 31849747102143117815180203)
          ·
            refine ⟨47774620653214676722770305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31849747102143117815180203 47774620653214676722770305)
            ·
              refine ⟨35830965489911007542077729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47774620653214676722770305 35830965489911007542077729)
              ·
                refine ⟨26873224117433255656558297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35830965489911007542077729 26873224117433255656558297)
                ·
                  refine ⟨20154918088074941742418723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26873224117433255656558297 20154918088074941742418723)
                  ·
                    refine ⟨30232377132112412613628085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20154918088074941742418723 30232377132112412613628085)
                    ·
                      refine ⟨2834285356135538682527633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30232377132112412613628085 2834285356135538682527633)
                      ·
                        rfl

theorem cell23_5519751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5519751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519751 prefixEnd_5519751 := by exact prefixLift 5519751
  have htrace : WordTrace (prefixWord ++ tailWord_5519751) baseStart_5519751 baseEnd_5519751 := by
    simpa [prefixWord, tailWord_5519751, baseEnd_5519751] using wordTrace_append hprefix tailTrace_5519751
  have hstable : (prefixWord ++ tailWord_5519751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519751).length < 2 ^ (prefixWord ++ tailWord_5519751).sum := by decide
  have hdescent : baseEnd_5519751 < baseStart_5519751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519768 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5519768 : Nat := 118140960795 + 5519768 * 2 ^ 59
def prefixEnd_5519768 : Nat := 4983230072969 + 3 ^ 40 * 5519768 * 2
def baseEnd_5519768 : Nat := 2834294085306665116015055

theorem tailTrace_5519768 : CollatzResearch.WordTrace tailWord_5519768 prefixEnd_5519768 2834294085306665116015055 := by
  unfold tailWord_5519768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100661239133415356083611979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134214985511220474778149305 100661239133415356083611979)
  ·
    refine ⟨150991858700123034125417969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100661239133415356083611979 150991858700123034125417969)
    ·
      refine ⟨113243894025092275594063477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150991858700123034125417969 113243894025092275594063477)
      ·
        refine ⟨10616615064852400836943451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113243894025092275594063477 10616615064852400836943451)
        ·
          refine ⟨15924922597278601255415177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616615064852400836943451 15924922597278601255415177)
          ·
            refine ⟨11943691947958950941561383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15924922597278601255415177 11943691947958950941561383)
            ·
              refine ⟨17915537921938426412342075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943691947958950941561383 17915537921938426412342075)
              ·
                refine ⟨26873306882907639618513113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17915537921938426412342075 26873306882907639618513113)
                ·
                  refine ⟨20154980162180729713884835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26873306882907639618513113 20154980162180729713884835)
                  ·
                    refine ⟨30232470243271094570827253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20154980162180729713884835 30232470243271094570827253)
                    ·
                      refine ⟨2834294085306665116015055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30232470243271094570827253 2834294085306665116015055)
                      ·
                        rfl

theorem cell23_5519768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5519768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519768 prefixEnd_5519768 := by exact prefixLift 5519768
  have htrace : WordTrace (prefixWord ++ tailWord_5519768) baseStart_5519768 baseEnd_5519768 := by
    simpa [prefixWord, tailWord_5519768, baseEnd_5519768] using wordTrace_append hprefix tailTrace_5519768
  have hstable : (prefixWord ++ tailWord_5519768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519768).length < 2 ^ (prefixWord ++ tailWord_5519768).sum := by decide
  have hdescent : baseEnd_5519768 < baseStart_5519768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519799 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_5519799 : Nat := 118140960795 + 5519799 * 2 ^ 59
def prefixEnd_5519799 : Nat := 4983230072969 + 3 ^ 40 * 5519799 * 2
def baseEnd_5519799 : Nat := 2834310003206954494727413

theorem tailTrace_5519799 : CollatzResearch.WordTrace tailWord_5519799 prefixEnd_5519799 2834310003206954494727413 := by
  unfold tailWord_5519799
  simp only [CollatzResearch.WordTrace]
  refine ⟨201323608929718404461602451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134215739286478936307734967 201323608929718404461602451)
  ·
    refine ⟨301985413394577606692403677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201323608929718404461602451 301985413394577606692403677)
    ·
      refine ⟨113244530022966602509651379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301985413394577606692403677 113244530022966602509651379)
      ·
        refine ⟨169866795034449903764477069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113244530022966602509651379 169866795034449903764477069)
        ·
          refine ⟨63700048137918713911678901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169866795034449903764477069 63700048137918713911678901)
          ·
            refine ⟨5971879512929879429219897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63700048137918713911678901 5971879512929879429219897)
            ·
              refine ⟨4478909634697409571914923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971879512929879429219897 4478909634697409571914923)
              ·
                refine ⟨6718364452046114357872385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478909634697409571914923 6718364452046114357872385)
                ·
                  refine ⟨5038773339034585768404289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6718364452046114357872385 5038773339034585768404289)
                  ·
                    refine ⟨3779080004275939326303217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5038773339034585768404289 3779080004275939326303217)
                    ·
                      refine ⟨2834310003206954494727413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779080004275939326303217 2834310003206954494727413)
                      ·
                        rfl

theorem cell23_5519799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_5519799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519799 prefixEnd_5519799 := by exact prefixLift 5519799
  have htrace : WordTrace (prefixWord ++ tailWord_5519799) baseStart_5519799 baseEnd_5519799 := by
    simpa [prefixWord, tailWord_5519799, baseEnd_5519799] using wordTrace_append hprefix tailTrace_5519799
  have hstable : (prefixWord ++ tailWord_5519799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519799).length < 2 ^ (prefixWord ++ tailWord_5519799).sum := by decide
  have hdescent : baseEnd_5519799 < baseStart_5519799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519818 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_5519818 : Nat := 118140960795 + 5519818 * 2 ^ 59
def prefixEnd_5519818 : Nat := 4983230072969 + 3 ^ 40 * 5519818 * 2
def baseEnd_5519818 : Nat := 944773253113129973463275

theorem tailTrace_5519818 : CollatzResearch.WordTrace tailWord_5519818 prefixEnd_5519818 944773253113129973463275 := by
  unfold tailWord_5519818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50331075479162392676636027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134216201277766380471029405 50331075479162392676636027)
  ·
    refine ⟨75496613218743589014954041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50331075479162392676636027 75496613218743589014954041)
    ·
      refine ⟨56622459914057691761215531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75496613218743589014954041 56622459914057691761215531)
      ·
        refine ⟨84933689871086537641823297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56622459914057691761215531 84933689871086537641823297)
        ·
          refine ⟨63700267403314903231367473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84933689871086537641823297 63700267403314903231367473)
          ·
            refine ⟨47775200552486177423525605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63700267403314903231367473 47775200552486177423525605)
            ·
              refine ⟨8957850103591158266911051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47775200552486177423525605 8957850103591158266911051)
              ·
                refine ⟨13436775155386737400366577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957850103591158266911051 13436775155386737400366577)
                ·
                  refine ⟨10077581366540053050274933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13436775155386737400366577 10077581366540053050274933)
                  ·
                    refine ⟨944773253113129973463275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10077581366540053050274933 944773253113129973463275)
                    ·
                      rfl

theorem cell23_5519818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_5519818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519818 prefixEnd_5519818 := by exact prefixLift 5519818
  have htrace : WordTrace (prefixWord ++ tailWord_5519818) baseStart_5519818 baseEnd_5519818 := by
    simpa [prefixWord, tailWord_5519818, baseEnd_5519818] using wordTrace_append hprefix tailTrace_5519818
  have hstable : (prefixWord ++ tailWord_5519818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519818).length < 2 ^ (prefixWord ++ tailWord_5519818).sum := by decide
  have hdescent : baseEnd_5519818 < baseStart_5519818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519828 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5519828 : Nat := 118140960795 + 5519828 * 2 ^ 59
def prefixEnd_5519828 : Nat := 4983230072969 + 3 ^ 40 * 5519828 * 2
def baseEnd_5519828 : Nat := 2834324894145934881264779

theorem tailTrace_5519828 : CollatzResearch.WordTrace tailWord_5519828 prefixEnd_5519828 2834324894145934881264779 := by
  unfold tailWord_5519828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100662333323306671207204069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134216444431075561609605425 100662333323306671207204069)
  ·
    refine ⟨18874187498120000851350763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100662333323306671207204069 18874187498120000851350763)
    ·
      refine ⟨28311281247180001277026145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18874187498120000851350763 28311281247180001277026145)
      ·
        refine ⟨21233460935385000957769609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28311281247180001277026145 21233460935385000957769609)
        ·
          refine ⟨15925095701538750718327207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21233460935385000957769609 15925095701538750718327207)
          ·
            refine ⟨23887643552308126077490811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15925095701538750718327207 23887643552308126077490811)
            ·
              refine ⟨35831465328462189116236217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23887643552308126077490811 35831465328462189116236217)
              ·
                refine ⟨26873598996346641837177163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35831465328462189116236217 26873598996346641837177163)
                ·
                  refine ⟨40310398494519962755765745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26873598996346641837177163 40310398494519962755765745)
                  ·
                    refine ⟨30232798870889972066824309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40310398494519962755765745 30232798870889972066824309)
                    ·
                      refine ⟨2834324894145934881264779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30232798870889972066824309 2834324894145934881264779)
                      ·
                        rfl

theorem cell23_5519828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5519828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519828 prefixEnd_5519828 := by exact prefixLift 5519828
  have htrace : WordTrace (prefixWord ++ tailWord_5519828) baseStart_5519828 baseEnd_5519828 := by
    simpa [prefixWord, tailWord_5519828, baseEnd_5519828] using wordTrace_append hprefix tailTrace_5519828
  have hstable : (prefixWord ++ tailWord_5519828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519828).length < 2 ^ (prefixWord ++ tailWord_5519828).sum := by decide
  have hdescent : baseEnd_5519828 < baseStart_5519828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519841 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_5519841 : Nat := 118140960795 + 5519841 * 2 ^ 59
def prefixEnd_5519841 : Nat := 4983230072969 + 3 ^ 40 * 5519841 * 2
def baseEnd_5519841 : Nat := 2834331569394443330402219

theorem tailTrace_5519841 : CollatzResearch.WordTrace tailWord_5519841 prefixEnd_5519841 2834331569394443330402219 := by
  unfold tailWord_5519841
  simp only [CollatzResearch.WordTrace]
  refine ⟨201325140795566245634631377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134216760530377497089754251 201325140795566245634631377)
  ·
    refine ⟨150993855596674684225973533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201325140795566245634631377 150993855596674684225973533)
    ·
      refine ⟨56622695848753006584740075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150993855596674684225973533 56622695848753006584740075)
      ·
        refine ⟨84934043773129509877110113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56622695848753006584740075 84934043773129509877110113)
        ·
          refine ⟨63700532829847132407832585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84934043773129509877110113 63700532829847132407832585)
          ·
            refine ⟨47775399622385349305874439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63700532829847132407832585 47775399622385349305874439)
            ·
              refine ⟨71663099433578023958811659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47775399622385349305874439 71663099433578023958811659)
              ·
                refine ⟨107494649150367035938217489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71663099433578023958811659 107494649150367035938217489)
                ·
                  refine ⟨80620986862775276953663117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107494649150367035938217489 80620986862775276953663117)
                  ·
                    refine ⟨30232870073540728857623669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80620986862775276953663117 30232870073540728857623669)
                    ·
                      refine ⟨2834331569394443330402219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30232870073540728857623669 2834331569394443330402219)
                      ·
                        rfl

theorem cell23_5519841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_5519841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519841 prefixEnd_5519841 := by exact prefixLift 5519841
  have htrace : WordTrace (prefixWord ++ tailWord_5519841) baseStart_5519841 baseEnd_5519841 := by
    simpa [prefixWord, tailWord_5519841, baseEnd_5519841] using wordTrace_append hprefix tailTrace_5519841
  have hstable : (prefixWord ++ tailWord_5519841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519841).length < 2 ^ (prefixWord ++ tailWord_5519841).sum := by decide
  have hdescent : baseEnd_5519841 < baseStart_5519841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519882 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 1, 4]
def baseStart_5519882 : Nat := 118140960795 + 5519882 * 2 ^ 59
def prefixEnd_5519882 : Nat := 4983230072969 + 3 ^ 40 * 5519882 * 2
def baseEnd_5519882 : Nat := 944784207367092556663177

theorem tailTrace_5519882 : CollatzResearch.WordTrace tailWord_5519882 prefixEnd_5519882 944784207367092556663177 := by
  unfold tailWord_5519882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50331659047104427409218475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134217757458945139757915933 50331659047104427409218475)
  ·
    refine ⟨75497488570656641113827713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50331659047104427409218475 75497488570656641113827713)
    ·
      refine ⟨56623116427992480835370785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75497488570656641113827713 56623116427992480835370785)
      ·
        refine ⟨42467337320994360626528089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56623116427992480835370785 42467337320994360626528089)
        ·
          refine ⟨31850502990745770469896067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42467337320994360626528089 31850502990745770469896067)
          ·
            refine ⟨47775754486118655704844101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31850502990745770469896067 47775754486118655704844101)
            ·
              refine ⟨8957953966147247944658269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47775754486118655704844101 8957953966147247944658269)
              ·
                refine ⟨3359232737305217979246851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8957953966147247944658269 3359232737305217979246851)
                ·
                  refine ⟨5038849105957826968870277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359232737305217979246851 5038849105957826968870277)
                  ·
                    refine ⟨944784207367092556663177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5038849105957826968870277 944784207367092556663177)
                    ·
                      rfl

theorem cell23_5519882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_5519882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519882 prefixEnd_5519882 := by exact prefixLift 5519882
  have htrace : WordTrace (prefixWord ++ tailWord_5519882) baseStart_5519882 baseEnd_5519882 := by
    simpa [prefixWord, tailWord_5519882, baseEnd_5519882] using wordTrace_append hprefix tailTrace_5519882
  have hstable : (prefixWord ++ tailWord_5519882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519882).length < 2 ^ (prefixWord ++ tailWord_5519882).sum := by decide
  have hdescent : baseEnd_5519882 < baseStart_5519882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519895 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 8]
def baseStart_5519895 : Nat := 118140960795 + 5519895 * 2 ^ 59
def prefixEnd_5519895 : Nat := 4983230072969 + 3 ^ 40 * 5519895 * 2
def baseEnd_5519895 : Nat := 314928810816642902125219

theorem tailTrace_5519895 : CollatzResearch.WordTrace tailWord_5519895 prefixEnd_5519895 314928810816642902125219 := by
  unfold tailWord_5519895
  simp only [CollatzResearch.WordTrace]
  refine ⟨201327110337370612857097139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134218073558247075238064759 201327110337370612857097139)
  ·
    refine ⟨301990665506055919285645709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201327110337370612857097139 301990665506055919285645709)
    ·
      refine ⟨113246499564770969732117141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301990665506055919285645709 113246499564770969732117141)
      ·
        refine ⟨5308429667098639206192991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113246499564770969732117141 5308429667098639206192991)
        ·
          refine ⟨7962644500647958809289487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308429667098639206192991 7962644500647958809289487)
          ·
            refine ⟨11943966750971938213934231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7962644500647958809289487 11943966750971938213934231)
            ·
              refine ⟨17915950126457907320901347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11943966750971938213934231 17915950126457907320901347)
              ·
                refine ⟨26873925189686860981352021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17915950126457907320901347 26873925189686860981352021)
                ·
                  refine ⟨314928810816642902125219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26873925189686860981352021 314928810816642902125219)
                  ·
                    rfl

theorem cell23_5519895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 8].length) (baseStart_5519895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519895 prefixEnd_5519895 := by exact prefixLift 5519895
  have htrace : WordTrace (prefixWord ++ tailWord_5519895) baseStart_5519895 baseEnd_5519895 := by
    simpa [prefixWord, tailWord_5519895, baseEnd_5519895] using wordTrace_append hprefix tailTrace_5519895
  have hstable : (prefixWord ++ tailWord_5519895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519895).length < 2 ^ (prefixWord ++ tailWord_5519895).sum := by decide
  have hdescent : baseEnd_5519895 < baseStart_5519895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519912 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 6]
def baseStart_5519912 : Nat := 118140960795 + 5519912 * 2 ^ 59
def prefixEnd_5519912 : Nat := 4983230072969 + 3 ^ 40 * 5519912 * 2
def baseEnd_5519912 : Nat := 314929780724545839179377

theorem tailTrace_5519912 : CollatzResearch.WordTrace tailWord_5519912 prefixEnd_5519912 314929780724545839179377 := by
  unfold tailWord_5519912
  simp only [CollatzResearch.WordTrace]
  refine ⟨100663865189154512380232995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134218486918872683173643993 100663865189154512380232995)
  ·
    refine ⟨150995797783731768570349493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100663865189154512380232995 150995797783731768570349493)
    ·
      refine ⟨14155856042224853303470265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150995797783731768570349493 14155856042224853303470265)
      ·
        refine ⟨10616892031668639977602699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14155856042224853303470265 10616892031668639977602699)
        ·
          refine ⟨15925338047502959966404049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616892031668639977602699 15925338047502959966404049)
          ·
            refine ⟨11944003535627219974803037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15925338047502959966404049 11944003535627219974803037)
            ·
              refine ⟨4479001325860207490551139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944003535627219974803037 4479001325860207490551139)
              ·
                refine ⟨6718501988790311235826709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479001325860207490551139 6718501988790311235826709)
                ·
                  refine ⟨314929780724545839179377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6718501988790311235826709 314929780724545839179377)
                  ·
                    rfl

theorem cell23_5519912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 6].length) (baseStart_5519912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519912 prefixEnd_5519912 := by exact prefixLift 5519912
  have htrace : WordTrace (prefixWord ++ tailWord_5519912) baseStart_5519912 baseEnd_5519912 := by
    simpa [prefixWord, tailWord_5519912, baseEnd_5519912] using wordTrace_append hprefix tailTrace_5519912
  have hstable : (prefixWord ++ tailWord_5519912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519912).length < 2 ^ (prefixWord ++ tailWord_5519912).sum := by decide
  have hdescent : baseEnd_5519912 < baseStart_5519912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519925 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_5519925 : Nat := 118140960795 + 5519925 * 2 ^ 59
def prefixEnd_5519925 : Nat := 4983230072969 + 3 ^ 40 * 5519925 * 2
def baseEnd_5519925 : Nat := 944791567256473667250611

theorem tailTrace_5519925 : CollatzResearch.WordTrace tailWord_5519925 prefixEnd_5519925 944791567256473667250611 := by
  unfold tailWord_5519925
  simp only [CollatzResearch.WordTrace]
  refine ⟨201328204527261927980689229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134218803018174618653792819 201328204527261927980689229)
  ·
    refine ⟨75498076697723222992758461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201328204527261927980689229 75498076697723222992758461)
    ·
      refine ⟨28311778761646208622284423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75498076697723222992758461 28311778761646208622284423)
      ·
        refine ⟨42467668142469312933426635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28311778761646208622284423 42467668142469312933426635)
        ·
          refine ⟨63701502213703969400139953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42467668142469312933426635 63701502213703969400139953)
          ·
            refine ⟨47776126660277977050104965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63701502213703969400139953 47776126660277977050104965)
            ·
              refine ⟨8958023748802120696894681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47776126660277977050104965 8958023748802120696894681)
              ·
                refine ⟨6718517811601590522671011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8958023748802120696894681 6718517811601590522671011)
                ·
                  refine ⟨10077776717402385784006517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718517811601590522671011 10077776717402385784006517)
                  ·
                    refine ⟨944791567256473667250611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10077776717402385784006517 944791567256473667250611)
                    ·
                      rfl

theorem cell23_5519925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_5519925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519925 prefixEnd_5519925 := by exact prefixLift 5519925
  have htrace : WordTrace (prefixWord ++ tailWord_5519925) baseStart_5519925 baseEnd_5519925 := by
    simpa [prefixWord, tailWord_5519925, baseEnd_5519925] using wordTrace_append hprefix tailTrace_5519925
  have hstable : (prefixWord ++ tailWord_5519925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519925).length < 2 ^ (prefixWord ++ tailWord_5519925).sum := by decide
  have hdescent : baseEnd_5519925 < baseStart_5519925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519949 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5519949 : Nat := 118140960795 + 5519949 * 2 ^ 59
def prefixEnd_5519949 : Nat := 4983230072969 + 3 ^ 40 * 5519949 * 2
def baseEnd_5519949 : Nat := 2834387025305128907851723

theorem tailTrace_5519949 : CollatzResearch.WordTrace tailWord_5519949 prefixEnd_5519949 2834387025305128907851723 := by
  unfold tailWord_5519949
  simp only [CollatzResearch.WordTrace]
  refine ⟨201329079879174980079562901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134219386586116653386375267 201329079879174980079562901)
  ·
    refine ⟨9437300619336327191229511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 201329079879174980079562901 9437300619336327191229511)
    ·
      refine ⟨14155950929004490786844267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437300619336327191229511 14155950929004490786844267)
      ·
        refine ⟨21233926393506736180266401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155950929004490786844267 21233926393506736180266401)
        ·
          refine ⟨15925444795130052135199801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21233926393506736180266401 15925444795130052135199801)
          ·
            refine ⟨11944083596347539101399851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15925444795130052135199801 11944083596347539101399851)
            ·
              refine ⟨17916125394521308652099777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11944083596347539101399851 17916125394521308652099777)
              ·
                refine ⟨13437094045890981489074833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17916125394521308652099777 13437094045890981489074833)
                ·
                  refine ⟨10077820534418236116806125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13437094045890981489074833 10077820534418236116806125)
                  ·
                    refine ⟨3779182700406838543802297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10077820534418236116806125 3779182700406838543802297)
                    ·
                      refine ⟨2834387025305128907851723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779182700406838543802297 2834387025305128907851723)
                      ·
                        rfl

theorem cell23_5519949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5519949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519949 prefixEnd_5519949 := by exact prefixLift 5519949
  have htrace : WordTrace (prefixWord ++ tailWord_5519949) baseStart_5519949 baseEnd_5519949 := by
    simpa [prefixWord, tailWord_5519949, baseEnd_5519949] using wordTrace_append hprefix tailTrace_5519949
  have hstable : (prefixWord ++ tailWord_5519949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519949).length < 2 ^ (prefixWord ++ tailWord_5519949).sum := by decide
  have hdescent : baseEnd_5519949 < baseStart_5519949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519951 : List Nat := [1, 1, 2, 1, 1, 2, 15]
def baseStart_5519951 : Nat := 118140960795 + 5519951 * 2 ^ 59
def prefixEnd_5519951 : Nat := 4983230072969 + 3 ^ 40 * 5519951 * 2
def baseEnd_5519951 : Nat := 34992445089709109876873

theorem tailTrace_5519951 : CollatzResearch.WordTrace tailWord_5519951 prefixEnd_5519951 34992445089709109876873 := by
  unfold tailWord_5519951
  simp only [CollatzResearch.WordTrace]
  refine ⟨201329152825167734421135707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134219435216778489614090471 201329152825167734421135707)
  ·
    refine ⟨301993729237751601631703561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201329152825167734421135707 301993729237751601631703561)
    ·
      refine ⟨226495296928313701223777671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 301993729237751601631703561 226495296928313701223777671)
      ·
        refine ⟨339742945392470551835666507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226495296928313701223777671 339742945392470551835666507)
        ·
          refine ⟨509614418088705827753499761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339742945392470551835666507 509614418088705827753499761)
          ·
            refine ⟨382210813566529370815124821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509614418088705827753499761 382210813566529370815124821)
            ·
              refine ⟨34992445089709109876873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 382210813566529370815124821 34992445089709109876873)
              ·
                rfl

theorem cell23_5519951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 15].length) (baseStart_5519951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519951 prefixEnd_5519951 := by exact prefixLift 5519951
  have htrace : WordTrace (prefixWord ++ tailWord_5519951) baseStart_5519951 baseEnd_5519951 := by
    simpa [prefixWord, tailWord_5519951, baseEnd_5519951] using wordTrace_append hprefix tailTrace_5519951
  have hstable : (prefixWord ++ tailWord_5519951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519951).length < 2 ^ (prefixWord ++ tailWord_5519951).sum := by decide
  have hdescent : baseEnd_5519951 < baseStart_5519951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519956 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_5519956 : Nat := 118140960795 + 5519956 * 2 ^ 59
def prefixEnd_5519956 : Nat := 4983230072969 + 3 ^ 40 * 5519956 * 2
def baseEnd_5519956 : Nat := 2834390619669710380464191

theorem tailTrace_5519956 : CollatzResearch.WordTrace tailWord_5519956 prefixEnd_5519956 2834390619669710380464191 := by
  unfold tailWord_5519956
  simp only [CollatzResearch.WordTrace]
  refine ⟨100664667595074810137533861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134219556793433080183378481 100664667595074810137533861)
  ·
    refine ⟨18874625174076526900787599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100664667595074810137533861 18874625174076526900787599)
    ·
      refine ⟨28311937761114790351181399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18874625174076526900787599 28311937761114790351181399)
      ·
        refine ⟨42467906641672185526772099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28311937761114790351181399 42467906641672185526772099)
        ·
          refine ⟨63701859962508278290158149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42467906641672185526772099 63701859962508278290158149)
          ·
            refine ⟨11944098742970302179404653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63701859962508278290158149 11944098742970302179404653)
            ·
              refine ⟨4479037028613863317276745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944098742970302179404653 4479037028613863317276745)
              ·
                refine ⟨3359277771460397487957559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479037028613863317276745 3359277771460397487957559)
                ·
                  refine ⟨5038916657190596231936339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359277771460397487957559 5038916657190596231936339)
                  ·
                    refine ⟨7558374985785894347904509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038916657190596231936339 7558374985785894347904509)
                    ·
                      refine ⟨2834390619669710380464191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558374985785894347904509 2834390619669710380464191)
                      ·
                        rfl

theorem cell23_5519956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_5519956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519956 prefixEnd_5519956 := by exact prefixLift 5519956
  have htrace : WordTrace (prefixWord ++ tailWord_5519956) baseStart_5519956 baseEnd_5519956 := by
    simpa [prefixWord, tailWord_5519956, baseEnd_5519956] using wordTrace_append hprefix tailTrace_5519956
  have hstable : (prefixWord ++ tailWord_5519956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519956).length < 2 ^ (prefixWord ++ tailWord_5519956).sum := by decide
  have hdescent : baseEnd_5519956 < baseStart_5519956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519982 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5519982 : Nat := 118140960795 + 5519982 * 2 ^ 59
def prefixEnd_5519982 : Nat := 4983230072969 + 3 ^ 40 * 5519982 * 2
def baseEnd_5519982 : Nat := 2834403970166727278739071

theorem tailTrace_5519982 : CollatzResearch.WordTrace tailWord_5519982 prefixEnd_5519982 2834403970166727278739071 := by
  unfold tailWord_5519982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166285436006928339439275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134220188992036951143676133 25166285436006928339439275)
  ·
    refine ⟨37749428154010392509158913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25166285436006928339439275 37749428154010392509158913)
    ·
      refine ⟨28312071115507794381869185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37749428154010392509158913 28312071115507794381869185)
      ·
        refine ⟨21234053336630845786401889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28312071115507794381869185 21234053336630845786401889)
        ·
          refine ⟨15925540002473134339801417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21234053336630845786401889 15925540002473134339801417)
          ·
            refine ⟨11944155001854850754851063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15925540002473134339801417 11944155001854850754851063)
            ·
              refine ⟨17916232502782276132276595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11944155001854850754851063 17916232502782276132276595)
              ·
                refine ⟨26874348754173414198414893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17916232502782276132276595 26874348754173414198414893)
                ·
                  refine ⟨10077880782815030324405585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26874348754173414198414893 10077880782815030324405585)
                  ·
                    refine ⟨7558410587111272743304189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10077880782815030324405585 7558410587111272743304189)
                    ·
                      refine ⟨2834403970166727278739071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558410587111272743304189 2834403970166727278739071)
                      ·
                        rfl

theorem cell23_5519982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5519982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519982 prefixEnd_5519982 := by exact prefixLift 5519982
  have htrace : WordTrace (prefixWord ++ tailWord_5519982) baseStart_5519982 baseEnd_5519982 := by
    simpa [prefixWord, tailWord_5519982, baseEnd_5519982] using wordTrace_append hprefix tailTrace_5519982
  have hstable : (prefixWord ++ tailWord_5519982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519982).length < 2 ^ (prefixWord ++ tailWord_5519982).sum := by decide
  have hdescent : baseEnd_5519982 < baseStart_5519982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5519995 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 3]
def baseStart_5519995 : Nat := 118140960795 + 5519995 * 2 ^ 59
def prefixEnd_5519995 : Nat := 4983230072969 + 3 ^ 40 * 5519995 * 2
def baseEnd_5519995 : Nat := 2834410645415235727876511

theorem tailTrace_5519995 : CollatzResearch.WordTrace tailWord_5519995 prefixEnd_5519995 2834410645415235727876511 := by
  unfold tailWord_5519995
  simp only [CollatzResearch.WordTrace]
  refine ⟨201330757637008329935737439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134220505091338886623824959 201330757637008329935737439)
  ·
    refine ⟨301996136455512494903606159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201330757637008329935737439 301996136455512494903606159)
    ·
      refine ⟨452994204683268742355409239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301996136455512494903606159 452994204683268742355409239)
      ·
        refine ⟨679491307024903113533113859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 452994204683268742355409239 679491307024903113533113859)
        ·
          refine ⟨1019236960537354670299670789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679491307024903113533113859 1019236960537354670299670789)
          ·
            refine ⟨191106930100754000681188273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1019236960537354670299670789 191106930100754000681188273)
            ·
              refine ⟨143330197575565500510891205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191106930100754000681188273 143330197575565500510891205)
              ·
                refine ⟨26874412045418531345792101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143330197575565500510891205 26874412045418531345792101)
                ·
                  refine ⟨5038952258515974627336019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26874412045418531345792101 5038952258515974627336019)
                  ·
                    refine ⟨7558428387773961941004029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5038952258515974627336019 7558428387773961941004029)
                    ·
                      refine ⟨2834410645415235727876511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558428387773961941004029 2834410645415235727876511)
                      ·
                        rfl

theorem cell23_5519995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 3].length) (baseStart_5519995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5519995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5519995 prefixEnd_5519995 := by exact prefixLift 5519995
  have htrace : WordTrace (prefixWord ++ tailWord_5519995) baseStart_5519995 baseEnd_5519995 := by
    simpa [prefixWord, tailWord_5519995, baseEnd_5519995] using wordTrace_append hprefix tailTrace_5519995
  have hstable : (prefixWord ++ tailWord_5519995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5519995).length < 2 ^ (prefixWord ++ tailWord_5519995).sum := by decide
  have hdescent : baseEnd_5519995 < baseStart_5519995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5519995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520002 : List Nat := [3, 4, 3, 1, 12]
def baseStart_5520002 : Nat := 118140960795 + 5520002 * 2 ^ 59
def prefixEnd_5520002 : Nat := 4983230072969 + 3 ^ 40 * 5520002 * 2
def baseEnd_5520002 : Nat := 3888085376927046914251

theorem tailTrace_5520002 : CollatzResearch.WordTrace tailWord_5520002 prefixEnd_5520002 3888085376927046914251 := by
  unfold tailWord_5520002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50332753236995742532810565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134220675298655313420828173 50332753236995742532810565)
  ·
    refine ⟨9437391231936701724901981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50332753236995742532810565 9437391231936701724901981)
    ·
      refine ⟨3539021711976263146838243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9437391231936701724901981 3539021711976263146838243)
      ·
        refine ⟨5308532567964394720257365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539021711976263146838243 5308532567964394720257365)
        ·
          refine ⟨3888085376927046914251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5308532567964394720257365 3888085376927046914251)
          ·
            rfl

theorem cell23_5520002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 12].length) (baseStart_5520002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520002 prefixEnd_5520002 := by exact prefixLift 5520002
  have htrace : WordTrace (prefixWord ++ tailWord_5520002) baseStart_5520002 baseEnd_5520002 := by
    simpa [prefixWord, tailWord_5520002, baseEnd_5520002] using wordTrace_append hprefix tailTrace_5520002
  have hstable : (prefixWord ++ tailWord_5520002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520002).length < 2 ^ (prefixWord ++ tailWord_5520002).sum := by decide
  have hdescent : baseEnd_5520002 < baseStart_5520002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520048 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_5520048 : Nat := 118140960795 + 5520048 * 2 ^ 59
def prefixEnd_5520048 : Nat := 4983230072969 + 3 ^ 40 * 5520048 * 2
def baseEnd_5520048 : Nat := 2834437859889924020513767

theorem tailTrace_5520048 : CollatzResearch.WordTrace tailWord_5520048 prefixEnd_5520048 2834437859889924020513767 := by
  unfold tailWord_5520048
  simp only [CollatzResearch.WordTrace]
  refine ⟨100666345352908159993708399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134221793803877546658277865 100666345352908159993708399)
  ·
    refine ⟨150999518029362239990562599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100666345352908159993708399 150999518029362239990562599)
    ·
      refine ⟨226499277044043359985843899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150999518029362239990562599 226499277044043359985843899)
      ·
        refine ⟨339748915566065039978765849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226499277044043359985843899 339748915566065039978765849)
        ·
          refine ⟨254811686674548779984074387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339748915566065039978765849 254811686674548779984074387)
          ·
            refine ⟨382217530011823169976111581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254811686674548779984074387 382217530011823169976111581)
            ·
              refine ⟨143331573754433688741041843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382217530011823169976111581 143331573754433688741041843)
              ·
                refine ⟨214997360631650533111562765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143331573754433688741041843 214997360631650533111562765)
                ·
                  refine ⟨80624010236868949916836037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214997360631650533111562765 80624010236868949916836037)
                  ·
                    refine ⟨15117001919412928109406757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80624010236868949916836037 15117001919412928109406757)
                    ·
                      refine ⟨2834437859889924020513767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15117001919412928109406757 2834437859889924020513767)
                      ·
                        rfl

theorem cell23_5520048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_5520048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520048 prefixEnd_5520048 := by exact prefixLift 5520048
  have htrace : WordTrace (prefixWord ++ tailWord_5520048) baseStart_5520048 baseEnd_5520048 := by
    simpa [prefixWord, tailWord_5520048, baseEnd_5520048] using wordTrace_append hprefix tailTrace_5520048
  have hstable : (prefixWord ++ tailWord_5520048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520048).length < 2 ^ (prefixWord ++ tailWord_5520048).sum := by decide
  have hdescent : baseEnd_5520048 < baseStart_5520048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520058 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_5520058 : Nat := 118140960795 + 5520058 * 2 ^ 59
def prefixEnd_5520058 : Nat := 4983230072969 + 3 ^ 40 * 5520058 * 2
def baseEnd_5520058 : Nat := 314938110521829886820969

theorem tailTrace_5520058 : CollatzResearch.WordTrace tailWord_5520058 prefixEnd_5520058 314938110521829886820969 := by
  unfold tailWord_5520058
  simp only [CollatzResearch.WordTrace]
  refine ⟨50333263858945022923820207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134222036957186727796853885 50333263858945022923820207)
  ·
    refine ⟨75499895788417534385730311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50333263858945022923820207 75499895788417534385730311)
    ·
      refine ⟨113249843682626301578595467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75499895788417534385730311 113249843682626301578595467)
      ·
        refine ⟨169874765523939452367893201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113249843682626301578595467 169874765523939452367893201)
        ·
          refine ⟨127406074142954589275919901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169874765523939452367893201 127406074142954589275919901)
          ·
            refine ⟨47777277803607970978469963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127406074142954589275919901 47777277803607970978469963)
            ·
              refine ⟨71665916705411956467704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47777277803607970978469963 71665916705411956467704945)
              ·
                refine ⟨53749437529058967350778709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71665916705411956467704945 53749437529058967350778709)
                ·
                  refine ⟨314938110521829886820969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53749437529058967350778709 314938110521829886820969)
                  ·
                    rfl

theorem cell23_5520058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_5520058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520058 prefixEnd_5520058 := by exact prefixLift 5520058
  have htrace : WordTrace (prefixWord ++ tailWord_5520058) baseStart_5520058 baseEnd_5520058 := by
    simpa [prefixWord, tailWord_5520058, baseEnd_5520058] using wordTrace_append hprefix tailTrace_5520058
  have hstable : (prefixWord ++ tailWord_5520058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520058).length < 2 ^ (prefixWord ++ tailWord_5520058).sum := by decide
  have hdescent : baseEnd_5520058 < baseStart_5520058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520092 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 7]
def baseStart_5520092 : Nat := 118140960795 + 5520092 * 2 ^ 59
def prefixEnd_5520092 : Nat := 4983230072969 + 3 ^ 40 * 5520092 * 2
def baseEnd_5520092 : Nat := 314940050337635760929285

theorem tailTrace_5520092 : CollatzResearch.WordTrace tailWord_5520092 prefixEnd_5520092 314940050337635760929285 := by
  unfold tailWord_5520092
  simp only [CollatzResearch.WordTrace]
  refine ⟨100667147758828457751009265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134222863678437943668012353 100667147758828457751009265)
  ·
    refine ⟨75500360819121343313256949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100667147758828457751009265 75500360819121343313256949)
    ·
      refine ⟨7078158826792625935617839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75500360819121343313256949 7078158826792625935617839)
      ·
        refine ⟨10617238240188938903426759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7078158826792625935617839 10617238240188938903426759)
        ·
          refine ⟨15925857360283408355140139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617238240188938903426759 15925857360283408355140139)
          ·
            refine ⟨23888786040425112532710209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15925857360283408355140139 23888786040425112532710209)
            ·
              refine ⟨17916589530318834399532657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23888786040425112532710209 17916589530318834399532657)
              ·
                refine ⟨13437442147739125799649493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17916589530318834399532657 13437442147739125799649493)
                ·
                  refine ⟨314940050337635760929285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13437442147739125799649493 314940050337635760929285)
                  ·
                    rfl

theorem cell23_5520092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_5520092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520092 prefixEnd_5520092 := by exact prefixLift 5520092
  have htrace : WordTrace (prefixWord ++ tailWord_5520092) baseStart_5520092 baseEnd_5520092 := by
    simpa [prefixWord, tailWord_5520092, baseEnd_5520092] using wordTrace_append hprefix tailTrace_5520092
  have hstable : (prefixWord ++ tailWord_5520092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520092).length < 2 ^ (prefixWord ++ tailWord_5520092).sum := by decide
  have hdescent : baseEnd_5520092 < baseStart_5520092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520126 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_5520126 : Nat := 118140960795 + 5520126 * 2 ^ 59
def prefixEnd_5520126 : Nat := 4983230072969 + 3 ^ 40 * 5520126 * 2
def baseEnd_5520126 : Nat := 314941990153441635037601

theorem tailTrace_5520126 : CollatzResearch.WordTrace tailWord_5520126 prefixEnd_5520126 314941990153441635037601 := by
  unfold tailWord_5520126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25166941949941717413594529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134223690399689159539170821 25166941949941717413594529)
  ·
    refine ⟨18875206462456288060195897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25166941949941717413594529 18875206462456288060195897)
    ·
      refine ⟨14156404846842216045146923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18875206462456288060195897 14156404846842216045146923)
      ·
        refine ⟨21234607270263324067720385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14156404846842216045146923 21234607270263324067720385)
        ·
          refine ⟨15925955452697493050790289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21234607270263324067720385 15925955452697493050790289)
          ·
            refine ⟨11944466589523119788092717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15925955452697493050790289 11944466589523119788092717)
            ·
              refine ⟨4479174971071169920534769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11944466589523119788092717 4479174971071169920534769)
              ·
                refine ⟨3359381228303377440401077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479174971071169920534769 3359381228303377440401077)
                ·
                  refine ⟨314941990153441635037601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359381228303377440401077 314941990153441635037601)
                  ·
                    rfl

theorem cell23_5520126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_5520126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520126 prefixEnd_5520126 := by exact prefixLift 5520126
  have htrace : WordTrace (prefixWord ++ tailWord_5520126) baseStart_5520126 baseEnd_5520126 := by
    simpa [prefixWord, tailWord_5520126, baseEnd_5520126] using wordTrace_append hprefix tailTrace_5520126
  have hstable : (prefixWord ++ tailWord_5520126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520126).length < 2 ^ (prefixWord ++ tailWord_5520126).sum := by decide
  have hdescent : baseEnd_5520126 < baseStart_5520126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520142 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5520142 : Nat := 118140960795 + 5520142 * 2 ^ 59
def prefixEnd_5520142 : Nat := 4983230072969 + 3 ^ 40 * 5520142 * 2
def baseEnd_5520142 : Nat := 2834486127071446652738335

theorem tailTrace_5520142 : CollatzResearch.WordTrace tailWord_5520142 prefixEnd_5520142 2834486127071446652738335 := by
  unfold tailWord_5520142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167014895934471755167335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134224079444983849360892453 25167014895934471755167335)
  ·
    refine ⟨37750522343901707632751003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25167014895934471755167335 37750522343901707632751003)
    ·
      refine ⟨56625783515852561449126505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37750522343901707632751003 56625783515852561449126505)
      ·
        refine ⟨42469337636889421086844879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56625783515852561449126505 42469337636889421086844879)
        ·
          refine ⟨63704006455334131630267319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42469337636889421086844879 63704006455334131630267319)
          ·
            refine ⟨95556009683001197445400979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63704006455334131630267319 95556009683001197445400979)
            ·
              refine ⟨143334014524501796168101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95556009683001197445400979 143334014524501796168101469)
              ·
                refine ⟨53750255446688173563038051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143334014524501796168101469 53750255446688173563038051)
                ·
                  refine ⟨80625383170032260344557077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53750255446688173563038051 80625383170032260344557077)
                  ·
                    refine ⟨3779314836095262203651113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80625383170032260344557077 3779314836095262203651113)
                    ·
                      refine ⟨2834486127071446652738335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779314836095262203651113 2834486127071446652738335)
                      ·
                        rfl

theorem cell23_5520142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5520142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520142 prefixEnd_5520142 := by exact prefixLift 5520142
  have htrace : WordTrace (prefixWord ++ tailWord_5520142) baseStart_5520142 baseEnd_5520142 := by
    simpa [prefixWord, tailWord_5520142, baseEnd_5520142] using wordTrace_append hprefix tailTrace_5520142
  have hstable : (prefixWord ++ tailWord_5520142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520142).length < 2 ^ (prefixWord ++ tailWord_5520142).sum := by decide
  have hdescent : baseEnd_5520142 < baseStart_5520142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520145 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_5520145 : Nat := 118140960795 + 5520145 * 2 ^ 59
def prefixEnd_5520145 : Nat := 4983230072969 + 3 ^ 40 * 5520145 * 2
def baseEnd_5520145 : Nat := 2834487667513410141000821

theorem tailTrace_5520145 : CollatzResearch.WordTrace tailWord_5520145 prefixEnd_5520145 2834487667513410141000821 := by
  unfold tailWord_5520145
  simp only [CollatzResearch.WordTrace]
  refine ⟨201336228586464905553697889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134224152390976603702465259 201336228586464905553697889)
  ·
    refine ⟨151002171439848679165273417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201336228586464905553697889 151002171439848679165273417)
    ·
      refine ⟨113251628579886509373955063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151002171439848679165273417 113251628579886509373955063)
      ·
        refine ⟨169877442869829764060932595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113251628579886509373955063 169877442869829764060932595)
        ·
          refine ⟨254816164304744646091398893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169877442869829764060932595 254816164304744646091398893)
          ·
            refine ⟨95556061614279242284274585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254816164304744646091398893 95556061614279242284274585)
            ·
              refine ⟨71667046210709431713205939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95556061614279242284274585 71667046210709431713205939)
              ·
                refine ⟨107500569316064147569808909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71667046210709431713205939 107500569316064147569808909)
                ·
                  refine ⟨40312713493524055338678341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107500569316064147569808909 40312713493524055338678341)
                  ·
                    refine ⟨7558633780035760376002189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40312713493524055338678341 7558633780035760376002189)
                    ·
                      refine ⟨2834487667513410141000821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558633780035760376002189 2834487667513410141000821)
                      ·
                        rfl

theorem cell23_5520145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_5520145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520145 prefixEnd_5520145 := by exact prefixLift 5520145
  have htrace : WordTrace (prefixWord ++ tailWord_5520145) baseStart_5520145 baseEnd_5520145 := by
    simpa [prefixWord, tailWord_5520145, baseEnd_5520145] using wordTrace_append hprefix tailTrace_5520145
  have hstable : (prefixWord ++ tailWord_5520145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520145).length < 2 ^ (prefixWord ++ tailWord_5520145).sum := by decide
  have hdescent : baseEnd_5520145 < baseStart_5520145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520186 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_5520186 : Nat := 118140960795 + 5520186 * 2 ^ 59
def prefixEnd_5520186 : Nat := 4983230072969 + 3 ^ 40 * 5520186 * 2
def baseEnd_5520186 : Nat := 944836240073414826862711

theorem tailTrace_5520186 : CollatzResearch.WordTrace tailWord_5520186 prefixEnd_5520186 944836240073414826862711 := by
  unfold tailWord_5520186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50334430994829092388985103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134225149319544246370626941 50334430994829092388985103)
  ·
    refine ⟨75501646492243638583477655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50334430994829092388985103 75501646492243638583477655)
    ·
      refine ⟨113252469738365457875216483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75501646492243638583477655 113252469738365457875216483)
      ·
        refine ⟨169878704607548186812824725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113252469738365457875216483 169878704607548186812824725)
        ·
          refine ⟨7963064278478821256851159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169878704607548186812824725 7963064278478821256851159)
          ·
            refine ⟨11944596417718231885276739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7963064278478821256851159 11944596417718231885276739)
            ·
              refine ⟨17916894626577347827915109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11944596417718231885276739 17916894626577347827915109)
              ·
                refine ⟨3359417742483252717734083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17916894626577347827915109 3359417742483252717734083)
                ·
                  refine ⟨5039126613724879076601125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359417742483252717734083 5039126613724879076601125)
                  ·
                    refine ⟨944836240073414826862711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039126613724879076601125 944836240073414826862711)
                    ·
                      rfl

theorem cell23_5520186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_5520186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520186 prefixEnd_5520186 := by exact prefixLift 5520186
  have htrace : WordTrace (prefixWord ++ tailWord_5520186) baseStart_5520186 baseEnd_5520186 := by
    simpa [prefixWord, tailWord_5520186, baseEnd_5520186] using wordTrace_append hprefix tailTrace_5520186
  have hstable : (prefixWord ++ tailWord_5520186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520186).length < 2 ^ (prefixWord ++ tailWord_5520186).sum := by decide
  have hdescent : baseEnd_5520186 < baseStart_5520186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520192 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_5520192 : Nat := 118140960795 + 5520192 * 2 ^ 59
def prefixEnd_5520192 : Nat := 4983230072969 + 3 ^ 40 * 5520192 * 2
def baseEnd_5520192 : Nat := 2834511801104171457113105

theorem tailTrace_5520192 : CollatzResearch.WordTrace tailWord_5520192 prefixEnd_5520192 2834511801104171457113105 := by
  unfold tailWord_5520192
  simp only [CollatzResearch.WordTrace]
  refine ⟨100668971408647316290329415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134225295211529755053772553 100668971408647316290329415)
  ·
    refine ⟨151003457112970974435494123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100668971408647316290329415 151003457112970974435494123)
    ·
      refine ⟨226505185669456461653241185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151003457112970974435494123 226505185669456461653241185)
      ·
        refine ⟨169878889252092346239930889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226505185669456461653241185 169878889252092346239930889)
        ·
          refine ⟨127409166939069259679948167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169878889252092346239930889 127409166939069259679948167)
          ·
            refine ⟨191113750408603889519922251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127409166939069259679948167 191113750408603889519922251)
            ·
              refine ⟨286670625612905834279883377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191113750408603889519922251 286670625612905834279883377)
              ·
                refine ⟨215002969209679375709912533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286670625612905834279883377 215002969209679375709912533)
                ·
                  refine ⟨5039132090851860368201075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215002969209679375709912533 5039132090851860368201075)
                  ·
                    refine ⟨7558698136277790552301613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5039132090851860368201075 7558698136277790552301613)
                    ·
                      refine ⟨2834511801104171457113105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558698136277790552301613 2834511801104171457113105)
                      ·
                        rfl

theorem cell23_5520192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_5520192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520192 prefixEnd_5520192 := by exact prefixLift 5520192
  have htrace : WordTrace (prefixWord ++ tailWord_5520192) baseStart_5520192 baseEnd_5520192 := by
    simpa [prefixWord, tailWord_5520192, baseEnd_5520192] using wordTrace_append hprefix tailTrace_5520192
  have hstable : (prefixWord ++ tailWord_5520192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520192).length < 2 ^ (prefixWord ++ tailWord_5520192).sum := by decide
  have hdescent : baseEnd_5520192 < baseStart_5520192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520195 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 5, 5]
def baseStart_5520195 : Nat := 118140960795 + 5520195 * 2 ^ 59
def prefixEnd_5520195 : Nat := 4983230072969 + 3 ^ 40 * 5520195 * 2
def baseEnd_5520195 : Nat := 944837780515378315125197

theorem tailTrace_5520195 : CollatzResearch.WordTrace tailWord_5520195 prefixEnd_5520195 944837780515378315125197 := by
  unfold tailWord_5520195
  simp only [CollatzResearch.WordTrace]
  refine ⟨201338052236283764093018039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134225368157522509395345359 201338052236283764093018039)
  ·
    refine ⟨302007078354425646139527059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201338052236283764093018039 302007078354425646139527059)
    ·
      refine ⟨453010617531638469209290589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302007078354425646139527059 453010617531638469209290589)
      ·
        refine ⟨169878981574364425953483971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453010617531638469209290589 169878981574364425953483971)
        ·
          refine ⟨254818472361546638930225957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169878981574364425953483971 254818472361546638930225957)
          ·
            refine ⟨47778463567789994799417367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254818472361546638930225957 47778463567789994799417367)
            ·
              refine ⟨71667695351684992199126051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47778463567789994799417367 71667695351684992199126051)
              ·
                refine ⟨107501543027527488298689077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71667695351684992199126051 107501543027527488298689077)
                ·
                  refine ⟨10078269658830702028002101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107501543027527488298689077 10078269658830702028002101)
                  ·
                    refine ⟨944837780515378315125197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10078269658830702028002101 944837780515378315125197)
                    ·
                      rfl

theorem cell23_5520195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 5].length) (baseStart_5520195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520195 prefixEnd_5520195 := by exact prefixLift 5520195
  have htrace : WordTrace (prefixWord ++ tailWord_5520195) baseStart_5520195 baseEnd_5520195 := by
    simpa [prefixWord, tailWord_5520195, baseEnd_5520195] using wordTrace_append hprefix tailTrace_5520195
  have hstable : (prefixWord ++ tailWord_5520195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520195).length < 2 ^ (prefixWord ++ tailWord_5520195).sum := by decide
  have hdescent : baseEnd_5520195 < baseStart_5520195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520225 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_5520225 : Nat := 118140960795 + 5520225 * 2 ^ 59
def prefixEnd_5520225 : Nat := 4983230072969 + 3 ^ 40 * 5520225 * 2
def baseEnd_5520225 : Nat := 944842915321923276000151

theorem tailTrace_5520225 : CollatzResearch.WordTrace tailWord_5520225 prefixEnd_5520225 944842915321923276000151 := by
  unfold tailWord_5520225
  simp only [CollatzResearch.WordTrace]
  refine ⟨201339146426175079216610129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134226097617450052811073419 201339146426175079216610129)
  ·
    refine ⟨151004359819631309412457597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201339146426175079216610129 151004359819631309412457597)
    ·
      refine ⟨56626634932361741029671599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151004359819631309412457597 56626634932361741029671599)
      ·
        refine ⟨84939952398542611544507399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56626634932361741029671599 84939952398542611544507399)
        ·
          refine ⟨127409928597813917316761099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84939952398542611544507399 127409928597813917316761099)
          ·
            refine ⟨191114892896720875975141649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127409928597813917316761099 191114892896720875975141649)
            ·
              refine ⟨143336169672540656981356237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191114892896720875975141649 143336169672540656981356237)
              ·
                refine ⟨53751063627202746368008589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143336169672540656981356237 53751063627202746368008589)
                ·
                  refine ⟨20156648860201029888003221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53751063627202746368008589 20156648860201029888003221)
                  ·
                    refine ⟨944842915321923276000151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20156648860201029888003221 944842915321923276000151)
                    ·
                      rfl

theorem cell23_5520225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_5520225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520225 prefixEnd_5520225 := by exact prefixLift 5520225
  have htrace : WordTrace (prefixWord ++ tailWord_5520225) baseStart_5520225 baseEnd_5520225 := by
    simpa [prefixWord, tailWord_5520225, baseEnd_5520225] using wordTrace_append hprefix tailTrace_5520225
  have hstable : (prefixWord ++ tailWord_5520225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520225).length < 2 ^ (prefixWord ++ tailWord_5520225).sum := by decide
  have hdescent : baseEnd_5520225 < baseStart_5520225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520229 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_5520229 : Nat := 118140960795 + 5520229 * 2 ^ 59
def prefixEnd_5520229 : Nat := 4983230072969 + 3 ^ 40 * 5520229 * 2
def baseEnd_5520229 : Nat := 944843599962795937450145

theorem tailTrace_5520229 : CollatzResearch.WordTrace tailWord_5520229 prefixEnd_5520229 944843599962795937450145 := by
  unfold tailWord_5520229
  simp only [CollatzResearch.WordTrace]
  refine ⟨201339292318160587899755741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134226194878773725266503827 201339292318160587899755741)
  ·
    refine ⟨75502234619310220462408403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201339292318160587899755741 75502234619310220462408403)
    ·
      refine ⟨113253351928965330693612605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75502234619310220462408403 113253351928965330693612605)
      ·
        refine ⟨42470006973361999010104727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113253351928965330693612605 42470006973361999010104727)
        ·
          refine ⟨63705010460042998515157091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42470006973361999010104727 63705010460042998515157091)
          ·
            refine ⟨95557515690064497772735637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63705010460042998515157091 95557515690064497772735637)
            ·
              refine ⟨4479258547971773333096983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 95557515690064497772735637 4479258547971773333096983)
              ·
                refine ⟨6718887821957659999645475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479258547971773333096983 6718887821957659999645475)
                ·
                  refine ⟨10078331732936489999468213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718887821957659999645475 10078331732936489999468213)
                  ·
                    refine ⟨944843599962795937450145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10078331732936489999468213 944843599962795937450145)
                    ·
                      rfl

theorem cell23_5520229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_5520229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520229 prefixEnd_5520229 := by exact prefixLift 5520229
  have htrace : WordTrace (prefixWord ++ tailWord_5520229) baseStart_5520229 baseEnd_5520229 := by
    simpa [prefixWord, tailWord_5520229, baseEnd_5520229] using wordTrace_append hprefix tailTrace_5520229
  have hstable : (prefixWord ++ tailWord_5520229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520229).length < 2 ^ (prefixWord ++ tailWord_5520229).sum := by decide
  have hdescent : baseEnd_5520229 < baseStart_5520229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520252 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_5520252 : Nat := 118140960795 + 5520252 * 2 ^ 59
def prefixEnd_5520252 : Nat := 4983230072969 + 3 ^ 40 * 5520252 * 2
def baseEnd_5520252 : Nat := 2834542609943441222362829

theorem tailTrace_5520252 : CollatzResearch.WordTrace tailWord_5520252 prefixEnd_5520252 2834542609943441222362829 := by
  unfold tailWord_5520252
  simp only [CollatzResearch.WordTrace]
  refine ⟨100670065598538631413921505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134226754131384841885228673 100670065598538631413921505)
  ·
    refine ⟨75502549198903973560441129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100670065598538631413921505 75502549198903973560441129)
    ·
      refine ⟨56626911899177980170330847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75502549198903973560441129 56626911899177980170330847)
      ·
        refine ⟨84940367848766970255496271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56626911899177980170330847 84940367848766970255496271)
        ·
          refine ⟨127410551773150455383244407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84940367848766970255496271 127410551773150455383244407)
          ·
            refine ⟨191115827659725683074866611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127410551773150455383244407 191115827659725683074866611)
            ·
              refine ⟨286673741489588524612299917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191115827659725683074866611 286673741489588524612299917)
              ·
                refine ⟨107502653058595696729612469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286673741489588524612299917 107502653058595696729612469)
                ·
                  refine ⟨10078373724243346568401169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107502653058595696729612469 10078373724243346568401169)
                  ·
                    refine ⟨7558780293182509926300877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10078373724243346568401169 7558780293182509926300877)
                    ·
                      refine ⟨2834542609943441222362829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558780293182509926300877 2834542609943441222362829)
                      ·
                        rfl

theorem cell23_5520252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_5520252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520252 prefixEnd_5520252 := by exact prefixLift 5520252
  have htrace : WordTrace (prefixWord ++ tailWord_5520252) baseStart_5520252 baseEnd_5520252 := by
    simpa [prefixWord, tailWord_5520252, baseEnd_5520252] using wordTrace_append hprefix tailTrace_5520252
  have hstable : (prefixWord ++ tailWord_5520252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520252).length < 2 ^ (prefixWord ++ tailWord_5520252).sum := by decide
  have hdescent : baseEnd_5520252 < baseStart_5520252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520266 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5520266 : Nat := 118140960795 + 5520266 * 2 ^ 59
def prefixEnd_5520266 : Nat := 4983230072969 + 3 ^ 40 * 5520266 * 2
def baseEnd_5520266 : Nat := 2834549798672604167587765

theorem tailTrace_5520266 : CollatzResearch.WordTrace tailWord_5520266 prefixEnd_5520266 2834549798672604167587765 := by
  unfold tailWord_5520266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50335160454756635804713163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134227094546017695479235101 50335160454756635804713163)
  ·
    refine ⟨75502740682134953707069745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50335160454756635804713163 75502740682134953707069745)
    ·
      refine ⟨56627055511601215280302309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75502740682134953707069745 56627055511601215280302309)
      ·
        refine ⟨10617572908425227865056683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56627055511601215280302309 10617572908425227865056683)
        ·
          refine ⟨15926359362637841797585025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617572908425227865056683 15926359362637841797585025)
          ·
            refine ⟨11944769521978381348188769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15926359362637841797585025 11944769521978381348188769)
            ·
              refine ⟨8958577141483786011141577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11944769521978381348188769 8958577141483786011141577)
              ·
                refine ⟨6718932856112839508356183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8958577141483786011141577 6718932856112839508356183)
                ·
                  refine ⟨10078399284169259262534275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6718932856112839508356183 10078399284169259262534275)
                  ·
                    refine ⟨15117598926253888893801413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10078399284169259262534275 15117598926253888893801413)
                    ·
                      refine ⟨2834549798672604167587765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15117598926253888893801413 2834549798672604167587765)
                      ·
                        rfl

theorem cell23_5520266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5520266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520266 prefixEnd_5520266 := by exact prefixLift 5520266
  have htrace : WordTrace (prefixWord ++ tailWord_5520266) baseStart_5520266 baseEnd_5520266 := by
    simpa [prefixWord, tailWord_5520266, baseEnd_5520266] using wordTrace_append hprefix tailTrace_5520266
  have hstable : (prefixWord ++ tailWord_5520266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520266).length < 2 ^ (prefixWord ++ tailWord_5520266).sum := by decide
  have hdescent : baseEnd_5520266 < baseStart_5520266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520359 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5520359 : Nat := 118140960795 + 5520359 * 2 ^ 59
def prefixEnd_5520359 : Nat := 4983230072969 + 3 ^ 40 * 5520359 * 2
def baseEnd_5520359 : Nat := 2834597552373472303724837

theorem tailTrace_5520359 : CollatzResearch.WordTrace tailWord_5520359 prefixEnd_5520359 2834597552373472303724837 := by
  unfold tailWord_5520359
  simp only [CollatzResearch.WordTrace]
  refine ⟨201344033807689620101988131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134229355871793080067992087 201344033807689620101988131)
  ·
    refine ⟨302016050711534430152982197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201344033807689620101988131 302016050711534430152982197)
    ·
      refine ⟨28314004754206352826842081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302016050711534430152982197 28314004754206352826842081)
      ·
        refine ⟨21235503565654764620131561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28314004754206352826842081 21235503565654764620131561)
        ·
          refine ⟨15926627674241073465098671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21235503565654764620131561 15926627674241073465098671)
          ·
            refine ⟨23889941511361610197648007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15926627674241073465098671 23889941511361610197648007)
            ·
              refine ⟨35834912267042415296472011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23889941511361610197648007 35834912267042415296472011)
              ·
                refine ⟨53752368400563622944708017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35834912267042415296472011 53752368400563622944708017)
                ·
                  refine ⟨40314276300422717208531013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53752368400563622944708017 40314276300422717208531013)
                  ·
                    refine ⟨7558926806329259476599565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40314276300422717208531013 7558926806329259476599565)
                    ·
                      refine ⟨2834597552373472303724837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7558926806329259476599565 2834597552373472303724837)
                      ·
                        rfl

theorem cell23_5520359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5520359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520359 prefixEnd_5520359 := by exact prefixLift 5520359
  have htrace : WordTrace (prefixWord ++ tailWord_5520359) baseStart_5520359 baseEnd_5520359 := by
    simpa [prefixWord, tailWord_5520359, baseEnd_5520359] using wordTrace_append hprefix tailTrace_5520359
  have hstable : (prefixWord ++ tailWord_5520359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520359).length < 2 ^ (prefixWord ++ tailWord_5520359).sum := by decide
  have hdescent : baseEnd_5520359 < baseStart_5520359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520369 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_5520369 : Nat := 118140960795 + 5520369 * 2 ^ 59
def prefixEnd_5520369 : Nat := 4983230072969 + 3 ^ 40 * 5520369 * 2
def baseEnd_5520369 : Nat := 2834602687180017264599791

theorem tailTrace_5520369 : CollatzResearch.WordTrace tailWord_5520369 prefixEnd_5520369 2834602687180017264599791 := by
  unfold tailWord_5520369
  simp only [CollatzResearch.WordTrace]
  refine ⟨201344398537653391809852161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134229599025102261206568107 201344398537653391809852161)
  ·
    refine ⟨151008298903240043857389121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201344398537653391809852161 151008298903240043857389121)
    ·
      refine ⟨113256224177430032893041841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151008298903240043857389121 113256224177430032893041841)
      ·
        refine ⟨84942168133072524669781381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113256224177430032893041841 84942168133072524669781381)
        ·
          refine ⟨15926656524951098375584009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84942168133072524669781381 15926656524951098375584009)
          ·
            refine ⟨11944992393713323781688007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15926656524951098375584009 11944992393713323781688007)
            ·
              refine ⟨17917488590569985672532011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11944992393713323781688007 17917488590569985672532011)
              ·
                refine ⟨26876232885854978508798017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17917488590569985672532011 26876232885854978508798017)
                ·
                  refine ⟨20157174664391233881598513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26876232885854978508798017 20157174664391233881598513)
                  ·
                    refine ⟨15117880998293425411198885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20157174664391233881598513 15117880998293425411198885)
                    ·
                      refine ⟨2834602687180017264599791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15117880998293425411198885 2834602687180017264599791)
                      ·
                        rfl

theorem cell23_5520369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_5520369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520369 prefixEnd_5520369 := by exact prefixLift 5520369
  have htrace : WordTrace (prefixWord ++ tailWord_5520369) baseStart_5520369 baseEnd_5520369 := by
    simpa [prefixWord, tailWord_5520369, baseEnd_5520369] using wordTrace_append hprefix tailTrace_5520369
  have hstable : (prefixWord ++ tailWord_5520369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520369).length < 2 ^ (prefixWord ++ tailWord_5520369).sum := by decide
  have hdescent : baseEnd_5520369 < baseStart_5520369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520396 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 5]
def baseStart_5520396 : Nat := 118140960795 + 5520396 * 2 ^ 59
def prefixEnd_5520396 : Nat := 4983230072969 + 3 ^ 40 * 5520396 * 2
def baseEnd_5520396 : Nat := 314957394573076517662463

theorem tailTrace_5520396 : CollatzResearch.WordTrace tailWord_5520396 prefixEnd_5520396 314957394573076517662463 := by
  unfold tailWord_5520396
  simp only [CollatzResearch.WordTrace]
  refine ⟨100672691654277787710542521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134230255539037050280723361 100672691654277787710542521)
  ·
    refine ⟨75504518740708340782906891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100672691654277787710542521 75504518740708340782906891)
    ·
      refine ⟨113256778111062511174360337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75504518740708340782906891 113256778111062511174360337)
      ·
        refine ⟨84942583583296883380770253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113256778111062511174360337 84942583583296883380770253)
        ·
          refine ⟨31853468843736331267788845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84942583583296883380770253 31853468843736331267788845)
          ·
            refine ⟨11945050816401124225420817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31853468843736331267788845 11945050816401124225420817)
            ·
              refine ⟨8958788112300843169065613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11945050816401124225420817 8958788112300843169065613)
              ·
                refine ⟨3359545542112816188399605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8958788112300843169065613 3359545542112816188399605)
                ·
                  refine ⟨314957394573076517662463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359545542112816188399605 314957394573076517662463)
                  ·
                    rfl

theorem cell23_5520396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_5520396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520396 prefixEnd_5520396 := by exact prefixLift 5520396
  have htrace : WordTrace (prefixWord ++ tailWord_5520396) baseStart_5520396 baseEnd_5520396 := by
    simpa [prefixWord, tailWord_5520396, baseEnd_5520396] using wordTrace_append hprefix tailTrace_5520396
  have hstable : (prefixWord ++ tailWord_5520396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520396).length < 2 ^ (prefixWord ++ tailWord_5520396).sum := by decide
  have hdescent : baseEnd_5520396 < baseStart_5520396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520446 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5520446 : Nat := 118140960795 + 5520446 * 2 ^ 59
def prefixEnd_5520446 : Nat := 4983230072969 + 3 ^ 40 * 5520446 * 2
def baseEnd_5520446 : Nat := 2834642225190413463336937

theorem tailTrace_5520446 : CollatzResearch.WordTrace tailWord_5520446 prefixEnd_5520446 2834642225190413463336937 := by
  unfold tailWord_5520446
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168400869796804245050649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134231471305582955973603461 25168400869796804245050649)
  ·
    refine ⟨18876300652347603183787987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25168400869796804245050649 18876300652347603183787987)
    ·
      refine ⟨28314450978521404775681981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18876300652347603183787987 28314450978521404775681981)
      ·
        refine ⟨10617919116945526790880743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28314450978521404775681981 10617919116945526790880743)
        ·
          refine ⟨15926878675418290186321115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10617919116945526790880743 15926878675418290186321115)
          ·
            refine ⟨23890318013127435279481673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15926878675418290186321115 23890318013127435279481673)
            ·
              refine ⟨17917738509845576459611255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23890318013127435279481673 17917738509845576459611255)
              ·
                refine ⟨26876607764768364689416883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17917738509845576459611255 26876607764768364689416883)
                ·
                  refine ⟨40314911647152547034125325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26876607764768364689416883 40314911647152547034125325)
                  ·
                    refine ⟨15118091867682205137796997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40314911647152547034125325 15118091867682205137796997)
                    ·
                      refine ⟨2834642225190413463336937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15118091867682205137796997 2834642225190413463336937)
                      ·
                        rfl

theorem cell23_5520446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5520446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520446 prefixEnd_5520446 := by exact prefixLift 5520446
  have htrace : WordTrace (prefixWord ++ tailWord_5520446) baseStart_5520446 baseEnd_5520446 := by
    simpa [prefixWord, tailWord_5520446, baseEnd_5520446] using wordTrace_append hprefix tailTrace_5520446
  have hstable : (prefixWord ++ tailWord_5520446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520446).length < 2 ^ (prefixWord ++ tailWord_5520446).sum := by decide
  have hdescent : baseEnd_5520446 < baseStart_5520446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520466 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_5520466 : Nat := 118140960795 + 5520466 * 2 ^ 59
def prefixEnd_5520466 : Nat := 4983230072969 + 3 ^ 40 * 5520466 * 2
def baseEnd_5520466 : Nat := 2834652494803503385086845

theorem tailTrace_5520466 : CollatzResearch.WordTrace tailWord_5520466 prefixEnd_5520466 2834652494803503385086845 := by
  unfold tailWord_5520466
  simp only [CollatzResearch.WordTrace]
  refine ⟨50336984104575494344033313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134231957612201318250755501 50336984104575494344033313)
  ·
    refine ⟨37752738078431620758024985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50336984104575494344033313 37752738078431620758024985)
    ·
      refine ⟨28314553558823715568518739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37752738078431620758024985 28314553558823715568518739)
      ·
        refine ⟨42471830338235573352778109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28314553558823715568518739 42471830338235573352778109)
        ·
          refine ⟨15926936376838340007291791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42471830338235573352778109 15926936376838340007291791)
          ·
            refine ⟨23890404565257510010937687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15926936376838340007291791 23890404565257510010937687)
            ·
              refine ⟨35835606847886265016406531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23890404565257510010937687 35835606847886265016406531)
              ·
                refine ⟨53753410271829397524609797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35835606847886265016406531 53753410271829397524609797)
                ·
                  refine ⟨10078764425968012035864337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53753410271829397524609797 10078764425968012035864337)
                  ·
                    refine ⟨7559073319476009026898253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10078764425968012035864337 7559073319476009026898253)
                    ·
                      refine ⟨2834652494803503385086845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7559073319476009026898253 2834652494803503385086845)
                      ·
                        rfl

theorem cell23_5520466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_5520466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520466 prefixEnd_5520466 := by exact prefixLift 5520466
  have htrace : WordTrace (prefixWord ++ tailWord_5520466) baseStart_5520466 baseEnd_5520466 := by
    simpa [prefixWord, tailWord_5520466, baseEnd_5520466] using wordTrace_append hprefix tailTrace_5520466
  have hstable : (prefixWord ++ tailWord_5520466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520466).length < 2 ^ (prefixWord ++ tailWord_5520466).sum := by decide
  have hdescent : baseEnd_5520466 < baseStart_5520466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520469 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 6]
def baseStart_5520469 : Nat := 118140960795 + 5520469 * 2 ^ 59
def prefixEnd_5520469 : Nat := 4983230072969 + 3 ^ 40 * 5520469 * 2
def baseEnd_5520469 : Nat := 314961559471718541483259

theorem tailTrace_5520469 : CollatzResearch.WordTrace tailWord_5520469 prefixEnd_5520469 314961559471718541483259 := by
  unfold tailWord_5520469
  simp only [CollatzResearch.WordTrace]
  refine ⟨201348045837291108888492461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134232030558194072592328307 201348045837291108888492461)
  ·
    refine ⟨75505517188984165833184673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201348045837291108888492461 75505517188984165833184673)
    ·
      refine ⟨56629137891738124374888505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75505517188984165833184673 56629137891738124374888505)
      ·
        refine ⟨42471853418803593281166379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56629137891738124374888505 42471853418803593281166379)
        ·
          refine ⟨63707780128205389921749569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42471853418803593281166379 63707780128205389921749569)
          ·
            refine ⟨47780835096154042441312177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63707780128205389921749569 47780835096154042441312177)
            ·
              refine ⟨35835626322115531830984133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47780835096154042441312177 35835626322115531830984133)
              ·
                refine ⟨6719179935396662218309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35835626322115531830984133 6719179935396662218309525)
                ·
                  refine ⟨314961559471718541483259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6719179935396662218309525 314961559471718541483259)
                  ·
                    rfl

theorem cell23_5520469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_5520469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520469 prefixEnd_5520469 := by exact prefixLift 5520469
  have htrace : WordTrace (prefixWord ++ tailWord_5520469) baseStart_5520469 baseEnd_5520469 := by
    simpa [prefixWord, tailWord_5520469, baseEnd_5520469] using wordTrace_append hprefix tailTrace_5520469
  have hstable : (prefixWord ++ tailWord_5520469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520469).length < 2 ^ (prefixWord ++ tailWord_5520469).sum := by decide
  have hdescent : baseEnd_5520469 < baseStart_5520469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520496 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_5520496 : Nat := 118140960795 + 5520496 * 2 ^ 59
def prefixEnd_5520496 : Nat := 4983230072969 + 3 ^ 40 * 5520496 * 2
def baseEnd_5520496 : Nat := 2834667899223138267711707

theorem tailTrace_5520496 : CollatzResearch.WordTrace tailWord_5520496 prefixEnd_5520496 2834667899223138267711707 := by
  unfold tailWord_5520496
  simp only [CollatzResearch.WordTrace]
  refine ⟨100674515304096646249862671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134232687072128861666483561 100674515304096646249862671)
  ·
    refine ⟨151011772956144969374794007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100674515304096646249862671 151011772956144969374794007)
    ·
      refine ⟨226517659434217454062191011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151011772956144969374794007 226517659434217454062191011)
      ·
        refine ⟨339776489151326181093286517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226517659434217454062191011 339776489151326181093286517)
        ·
          refine ⟨31854045857936829477495611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339776489151326181093286517 31854045857936829477495611)
          ·
            refine ⟨47781068786905244216243417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31854045857936829477495611 47781068786905244216243417)
            ·
              refine ⟨35835801590178933162182563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47781068786905244216243417 35835801590178933162182563)
              ·
                refine ⟨53753702385268399743273845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35835801590178933162182563 53753702385268399743273845)
                ·
                  refine ⟨5039409598618912475931923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53753702385268399743273845 5039409598618912475931923)
                  ·
                    refine ⟨7559114397928368713897885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5039409598618912475931923 7559114397928368713897885)
                    ·
                      refine ⟨2834667899223138267711707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7559114397928368713897885 2834667899223138267711707)
                      ·
                        rfl

theorem cell23_5520496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_5520496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520496 prefixEnd_5520496 := by exact prefixLift 5520496
  have htrace : WordTrace (prefixWord ++ tailWord_5520496) baseStart_5520496 baseEnd_5520496 := by
    simpa [prefixWord, tailWord_5520496, baseEnd_5520496] using wordTrace_append hprefix tailTrace_5520496
  have hstable : (prefixWord ++ tailWord_5520496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520496).length < 2 ^ (prefixWord ++ tailWord_5520496).sum := by decide
  have hdescent : baseEnd_5520496 < baseStart_5520496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520536 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5520536 : Nat := 118140960795 + 5520536 * 2 ^ 59
def prefixEnd_5520536 : Nat := 4983230072969 + 3 ^ 40 * 5520536 * 2
def baseEnd_5520536 : Nat := 2834688438449318111211523

theorem tailTrace_5520536 : CollatzResearch.WordTrace tailWord_5520536 prefixEnd_5520536 2834688438449318111211523 := by
  unfold tailWord_5520536
  simp only [CollatzResearch.WordTrace]
  refine ⟨100675244764024189665590731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134233659685365586220787641 100675244764024189665590731)
  ·
    refine ⟨151012867146036284498386097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100675244764024189665590731 151012867146036284498386097)
    ·
      refine ⟨113259650359527213373789573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151012867146036284498386097 113259650359527213373789573)
      ·
        refine ⟨21236184442411352507585545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113259650359527213373789573 21236184442411352507585545)
        ·
          refine ⟨15927138331808514380689159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21236184442411352507585545 15927138331808514380689159)
          ·
            refine ⟨23890707497712771571033739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15927138331808514380689159 23890707497712771571033739)
            ·
              refine ⟨35836061246569157356550609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23890707497712771571033739 35836061246569157356550609)
              ·
                refine ⟨26877045934926868017412957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35836061246569157356550609 26877045934926868017412957)
                ·
                  refine ⟨10078892225597575506529859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26877045934926868017412957 10078892225597575506529859)
                  ·
                    refine ⟨15118338338396363259794789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10078892225597575506529859 15118338338396363259794789)
                    ·
                      refine ⟨2834688438449318111211523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15118338338396363259794789 2834688438449318111211523)
                      ·
                        rfl

theorem cell23_5520536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5520536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520536 prefixEnd_5520536 := by exact prefixLift 5520536
  have htrace : WordTrace (prefixWord ++ tailWord_5520536) baseStart_5520536 baseEnd_5520536 := by
    simpa [prefixWord, tailWord_5520536, baseEnd_5520536] using wordTrace_append hprefix tailTrace_5520536
  have hstable : (prefixWord ++ tailWord_5520536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520536).length < 2 ^ (prefixWord ++ tailWord_5520536).sum := by decide
  have hdescent : baseEnd_5520536 < baseStart_5520536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520557 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_5520557 : Nat := 118140960795 + 5520557 * 2 ^ 59
def prefixEnd_5520557 : Nat := 4983230072969 + 3 ^ 40 * 5520557 * 2
def baseEnd_5520557 : Nat := 2834699221543062529048927

theorem tailTrace_5520557 : CollatzResearch.WordTrace tailWord_5520557 prefixEnd_5520557 2834699221543062529048927 := by
  unfold tailWord_5520557
  simp only [CollatzResearch.WordTrace]
  refine ⟨201351255460972299917695925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134234170307314866611797283 201351255460972299917695925)
  ·
    refine ⟨18876680199466153117283993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201351255460972299917695925 18876680199466153117283993)
    ·
      refine ⟨14157510149599614837962995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18876680199466153117283993 14157510149599614837962995)
      ·
        refine ⟨21236265224399422256944493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14157510149599614837962995 21236265224399422256944493)
        ·
          refine ⟨7963599459149783346354185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21236265224399422256944493 7963599459149783346354185)
          ·
            refine ⟨5972699594362337509765639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7963599459149783346354185 5972699594362337509765639)
            ·
              refine ⟨8959049391543506264648459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972699594362337509765639 8959049391543506264648459)
              ·
                refine ⟨13438574087315259396972689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959049391543506264648459 13438574087315259396972689)
                ·
                  refine ⟨10078930565486444547729517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13438574087315259396972689 10078930565486444547729517)
                  ·
                    refine ⟨3779598962057416705398569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10078930565486444547729517 3779598962057416705398569)
                    ·
                      refine ⟨2834699221543062529048927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779598962057416705398569 2834699221543062529048927)
                      ·
                        rfl

theorem cell23_5520557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_5520557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520557 prefixEnd_5520557 := by exact prefixLift 5520557
  have htrace : WordTrace (prefixWord ++ tailWord_5520557) baseStart_5520557 baseEnd_5520557 := by
    simpa [prefixWord, tailWord_5520557, baseEnd_5520557] using wordTrace_append hprefix tailTrace_5520557
  have hstable : (prefixWord ++ tailWord_5520557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520557).length < 2 ^ (prefixWord ++ tailWord_5520557).sum := by decide
  have hdescent : baseEnd_5520557 < baseStart_5520557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520600 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_5520600 : Nat := 118140960795 + 5520600 * 2 ^ 59
def prefixEnd_5520600 : Nat := 4983230072969 + 3 ^ 40 * 5520600 * 2
def baseEnd_5520600 : Nat := 2834721301211205860811229

theorem tailTrace_5520600 : CollatzResearch.WordTrace tailWord_5520600 prefixEnd_5520600 2834721301211205860811229 := by
  unfold tailWord_5520600
  simp only [CollatzResearch.WordTrace]
  refine ⟨100676411899908259130755627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134235215866544345507674169 100676411899908259130755627)
  ·
    refine ⟨151014617849862388696133441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100676411899908259130755627 151014617849862388696133441)
    ·
      refine ⟨113260963387396791522100081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151014617849862388696133441 113260963387396791522100081)
      ·
        refine ⟨84945722540547593641575061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113260963387396791522100081 84945722540547593641575061)
        ·
          refine ⟨3981830744088168451948831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84945722540547593641575061 3981830744088168451948831)
          ·
            refine ⟨5972746116132252677923247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981830744088168451948831 5972746116132252677923247)
            ·
              refine ⟨8959119174198379016884871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5972746116132252677923247 8959119174198379016884871)
              ·
                refine ⟨13438678761297568525327307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959119174198379016884871 13438678761297568525327307)
                ·
                  refine ⟨20158018141946352787990961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13438678761297568525327307 20158018141946352787990961)
                  ·
                    refine ⟨15118513606459764590993221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20158018141946352787990961 15118513606459764590993221)
                    ·
                      refine ⟨2834721301211205860811229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15118513606459764590993221 2834721301211205860811229)
                      ·
                        rfl

theorem cell23_5520600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_5520600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520600 prefixEnd_5520600 := by exact prefixLift 5520600
  have htrace : WordTrace (prefixWord ++ tailWord_5520600) baseStart_5520600 baseEnd_5520600 := by
    simpa [prefixWord, tailWord_5520600, baseEnd_5520600] using wordTrace_append hprefix tailTrace_5520600
  have hstable : (prefixWord ++ tailWord_5520600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520600).length < 2 ^ (prefixWord ++ tailWord_5520600).sum := by decide
  have hdescent : baseEnd_5520600 < baseStart_5520600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520700 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 5]
def baseStart_5520700 : Nat := 118140960795 + 5520700 * 2 ^ 59
def prefixEnd_5520700 : Nat := 4983230072969 + 3 ^ 40 * 5520700 * 2
def baseEnd_5520700 : Nat := 314974738808517274395641

theorem tailTrace_5520700 : CollatzResearch.WordTrace tailWord_5520700 prefixEnd_5520700 314974738808517274395641 := by
  unfold tailWord_5520700
  simp only [CollatzResearch.WordTrace]
  refine ⟨100678235549727117670075777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134237647399636156893434369 100678235549727117670075777)
  ·
    refine ⟨75508676662295338252556833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100678235549727117670075777 75508676662295338252556833)
    ·
      refine ⟨56631507496721503689417625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75508676662295338252556833 56631507496721503689417625)
      ·
        refine ⟨42473630622541127767063219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56631507496721503689417625 42473630622541127767063219)
        ·
          refine ⟨63710445933811691650594829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42473630622541127767063219 63710445933811691650594829)
          ·
            refine ⟨23891417225179384368973061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63710445933811691650594829 23891417225179384368973061)
            ·
              refine ⟨4479640729721134569182449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23891417225179384368973061 4479640729721134569182449)
              ·
                refine ⟨3359730547290850926886837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4479640729721134569182449 3359730547290850926886837)
                ·
                  refine ⟨314974738808517274395641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3359730547290850926886837 314974738808517274395641)
                  ·
                    rfl

theorem cell23_5520700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_5520700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520700 prefixEnd_5520700 := by exact prefixLift 5520700
  have htrace : WordTrace (prefixWord ++ tailWord_5520700) baseStart_5520700 baseEnd_5520700 := by
    simpa [prefixWord, tailWord_5520700, baseEnd_5520700] using wordTrace_append hprefix tailTrace_5520700
  have hstable : (prefixWord ++ tailWord_5520700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520700).length < 2 ^ (prefixWord ++ tailWord_5520700).sum := by decide
  have hdescent : baseEnd_5520700 < baseStart_5520700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520703 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 5, 2]
def baseStart_5520703 : Nat := 118140960795 + 5520703 * 2 ^ 59
def prefixEnd_5520703 : Nat := 4983230072969 + 3 ^ 40 * 5520703 * 2
def baseEnd_5520703 : Nat := 2834774189718618957823255

theorem tailTrace_5520703 : CollatzResearch.WordTrace tailWord_5520703 prefixEnd_5520703 2834774189718618957823255 := by
  unfold tailWord_5520703
  simp only [CollatzResearch.WordTrace]
  refine ⟨201356580518443366852510763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134237720345628911235007175 201356580518443366852510763)
  ·
    refine ⟨302034870777665050278766145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201356580518443366852510763 302034870777665050278766145)
    ·
      refine ⟨226526153083248787709074609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302034870777665050278766145 226526153083248787709074609)
      ·
        refine ⟨169894614812436590781805957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226526153083248787709074609 169894614812436590781805957)
        ·
          refine ⟨31855240277331860771588617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169894614812436590781805957 31855240277331860771588617)
          ·
            refine ⟨23891430207998895578691463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31855240277331860771588617 23891430207998895578691463)
            ·
              refine ⟨35837145311998343368037195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23891430207998895578691463 35837145311998343368037195)
              ·
                refine ⟨53755717967997515052055793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35837145311998343368037195 53755717967997515052055793)
                ·
                  refine ⟨40316788475998136289041845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53755717967997515052055793 40316788475998136289041845)
                  ·
                    refine ⟨3779698919624825277097673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40316788475998136289041845 3779698919624825277097673)
                    ·
                      refine ⟨2834774189718618957823255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779698919624825277097673 2834774189718618957823255)
                      ·
                        rfl

theorem cell23_5520703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_5520703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520703 prefixEnd_5520703 := by exact prefixLift 5520703
  have htrace : WordTrace (prefixWord ++ tailWord_5520703) baseStart_5520703 baseEnd_5520703 := by
    simpa [prefixWord, tailWord_5520703, baseEnd_5520703] using wordTrace_append hprefix tailTrace_5520703
  have hstable : (prefixWord ++ tailWord_5520703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520703).length < 2 ^ (prefixWord ++ tailWord_5520703).sum := by decide
  have hdescent : baseEnd_5520703 < baseStart_5520703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520753 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_5520753 : Nat := 118140960795 + 5520753 * 2 ^ 59
def prefixEnd_5520753 : Nat := 4983230072969 + 3 ^ 40 * 5520753 * 2
def baseEnd_5520753 : Nat := 2834799863751343762198025

theorem tailTrace_5520753 : CollatzResearch.WordTrace tailWord_5520753 prefixEnd_5520753 2834799863751343762198025 := by
  unfold tailWord_5520753
  simp only [CollatzResearch.WordTrace]
  refine ⟨201358404168262225391830913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134238936112174816927887275 201358404168262225391830913)
  ·
    refine ⟨151018803126196669043873185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201358404168262225391830913 151018803126196669043873185)
    ·
      refine ⟨113264102344647501782904889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151018803126196669043873185 113264102344647501782904889)
      ·
        refine ⟨84948076758485626337178667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113264102344647501782904889 84948076758485626337178667)
        ·
          refine ⟨127422115137728439505768001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84948076758485626337178667 127422115137728439505768001)
          ·
            refine ⟨95566586353296329629326001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127422115137728439505768001 95566586353296329629326001)
            ·
              refine ⟨71674939764972247221994501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95566586353296329629326001 71674939764972247221994501)
              ·
                refine ⟨13439051205932296354123969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71674939764972247221994501 13439051205932296354123969)
                ·
                  refine ⟨10079288404449222265592977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13439051205932296354123969 10079288404449222265592977)
                  ·
                    refine ⟨7559466303336916699194733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10079288404449222265592977 7559466303336916699194733)
                    ·
                      refine ⟨2834799863751343762198025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7559466303336916699194733 2834799863751343762198025)
                      ·
                        rfl

theorem cell23_5520753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_5520753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520753 prefixEnd_5520753 := by exact prefixLift 5520753
  have htrace : WordTrace (prefixWord ++ tailWord_5520753) baseStart_5520753 baseEnd_5520753 := by
    simpa [prefixWord, tailWord_5520753, baseEnd_5520753] using wordTrace_append hprefix tailTrace_5520753
  have hstable : (prefixWord ++ tailWord_5520753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520753).length < 2 ^ (prefixWord ++ tailWord_5520753).sum := by decide
  have hdescent : baseEnd_5520753 < baseStart_5520753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520803 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 1, 5]
def baseStart_5520803 : Nat := 118140960795 + 5520803 * 2 ^ 59
def prefixEnd_5520803 : Nat := 4983230072969 + 3 ^ 40 * 5520803 * 2
def baseEnd_5520803 : Nat := 944941845928022855524265

theorem tailTrace_5520803 : CollatzResearch.WordTrace tailWord_5520803 prefixEnd_5520803 944941845928022855524265 := by
  unfold tailWord_5520803
  simp only [CollatzResearch.WordTrace]
  refine ⟨201360227818081083931151063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134240151878720722620767375 201360227818081083931151063)
  ·
    refine ⟨302040341727121625896726595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201360227818081083931151063 302040341727121625896726595)
    ·
      refine ⟨453060512590682438845089893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302040341727121625896726595 453060512590682438845089893)
      ·
        refine ⟨84948846110752957283454355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453060512590682438845089893 84948846110752957283454355)
        ·
          refine ⟨127423269166129435925181533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84948846110752957283454355 127423269166129435925181533)
          ·
            refine ⟨47783725937298538471943075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127423269166129435925181533 47783725937298538471943075)
            ·
              refine ⟨71675588905947807707914613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47783725937298538471943075 71675588905947807707914613)
              ·
                refine ⟨6719586459932606972616995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71675588905947807707914613 6719586459932606972616995)
                ·
                  refine ⟨10079379689898910458925493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719586459932606972616995 10079379689898910458925493)
                  ·
                    refine ⟨944941845928022855524265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10079379689898910458925493 944941845928022855524265)
                    ·
                      rfl

theorem cell23_5520803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 5].length) (baseStart_5520803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520803 prefixEnd_5520803 := by exact prefixLift 5520803
  have htrace : WordTrace (prefixWord ++ tailWord_5520803) baseStart_5520803 baseEnd_5520803 := by
    simpa [prefixWord, tailWord_5520803, baseEnd_5520803] using wordTrace_append hprefix tailTrace_5520803
  have hstable : (prefixWord ++ tailWord_5520803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520803).length < 2 ^ (prefixWord ++ tailWord_5520803).sum := by decide
  have hdescent : baseEnd_5520803 < baseStart_5520803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520816 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_5520816 : Nat := 118140960795 + 5520816 * 2 ^ 59
def prefixEnd_5520816 : Nat := 4983230072969 + 3 ^ 40 * 5520816 * 2
def baseEnd_5520816 : Nat := 944944071010859005236745

theorem tailTrace_5520816 : CollatzResearch.WordTrace tailWord_5520816 prefixEnd_5520816 944944071010859005236745 := by
  unfold tailWord_5520816
  simp only [CollatzResearch.WordTrace]
  refine ⟨100680350983516993575687151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134240467978022658100916201 100680350983516993575687151)
  ·
    refine ⟨151020526475275490363530727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100680350983516993575687151 151020526475275490363530727)
    ·
      refine ⟨226530789712913235545296091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151020526475275490363530727 226530789712913235545296091)
      ·
        refine ⟨339796184569369853317944137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226530789712913235545296091 339796184569369853317944137)
        ·
          refine ⟨254847138427027389988458103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339796184569369853317944137 254847138427027389988458103)
          ·
            refine ⟨382270707640541084982687155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254847138427027389988458103 382270707640541084982687155)
            ·
              refine ⟨573406061460811627474030733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382270707640541084982687155 573406061460811627474030733)
              ·
                refine ⟨215027273047804360302761525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573406061460811627474030733 215027273047804360302761525)
                ·
                  refine ⟨20158806848231658778383893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215027273047804360302761525 20158806848231658778383893)
                  ·
                    refine ⟨944944071010859005236745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20158806848231658778383893 944944071010859005236745)
                    ·
                      rfl

theorem cell23_5520816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_5520816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520816 prefixEnd_5520816 := by exact prefixLift 5520816
  have htrace : WordTrace (prefixWord ++ tailWord_5520816) baseStart_5520816 baseEnd_5520816 := by
    simpa [prefixWord, tailWord_5520816, baseEnd_5520816] using wordTrace_append hprefix tailTrace_5520816
  have hstable : (prefixWord ++ tailWord_5520816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520816).length < 2 ^ (prefixWord ++ tailWord_5520816).sum := by decide
  have hdescent : baseEnd_5520816 < baseStart_5520816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520823 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_5520823 : Nat := 118140960795 + 5520823 * 2 ^ 59
def prefixEnd_5520823 : Nat := 4983230072969 + 3 ^ 40 * 5520823 * 2
def baseEnd_5520823 : Nat := 2834835807397158488322703

theorem tailTrace_5520823 : CollatzResearch.WordTrace tailWord_5520823 prefixEnd_5520823 2834835807397158488322703 := by
  unfold tailWord_5520823
  simp only [CollatzResearch.WordTrace]
  refine ⟨201360957278008627346879123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134240638185339084897919415 201360957278008627346879123)
  ·
    refine ⟨302041435917012941020318685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201360957278008627346879123 302041435917012941020318685)
    ·
      refine ⟨113265538468879852882619507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302041435917012941020318685 113265538468879852882619507)
      ·
        refine ⟨169898307703319779323929261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113265538468879852882619507 169898307703319779323929261)
        ·
          refine ⟨63711865388744917246473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169898307703319779323929261 63711865388744917246473473)
          ·
            refine ⟨47783899041558687934855105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63711865388744917246473473 47783899041558687934855105)
            ·
              refine ⟨35837924281169015951141329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47783899041558687934855105 35837924281169015951141329)
              ·
                refine ⟨26878443210876761963355997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35837924281169015951141329 26878443210876761963355997)
                ·
                  refine ⟨10079416204078785736258499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26878443210876761963355997 10079416204078785736258499)
                  ·
                    refine ⟨15119124306118178604387749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10079416204078785736258499 15119124306118178604387749)
                    ·
                      refine ⟨2834835807397158488322703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15119124306118178604387749 2834835807397158488322703)
                      ·
                        rfl

theorem cell23_5520823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_5520823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520823 prefixEnd_5520823 := by exact prefixLift 5520823
  have htrace : WordTrace (prefixWord ++ tailWord_5520823) baseStart_5520823 baseEnd_5520823 := by
    simpa [prefixWord, tailWord_5520823, baseEnd_5520823] using wordTrace_append hprefix tailTrace_5520823
  have hstable : (prefixWord ++ tailWord_5520823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520823).length < 2 ^ (prefixWord ++ tailWord_5520823).sum := by decide
  have hdescent : baseEnd_5520823 < baseStart_5520823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520854 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5520854 : Nat := 118140960795 + 5520854 * 2 ^ 59
def prefixEnd_5520854 : Nat := 4983230072969 + 3 ^ 40 * 5520854 * 2
def baseEnd_5520854 : Nat := 944950575099149289011687

theorem tailTrace_5520854 : CollatzResearch.WordTrace tailWord_5520854 prefixEnd_5520854 944950575099149289011687 := by
  unfold tailWord_5520854
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585130496306019977578601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134241391960597546427505077 12585130496306019977578601)
  ·
    refine ⟨9438847872229514983183951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12585130496306019977578601 9438847872229514983183951)
    ·
      refine ⟨14158271808344272474775927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9438847872229514983183951 14158271808344272474775927)
      ·
        refine ⟨21237407712516408712163891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14158271808344272474775927 21237407712516408712163891)
        ·
          refine ⟨31856111568774613068245837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21237407712516408712163891 31856111568774613068245837)
          ·
            refine ⟨11946041838290479900592189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31856111568774613068245837 11946041838290479900592189)
            ·
              refine ⟨4479765689358929962722071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11946041838290479900592189 4479765689358929962722071)
              ·
                refine ⟨6719648534038394944083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479765689358929962722071 6719648534038394944083107)
                ·
                  refine ⟨10079472801057592416124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719648534038394944083107 10079472801057592416124661)
                  ·
                    refine ⟨944950575099149289011687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10079472801057592416124661 944950575099149289011687)
                    ·
                      rfl

theorem cell23_5520854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5520854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520854 prefixEnd_5520854 := by exact prefixLift 5520854
  have htrace : WordTrace (prefixWord ++ tailWord_5520854) baseStart_5520854 baseEnd_5520854 := by
    simpa [prefixWord, tailWord_5520854, baseEnd_5520854] using wordTrace_append hprefix tailTrace_5520854
  have hstable : (prefixWord ++ tailWord_5520854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520854).length < 2 ^ (prefixWord ++ tailWord_5520854).sum := by decide
  have hdescent : baseEnd_5520854 < baseStart_5520854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520857 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 1, 1, 4]
def baseStart_5520857 : Nat := 118140960795 + 5520857 * 2 ^ 59
def prefixEnd_5520857 : Nat := 4983230072969 + 3 ^ 40 * 5520857 * 2
def baseEnd_5520857 : Nat := 2834853265739411355297547

theorem tailTrace_5520857 : CollatzResearch.WordTrace tailWord_5520857 prefixEnd_5520857 2834853265739411355297547 := by
  unfold tailWord_5520857
  simp only [CollatzResearch.WordTrace]
  refine ⟨201362197359885451153616825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134241464906590300769077883 201362197359885451153616825)
  ·
    refine ⟨151021648019914088365212619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201362197359885451153616825 151021648019914088365212619)
    ·
      refine ⟨226532472029871132547818929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151021648019914088365212619 226532472029871132547818929)
      ·
        refine ⟨169899354022403349410864197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226532472029871132547818929 169899354022403349410864197)
        ·
          refine ⟨31856128879200628014537037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169899354022403349410864197 31856128879200628014537037)
          ·
            refine ⟨11946048329700235505451389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31856128879200628014537037 11946048329700235505451389)
            ·
              refine ⟨4479768123637588314544271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11946048329700235505451389 4479768123637588314544271)
              ·
                refine ⟨6719652185456382471816407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4479768123637588314544271 6719652185456382471816407)
                ·
                  refine ⟨10079478278184573707724611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6719652185456382471816407 10079478278184573707724611)
                  ·
                    refine ⟨15119217417276860561586917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10079478278184573707724611 15119217417276860561586917)
                    ·
                      refine ⟨2834853265739411355297547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15119217417276860561586917 2834853265739411355297547)
                      ·
                        rfl

theorem cell23_5520857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_5520857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520857 prefixEnd_5520857 := by exact prefixLift 5520857
  have htrace : WordTrace (prefixWord ++ tailWord_5520857) baseStart_5520857 baseEnd_5520857 := by
    simpa [prefixWord, tailWord_5520857, baseEnd_5520857] using wordTrace_append hprefix tailTrace_5520857
  have hstable : (prefixWord ++ tailWord_5520857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520857).length < 2 ^ (prefixWord ++ tailWord_5520857).sum := by decide
  have hdescent : baseEnd_5520857 < baseStart_5520857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520867 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 2, 4]
def baseStart_5520867 : Nat := 118140960795 + 5520867 * 2 ^ 59
def prefixEnd_5520867 : Nat := 4983230072969 + 3 ^ 40 * 5520867 * 2
def baseEnd_5520867 : Nat := 944952800181985438724167

theorem tailTrace_5520867 : CollatzResearch.WordTrace tailWord_5520867 prefixEnd_5520867 944952800181985438724167 := by
  unfold tailWord_5520867
  simp only [CollatzResearch.WordTrace]
  refine ⟨201362562089849222861480855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134241708059899481907653903 201362562089849222861480855)
  ·
    refine ⟨302043843134773834292221283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201362562089849222861480855 302043843134773834292221283)
    ·
      refine ⟨453065764702160751438331925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302043843134773834292221283 453065764702160751438331925)
      ·
        refine ⟨21237457720413785223671809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 453065764702160751438331925 21237457720413785223671809)
        ·
          refine ⟨15928093290310338917753857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21237457720413785223671809 15928093290310338917753857)
          ·
            refine ⟨11946069967732754188315393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15928093290310338917753857 11946069967732754188315393)
            ·
              refine ⟨8959552475799565641236545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11946069967732754188315393 8959552475799565641236545)
              ·
                refine ⟨6719664356849674230927409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8959552475799565641236545 6719664356849674230927409)
                ·
                  refine ⟨5039748267637255673195557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6719664356849674230927409 5039748267637255673195557)
                  ·
                    refine ⟨944952800181985438724167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039748267637255673195557 944952800181985438724167)
                    ·
                      rfl

theorem cell23_5520867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 4].length) (baseStart_5520867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520867 prefixEnd_5520867 := by exact prefixLift 5520867
  have htrace : WordTrace (prefixWord ++ tailWord_5520867) baseStart_5520867 baseEnd_5520867 := by
    simpa [prefixWord, tailWord_5520867, baseEnd_5520867] using wordTrace_append hprefix tailTrace_5520867
  have hstable : (prefixWord ++ tailWord_5520867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520867).length < 2 ^ (prefixWord ++ tailWord_5520867).sum := by decide
  have hdescent : baseEnd_5520867 < baseStart_5520867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520890 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_5520890 : Nat := 118140960795 + 5520890 * 2 ^ 59
def prefixEnd_5520890 : Nat := 4983230072969 + 3 ^ 40 * 5520890 * 2
def baseEnd_5520890 : Nat := 2834870210601009726184895

theorem tailTrace_5520890 : CollatzResearch.WordTrace tailWord_5520890 prefixEnd_5520890 2834870210601009726184895 := by
  unfold tailWord_5520890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50340850242191474447392031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134242267312510598526378749 50340850242191474447392031)
  ·
    refine ⟨75511275363287211671088047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50340850242191474447392031 75511275363287211671088047)
    ·
      refine ⟨113266913044930817506632071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75511275363287211671088047 113266913044930817506632071)
      ·
        refine ⟨169900369567396226259948107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113266913044930817506632071 169900369567396226259948107)
        ·
          refine ⟨254850554351094339389922161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169900369567396226259948107 254850554351094339389922161)
          ·
            refine ⟨191137915763320754542441621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254850554351094339389922161 191137915763320754542441621)
            ·
              refine ⟨8959589801405660369176951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191137915763320754542441621 8959589801405660369176951)
              ·
                refine ⟨13439384702108490553765427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959589801405660369176951 13439384702108490553765427)
                ·
                  refine ⟨20159077053162735830648141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13439384702108490553765427 20159077053162735830648141)
                  ·
                    refine ⟨7559653894936025936493053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20159077053162735830648141 7559653894936025936493053)
                    ·
                      refine ⟨2834870210601009726184895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7559653894936025936493053 2834870210601009726184895)
                      ·
                        rfl

theorem cell23_5520890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_5520890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520890 prefixEnd_5520890 := by exact prefixLift 5520890
  have htrace : WordTrace (prefixWord ++ tailWord_5520890) baseStart_5520890 baseEnd_5520890 := by
    simpa [prefixWord, tailWord_5520890, baseEnd_5520890] using wordTrace_append hprefix tailTrace_5520890
  have hstable : (prefixWord ++ tailWord_5520890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520890).length < 2 ^ (prefixWord ++ tailWord_5520890).sum := by decide
  have hdescent : baseEnd_5520890 < baseStart_5520890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520933 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_5520933 : Nat := 118140960795 + 5520933 * 2 ^ 59
def prefixEnd_5520933 : Nat := 4983230072969 + 3 ^ 40 * 5520933 * 2
def baseEnd_5520933 : Nat := 2834892290269153057947197

theorem tailTrace_5520933 : CollatzResearch.WordTrace tailWord_5520933 prefixEnd_5520933 2834892290269153057947197 := by
  unfold tailWord_5520933
  simp only [CollatzResearch.WordTrace]
  refine ⟨201364969307610116133383453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134243312871740077422255635 201364969307610116133383453)
  ·
    refine ⟨75511863490353793550018795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201364969307610116133383453 75511863490353793550018795)
    ·
      refine ⟨113267795235530690325028193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75511863490353793550018795 113267795235530690325028193)
      ·
        refine ⟨84950846426648017743771145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113267795235530690325028193 84950846426648017743771145)
        ·
          refine ⟨63713134819986013307828359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84950846426648017743771145 63713134819986013307828359)
          ·
            refine ⟨95569702229979019961742539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63713134819986013307828359 95569702229979019961742539)
            ·
              refine ⟨143354553344968529942613809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95569702229979019961742539 143354553344968529942613809)
              ·
                refine ⟨107515915008726397456960357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143354553344968529942613809 107515915008726397456960357)
                ·
                  refine ⟨20159234064136199523180067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107515915008726397456960357 20159234064136199523180067)
                  ·
                    refine ⟨30238851096204299284770101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20159234064136199523180067 30238851096204299284770101)
                    ·
                      refine ⟨2834892290269153057947197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30238851096204299284770101 2834892290269153057947197)
                      ·
                        rfl

theorem cell23_5520933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_5520933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520933 prefixEnd_5520933 := by exact prefixLift 5520933
  have htrace : WordTrace (prefixWord ++ tailWord_5520933) baseStart_5520933 baseEnd_5520933 := by
    simpa [prefixWord, tailWord_5520933, baseEnd_5520933] using wordTrace_append hprefix tailTrace_5520933
  have hstable : (prefixWord ++ tailWord_5520933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520933).length < 2 ^ (prefixWord ++ tailWord_5520933).sum := by decide
  have hdescent : baseEnd_5520933 < baseStart_5520933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5520947 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 4, 2]
def baseStart_5520947 : Nat := 118140960795 + 5520947 * 2 ^ 59
def prefixEnd_5520947 : Nat := 4983230072969 + 3 ^ 40 * 5520947 * 2
def baseEnd_5520947 : Nat := 2834899478998316003172133

theorem tailTrace_5520947 : CollatzResearch.WordTrace tailWord_5520947 prefixEnd_5520947 2834899478998316003172133 := by
  unfold tailWord_5520947
  simp only [CollatzResearch.WordTrace]
  refine ⟨201365479929559396524393095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134243653286372931016262063 201365479929559396524393095)
  ·
    refine ⟨302048219894339094786589643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201365479929559396524393095 302048219894339094786589643)
    ·
      refine ⟨453072329841508642179884465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302048219894339094786589643 453072329841508642179884465)
      ·
        refine ⟨339804247381131481634913349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453072329841508642179884465 339804247381131481634913349)
        ·
          refine ⟨63713296383962152806546253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339804247381131481634913349 63713296383962152806546253)
          ·
            refine ⟨23892486143985807302454845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63713296383962152806546253 23892486143985807302454845)
            ·
              refine ⟨8959682303994677738420567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23892486143985807302454845 8959682303994677738420567)
              ·
                refine ⟨13439523455992016607630851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8959682303994677738420567 13439523455992016607630851)
                ·
                  refine ⟨20159285183988024911446277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13439523455992016607630851 20159285183988024911446277)
                  ·
                    refine ⟨3779865971997754670896177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20159285183988024911446277 3779865971997754670896177)
                    ·
                      refine ⟨2834899478998316003172133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779865971997754670896177 2834899478998316003172133)
                      ·
                        rfl

theorem cell23_5520947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4, 2].length) (baseStart_5520947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5520947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5520947 prefixEnd_5520947 := by exact prefixLift 5520947
  have htrace : WordTrace (prefixWord ++ tailWord_5520947) baseStart_5520947 baseEnd_5520947 := by
    simpa [prefixWord, tailWord_5520947, baseEnd_5520947] using wordTrace_append hprefix tailTrace_5520947
  have hstable : (prefixWord ++ tailWord_5520947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5520947).length < 2 ^ (prefixWord ++ tailWord_5520947).sum := by decide
  have hdescent : baseEnd_5520947 < baseStart_5520947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5520947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521054 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5521054 : Nat := 118140960795 + 5521054 * 2 ^ 59
def prefixEnd_5521054 : Nat := 4983230072969 + 3 ^ 40 * 5521054 * 2
def baseEnd_5521054 : Nat := 2834954421428347084534141

theorem tailTrace_5521054 : CollatzResearch.WordTrace tailWord_5521054 prefixEnd_5521054 2834954421428347084534141 := by
  unfold tailWord_5521054
  simp only [CollatzResearch.WordTrace]
  refine ⟨25171172817521469224817277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134246255026781169199025477 25171172817521469224817277)
  ·
    refine ⟨9439189806570550959306479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25171172817521469224817277 9439189806570550959306479)
    ·
      refine ⟨14158784709855826438959719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439189806570550959306479 14158784709855826438959719)
      ·
        refine ⟨21238177064783739658439579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14158784709855826438959719 21238177064783739658439579)
        ·
          refine ⟨31857265597175609487659369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21238177064783739658439579 31857265597175609487659369)
          ·
            refine ⟨23892949197881707115744527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31857265597175609487659369 23892949197881707115744527)
            ·
              refine ⟨35839423796822560673616791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23892949197881707115744527 35839423796822560673616791)
              ·
                refine ⟨53759135695233841010425187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35839423796822560673616791 53759135695233841010425187)
                ·
                  refine ⟨80638703542850761515637781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53759135695233841010425187 80638703542850761515637781)
                  ·
                    refine ⟨3779939228571129446045521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80638703542850761515637781 3779939228571129446045521)
                    ·
                      refine ⟨2834954421428347084534141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3779939228571129446045521 2834954421428347084534141)
                      ·
                        rfl

theorem cell23_5521054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5521054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521054 prefixEnd_5521054 := by exact prefixLift 5521054
  have htrace : WordTrace (prefixWord ++ tailWord_5521054) baseStart_5521054 baseEnd_5521054 := by
    simpa [prefixWord, tailWord_5521054, baseEnd_5521054] using wordTrace_append hprefix tailTrace_5521054
  have hstable : (prefixWord ++ tailWord_5521054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521054).length < 2 ^ (prefixWord ++ tailWord_5521054).sum := by decide
  have hdescent : baseEnd_5521054 < baseStart_5521054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521087 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_5521087 : Nat := 118140960795 + 5521087 * 2 ^ 59
def prefixEnd_5521087 : Nat := 4983230072969 + 3 ^ 40 * 5521087 * 2
def baseEnd_5521087 : Nat := 2834971366289945455421489

theorem tailTrace_5521087 : CollatzResearch.WordTrace tailWord_5521087 prefixEnd_5521087 2834971366289945455421489 := by
  unfold tailWord_5521087
  simp only [CollatzResearch.WordTrace]
  refine ⟨201370586149052200434489515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134247057432701466956326343 201370586149052200434489515)
  ·
    refine ⟨302055879223578300651734273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201370586149052200434489515 302055879223578300651734273)
    ·
      refine ⟨226541909417683725488800705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302055879223578300651734273 226541909417683725488800705)
      ·
        refine ⟨169906432063262794116600529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226541909417683725488800705 169906432063262794116600529)
        ·
          refine ⟨127429824047447095587450397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169906432063262794116600529 127429824047447095587450397)
          ·
            refine ⟨47786184017792660845293899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127429824047447095587450397 47786184017792660845293899)
            ·
              refine ⟨71679276026688991267940849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47786184017792660845293899 71679276026688991267940849)
              ·
                refine ⟨53759457020016743450955637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71679276026688991267940849 53759457020016743450955637)
                ·
                  refine ⟨5039949095626569698527091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53759457020016743450955637 5039949095626569698527091)
                  ·
                    refine ⟨7559923643439854547790637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5039949095626569698527091 7559923643439854547790637)
                    ·
                      refine ⟨2834971366289945455421489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7559923643439854547790637 2834971366289945455421489)
                      ·
                        rfl

theorem cell23_5521087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_5521087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521087 prefixEnd_5521087 := by exact prefixLift 5521087
  have htrace : WordTrace (prefixWord ++ tailWord_5521087) baseStart_5521087 baseEnd_5521087 := by
    simpa [prefixWord, tailWord_5521087, baseEnd_5521087] using wordTrace_append hprefix tailTrace_5521087
  have hstable : (prefixWord ++ tailWord_5521087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521087).length < 2 ^ (prefixWord ++ tailWord_5521087).sum := by decide
  have hdescent : baseEnd_5521087 < baseStart_5521087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521137 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 4, 4]
def baseStart_5521137 : Nat := 118140960795 + 5521137 * 2 ^ 59
def prefixEnd_5521137 : Nat := 4983230072969 + 3 ^ 40 * 5521137 * 2
def baseEnd_5521137 : Nat := 944999013440890086598753

theorem tailTrace_5521137 : CollatzResearch.WordTrace tailWord_5521137 prefixEnd_5521137 944999013440890086598753 := by
  unfold tailWord_5521137
  simp only [CollatzResearch.WordTrace]
  refine ⟨201372409798871058973809665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134248273199247372649206443 201372409798871058973809665)
  ·
    refine ⟨151029307349153294230357249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201372409798871058973809665 151029307349153294230357249)
    ·
      refine ⟨113271980511864970672767937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151029307349153294230357249 113271980511864970672767937)
      ·
        refine ⟨84953985383898728004575953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113271980511864970672767937 84953985383898728004575953)
        ·
          refine ⟨63715489037924046003431965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84953985383898728004575953 63715489037924046003431965)
          ·
            refine ⟨23893308389221517251286987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63715489037924046003431965 23893308389221517251286987)
            ·
              refine ⟨35839962583832275876930481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23893308389221517251286987 35839962583832275876930481)
              ·
                refine ⟨26879971937874206907697861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35839962583832275876930481 26879971937874206907697861)
                ·
                  refine ⟨5039994738351413795193349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26879971937874206907697861 5039994738351413795193349)
                  ·
                    refine ⟨944999013440890086598753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5039994738351413795193349 944999013440890086598753)
                    ·
                      rfl

theorem cell23_5521137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_5521137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521137 prefixEnd_5521137 := by exact prefixLift 5521137
  have htrace : WordTrace (prefixWord ++ tailWord_5521137) baseStart_5521137 baseEnd_5521137 := by
    simpa [prefixWord, tailWord_5521137, baseEnd_5521137] using wordTrace_append hprefix tailTrace_5521137
  have hstable : (prefixWord ++ tailWord_5521137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521137).length < 2 ^ (prefixWord ++ tailWord_5521137).sum := by decide
  have hdescent : baseEnd_5521137 < baseStart_5521137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521154 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_5521154 : Nat := 118140960795 + 5521154 * 2 ^ 59
def prefixEnd_5521154 : Nat := 4983230072969 + 3 ^ 40 * 5521154 * 2
def baseEnd_5521154 : Nat := 945001923164598897761227

theorem tailTrace_5521154 : CollatzResearch.WordTrace tailWord_5521154 prefixEnd_5521154 945001923164598897761227 := by
  unfold tailWord_5521154
  simp only [CollatzResearch.WordTrace]
  refine ⟨50343257459952367719294629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134248686559872980584785677 50343257459952367719294629)
  ·
    refine ⟨9439360773741068947367743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50343257459952367719294629 9439360773741068947367743)
    ·
      refine ⟨14159041160611603421051615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439360773741068947367743 14159041160611603421051615)
      ·
        refine ⟨21238561740917405131577423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159041160611603421051615 21238561740917405131577423)
        ·
          refine ⟨31857842611376107697366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21238561740917405131577423 31857842611376107697366135)
          ·
            refine ⟨47786763917064161546049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31857842611376107697366135 47786763917064161546049203)
            ·
              refine ⟨71680145875596242319073805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47786763917064161546049203 71680145875596242319073805)
              ·
                refine ⟨26880054703348590869652677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71680145875596242319073805 26880054703348590869652677)
                ·
                  refine ⟨5040010256877860788059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26880054703348590869652677 5040010256877860788059877)
                  ·
                    refine ⟨945001923164598897761227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040010256877860788059877 945001923164598897761227)
                    ·
                      rfl

theorem cell23_5521154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_5521154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521154 prefixEnd_5521154 := by exact prefixLift 5521154
  have htrace : WordTrace (prefixWord ++ tailWord_5521154) baseStart_5521154 baseEnd_5521154 := by
    simpa [prefixWord, tailWord_5521154, baseEnd_5521154] using wordTrace_append hprefix tailTrace_5521154
  have hstable : (prefixWord ++ tailWord_5521154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521154).length < 2 ^ (prefixWord ++ tailWord_5521154).sum := by decide
  have hdescent : baseEnd_5521154 < baseStart_5521154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521198 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5521198 : Nat := 118140960795 + 5521198 * 2 ^ 59
def prefixEnd_5521198 : Nat := 4983230072969 + 3 ^ 40 * 5521198 * 2
def baseEnd_5521198 : Nat := 2835028362642594521133479

theorem tailTrace_5521198 : CollatzResearch.WordTrace tailWord_5521198 prefixEnd_5521198 2835028362642594521133479 := by
  unfold tailWord_5521198
  simp only [CollatzResearch.WordTrace]
  refine ⟨25171829331456258298972531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134249756434433377594520165 25171829331456258298972531)
  ·
    refine ⟨37757743997184387448458797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25171829331456258298972531 37757743997184387448458797)
    ·
      refine ⟨14159153998944145293172049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37757743997184387448458797 14159153998944145293172049)
      ·
        refine ⟨10619365499208108969879037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14159153998944145293172049 10619365499208108969879037)
        ·
          refine ⟨3982262062203040863704639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10619365499208108969879037 3982262062203040863704639)
          ·
            refine ⟨5973393093304561295556959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982262062203040863704639 5973393093304561295556959)
            ·
              refine ⟨8960089639956841943335439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973393093304561295556959 8960089639956841943335439)
              ·
                refine ⟨13440134459935262915003159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960089639956841943335439 13440134459935262915003159)
                ·
                  refine ⟨20160201689902894372504739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13440134459935262915003159 20160201689902894372504739)
                  ·
                    refine ⟨30240302534854341558757109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20160201689902894372504739 30240302534854341558757109)
                    ·
                      refine ⟨2835028362642594521133479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30240302534854341558757109 2835028362642594521133479)
                      ·
                        rfl

theorem cell23_5521198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5521198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521198 prefixEnd_5521198 := by exact prefixLift 5521198
  have htrace : WordTrace (prefixWord ++ tailWord_5521198) baseStart_5521198 baseEnd_5521198 := by
    simpa [prefixWord, tailWord_5521198, baseEnd_5521198] using wordTrace_append hprefix tailTrace_5521198
  have hstable : (prefixWord ++ tailWord_5521198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521198).length < 2 ^ (prefixWord ++ tailWord_5521198).sum := by decide
  have hdescent : baseEnd_5521198 < baseStart_5521198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521274 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_5521274 : Nat := 118140960795 + 5521274 * 2 ^ 59
def prefixEnd_5521274 : Nat := 4983230072969 + 3 ^ 40 * 5521274 * 2
def baseEnd_5521274 : Nat := 315007487463592913753681

theorem tailTrace_5521274 : CollatzResearch.WordTrace tailWord_5521274 prefixEnd_5521274 315007487463592913753681 := by
  unfold tailWord_5521274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50344351649843682842886719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134251604399583154247697917 50344351649843682842886719)
  ·
    refine ⟨75516527474765524264330079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50344351649843682842886719 75516527474765524264330079)
    ·
      refine ⟨113274791212148286396495119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75516527474765524264330079 113274791212148286396495119)
      ·
        refine ⟨169912186818222429594742679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113274791212148286396495119 169912186818222429594742679)
        ·
          refine ⟨254868280227333644392114019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169912186818222429594742679 254868280227333644392114019)
          ·
            refine ⟨382302420341000466588171029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254868280227333644392114019 382302420341000466588171029)
            ·
              refine ⟨17920425953484396871320517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 382302420341000466588171029 17920425953484396871320517)
              ·
                refine ⟨3360079866278324413372597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17920425953484396871320517 3360079866278324413372597)
                ·
                  refine ⟨315007487463592913753681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360079866278324413372597 315007487463592913753681)
                  ·
                    rfl

theorem cell23_5521274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_5521274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521274 prefixEnd_5521274 := by exact prefixLift 5521274
  have htrace : WordTrace (prefixWord ++ tailWord_5521274) baseStart_5521274 baseEnd_5521274 := by
    simpa [prefixWord, tailWord_5521274, baseEnd_5521274] using wordTrace_append hprefix tailTrace_5521274
  have hstable : (prefixWord ++ tailWord_5521274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521274).length < 2 ^ (prefixWord ++ tailWord_5521274).sum := by decide
  have hdescent : baseEnd_5521274 < baseStart_5521274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521284 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5521284 : Nat := 118140960795 + 5521284 * 2 ^ 59
def prefixEnd_5521284 : Nat := 4983230072969 + 3 ^ 40 * 5521284 * 2
def baseEnd_5521284 : Nat := 2835072521978881184658083

theorem tailTrace_5521284 : CollatzResearch.WordTrace tailWord_5521284 prefixEnd_5521284 2835072521978881184658083 := by
  unfold tailWord_5521284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100688885664669251539705453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134251847552892335386273937 100688885664669251539705453)
  ·
    refine ⟨37758332124250969327389545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100688885664669251539705453 37758332124250969327389545)
    ·
      refine ⟨28318749093188226995542159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37758332124250969327389545 28318749093188226995542159)
      ·
        refine ⟨42478123639782340493313239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28318749093188226995542159 42478123639782340493313239)
        ·
          refine ⟨63717185459673510739969859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42478123639782340493313239 63717185459673510739969859)
          ·
            refine ⟨95575778189510266109954789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63717185459673510739969859 95575778189510266109954789)
            ·
              refine ⟨17920458410533174895616523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95575778189510266109954789 17920458410533174895616523)
              ·
                refine ⟨26880687615799762343424785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17920458410533174895616523 26880687615799762343424785)
                ·
                  refine ⟨20160515711849821757568589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26880687615799762343424785 20160515711849821757568589)
                  ·
                    refine ⟨7560193391943683159088221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20160515711849821757568589 7560193391943683159088221)
                    ·
                      refine ⟨2835072521978881184658083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560193391943683159088221 2835072521978881184658083)
                      ·
                        rfl

theorem cell23_5521284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5521284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521284 prefixEnd_5521284 := by exact prefixLift 5521284
  have htrace : WordTrace (prefixWord ++ tailWord_5521284) baseStart_5521284 baseEnd_5521284 := by
    simpa [prefixWord, tailWord_5521284, baseEnd_5521284] using wordTrace_append hprefix tailTrace_5521284
  have hstable : (prefixWord ++ tailWord_5521284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521284).length < 2 ^ (prefixWord ++ tailWord_5521284).sum := by decide
  have hdescent : baseEnd_5521284 < baseStart_5521284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521308 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 5]
def baseStart_5521308 : Nat := 118140960795 + 5521308 * 2 ^ 59
def prefixEnd_5521308 : Nat := 4983230072969 + 3 ^ 40 * 5521308 * 2
def baseEnd_5521308 : Nat := 315009427279398787861997

theorem tailTrace_5521308 : CollatzResearch.WordTrace tailWord_5521308 prefixEnd_5521308 315009427279398787861997 := by
  unfold tailWord_5521308
  simp only [CollatzResearch.WordTrace]
  refine ⟨100689323340625777589142289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134252431120834370118856385 100689323340625777589142289)
  ·
    refine ⟨75516992505469333191856717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100689323340625777589142289 75516992505469333191856717)
    ·
      refine ⟨28318872189550999946946269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75516992505469333191856717 28318872189550999946946269)
      ·
        refine ⟨10619577071081624980104851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28318872189550999946946269 10619577071081624980104851)
        ·
          refine ⟨15929365606622437470157277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619577071081624980104851 15929365606622437470157277)
          ·
            refine ⟨5973512102483414051308979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15929365606622437470157277 5973512102483414051308979)
            ·
              refine ⟨8960268153725121076963469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973512102483414051308979 8960268153725121076963469)
              ·
                refine ⟨3360100557646920403861301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8960268153725121076963469 3360100557646920403861301)
                ·
                  refine ⟨315009427279398787861997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360100557646920403861301 315009427279398787861997)
                  ·
                    rfl

theorem cell23_5521308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_5521308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521308 prefixEnd_5521308 := by exact prefixLift 5521308
  have htrace : WordTrace (prefixWord ++ tailWord_5521308) baseStart_5521308 baseEnd_5521308 := by
    simpa [prefixWord, tailWord_5521308, baseEnd_5521308] using wordTrace_append hprefix tailTrace_5521308
  have hstable : (prefixWord ++ tailWord_5521308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521308).length < 2 ^ (prefixWord ++ tailWord_5521308).sum := by decide
  have hdescent : baseEnd_5521308 < baseStart_5521308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521344 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_5521344 : Nat := 118140960795 + 5521344 * 2 ^ 59
def prefixEnd_5521344 : Nat := 4983230072969 + 3 ^ 40 * 5521344 * 2
def baseEnd_5521344 : Nat := 2835103330818150949907807

theorem tailTrace_5521344 : CollatzResearch.WordTrace tailWord_5521344 prefixEnd_5521344 2835103330818150949907807 := by
  unfold tailWord_5521344
  simp only [CollatzResearch.WordTrace]
  refine ⟨100689979854560566663297543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134253306472747422217730057 100689979854560566663297543)
  ·
    refine ⟨151034969781840849994946315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100689979854560566663297543 151034969781840849994946315)
    ·
      refine ⟨226552454672761274992419473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151034969781840849994946315 226552454672761274992419473)
      ·
        refine ⟨169914341004570956244314605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226552454672761274992419473 169914341004570956244314605)
        ·
          refine ⟨63717877876714108591617977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169914341004570956244314605 63717877876714108591617977)
          ·
            refine ⟨47788408407535581443713483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63717877876714108591617977 47788408407535581443713483)
            ·
              refine ⟨71682612611303372165570225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47788408407535581443713483 71682612611303372165570225)
              ·
                refine ⟨53761959458477529124177669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71682612611303372165570225 53761959458477529124177669)
                ·
                  refine ⟨10080367398464536710783313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53761959458477529124177669 10080367398464536710783313)
                  ·
                    refine ⟨7560275548848402533087485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10080367398464536710783313 7560275548848402533087485)
                    ·
                      refine ⟨2835103330818150949907807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560275548848402533087485 2835103330818150949907807)
                      ·
                        rfl

theorem cell23_5521344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_5521344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521344 prefixEnd_5521344 := by exact prefixLift 5521344
  have htrace : WordTrace (prefixWord ++ tailWord_5521344) baseStart_5521344 baseEnd_5521344 := by
    simpa [prefixWord, tailWord_5521344, baseEnd_5521344] using wordTrace_append hprefix tailTrace_5521344
  have hstable : (prefixWord ++ tailWord_5521344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521344).length < 2 ^ (prefixWord ++ tailWord_5521344).sum := by decide
  have hdescent : baseEnd_5521344 < baseStart_5521344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521387 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_5521387 : Nat := 118140960795 + 5521387 * 2 ^ 59
def prefixEnd_5521387 : Nat := 4983230072969 + 3 ^ 40 * 5521387 * 2
def baseEnd_5521387 : Nat := 2835125410486294281670109

theorem tailTrace_5521387 : CollatzResearch.WordTrace tailWord_5521387 prefixEnd_5521387 2835125410486294281670109 := by
  unfold tailWord_5521387
  simp only [CollatzResearch.WordTrace]
  refine ⟨201381528047965351670410415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134254352031976901113606943 201381528047965351670410415)
  ·
    refine ⟨302072292071948027505615623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201381528047965351670410415 302072292071948027505615623)
    ·
      refine ⟨453108438107922041258423435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302072292071948027505615623 453108438107922041258423435)
      ·
        refine ⟨679662657161883061887635153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453108438107922041258423435 679662657161883061887635153)
        ·
          refine ⟨509746992871412296415726365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679662657161883061887635153 509746992871412296415726365)
          ·
            refine ⟨191155122326779611155897387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509746992871412296415726365 191155122326779611155897387)
            ·
              refine ⟨286732683490169416733846081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191155122326779611155897387 286732683490169416733846081)
              ·
                refine ⟨215049512617627062550384561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286732683490169416733846081 215049512617627062550384561)
                ·
                  refine ⟨161287134463220296912788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215049512617627062550384561 161287134463220296912788421)
                  ·
                    refine ⟨30241337711853805671147829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161287134463220296912788421 30241337711853805671147829)
                    ·
                      refine ⟨2835125410486294281670109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30241337711853805671147829 2835125410486294281670109)
                      ·
                        rfl

theorem cell23_5521387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_5521387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521387 prefixEnd_5521387 := by exact prefixLift 5521387
  have htrace : WordTrace (prefixWord ++ tailWord_5521387) baseStart_5521387 baseEnd_5521387 := by
    simpa [prefixWord, tailWord_5521387, baseEnd_5521387] using wordTrace_append hprefix tailTrace_5521387
  have hstable : (prefixWord ++ tailWord_5521387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521387).length < 2 ^ (prefixWord ++ tailWord_5521387).sum := by decide
  have hdescent : baseEnd_5521387 < baseStart_5521387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521391 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_5521391 : Nat := 118140960795 + 5521391 * 2 ^ 59
def prefixEnd_5521391 : Nat := 4983230072969 + 3 ^ 40 * 5521391 * 2
def baseEnd_5521391 : Nat := 2835127464408912266020091

theorem tailTrace_5521391 : CollatzResearch.WordTrace tailWord_5521391 prefixEnd_5521391 2835127464408912266020091 := by
  unfold tailWord_5521391
  simp only [CollatzResearch.WordTrace]
  refine ⟨201381673939950860353556027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134254449293300573569037351 201381673939950860353556027)
  ·
    refine ⟨302072510909926290530334041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201381673939950860353556027 302072510909926290530334041)
    ·
      refine ⟨226554383182444717897750531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302072510909926290530334041 226554383182444717897750531)
      ·
        refine ⟨339831574773667076846625797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226554383182444717897750531 339831574773667076846625797)
        ·
          refine ⟨63718420270062576908742337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339831574773667076846625797 63718420270062576908742337)
          ·
            refine ⟨47788815202546932681556753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63718420270062576908742337 47788815202546932681556753)
            ·
              refine ⟨35841611401910199511167565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47788815202546932681556753 35841611401910199511167565)
              ·
                refine ⟨13440604275716324816687837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35841611401910199511167565 13440604275716324816687837)
                ·
                  refine ⟨5040226603393621806257939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13440604275716324816687837 5040226603393621806257939)
                  ·
                    refine ⟨7560339905090432709386909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5040226603393621806257939 7560339905090432709386909)
                    ·
                      refine ⟨2835127464408912266020091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560339905090432709386909 2835127464408912266020091)
                      ·
                        rfl

theorem cell23_5521391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_5521391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521391 prefixEnd_5521391 := by exact prefixLift 5521391
  have htrace : WordTrace (prefixWord ++ tailWord_5521391) baseStart_5521391 baseEnd_5521391 := by
    simpa [prefixWord, tailWord_5521391, baseEnd_5521391] using wordTrace_append hprefix tailTrace_5521391
  have hstable : (prefixWord ++ tailWord_5521391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521391).length < 2 ^ (prefixWord ++ tailWord_5521391).sum := by decide
  have hdescent : baseEnd_5521391 < baseStart_5521391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521412 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5521412 : Nat := 118140960795 + 5521412 * 2 ^ 59
def prefixEnd_5521412 : Nat := 4983230072969 + 3 ^ 40 * 5521412 * 2
def baseEnd_5521412 : Nat := 2835138247502656683857495

theorem tailTrace_5521412 : CollatzResearch.WordTrace tailWord_5521412 prefixEnd_5521412 2835138247502656683857495 := by
  unfold tailWord_5521412
  simp only [CollatzResearch.WordTrace]
  refine ⟨100691219936437390470035245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134254959915249853960046993 100691219936437390470035245)
  ·
    refine ⟨37759207476164021426263217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100691219936437390470035245 37759207476164021426263217)
    ·
      refine ⟨28319405607123016069697413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37759207476164021426263217 28319405607123016069697413)
      ·
        refine ⟨5309888551335565513068265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28319405607123016069697413 5309888551335565513068265)
        ·
          refine ⟨3982416413501674134801199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309888551335565513068265 3982416413501674134801199)
          ·
            refine ⟨5973624620252511202201799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3982416413501674134801199 5973624620252511202201799)
            ·
              refine ⟨8960436930378766803302699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973624620252511202201799 8960436930378766803302699)
              ·
                refine ⟨13440655395568150204954049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960436930378766803302699 13440655395568150204954049)
                ·
                  refine ⟨10080491546676112653715537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13440655395568150204954049 10080491546676112653715537)
                  ·
                    refine ⟨7560368660007084490286653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10080491546676112653715537 7560368660007084490286653)
                    ·
                      refine ⟨2835138247502656683857495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560368660007084490286653 2835138247502656683857495)
                      ·
                        rfl

theorem cell23_5521412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5521412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521412 prefixEnd_5521412 := by exact prefixLift 5521412
  have htrace : WordTrace (prefixWord ++ tailWord_5521412) baseStart_5521412 baseEnd_5521412 := by
    simpa [prefixWord, tailWord_5521412, baseEnd_5521412] using wordTrace_append hprefix tailTrace_5521412
  have hstable : (prefixWord ++ tailWord_5521412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521412).length < 2 ^ (prefixWord ++ tailWord_5521412).sum := by decide
  have hdescent : baseEnd_5521412 < baseStart_5521412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521418 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_5521418 : Nat := 118140960795 + 5521418 * 2 ^ 59
def prefixEnd_5521418 : Nat := 4983230072969 + 3 ^ 40 * 5521418 * 2
def baseEnd_5521418 : Nat := 2835141328386583660382467

theorem tailTrace_5521418 : CollatzResearch.WordTrace tailWord_5521418 prefixEnd_5521418 2835141328386583660382467 := by
  unfold tailWord_5521418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50345664677713260991197227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134255105807235362643192605 50345664677713260991197227)
  ·
    refine ⟨75518497016569891486795841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50345664677713260991197227 75518497016569891486795841)
    ·
      refine ⟨56638872762427418615096881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75518497016569891486795841 56638872762427418615096881)
      ·
        refine ⟨42479154571820563961322661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56638872762427418615096881 42479154571820563961322661)
        ·
          refine ⟨7964841482216355742747999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42479154571820563961322661 7964841482216355742747999)
          ·
            refine ⟨11947262223324533614121999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7964841482216355742747999 11947262223324533614121999)
            ·
              refine ⟨17920893334986800421182999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11947262223324533614121999 17920893334986800421182999)
              ·
                refine ⟨26881340002480200631774499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17920893334986800421182999 26881340002480200631774499)
                ·
                  refine ⟨40322010003720300947661749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26881340002480200631774499 40322010003720300947661749)
                  ·
                    refine ⟨3780188437848778213843289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40322010003720300947661749 3780188437848778213843289)
                    ·
                      refine ⟨2835141328386583660382467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780188437848778213843289 2835141328386583660382467)
                      ·
                        rfl

theorem cell23_5521418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_5521418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521418 prefixEnd_5521418 := by exact prefixLift 5521418
  have htrace : WordTrace (prefixWord ++ tailWord_5521418) baseStart_5521418 baseEnd_5521418 := by
    simpa [prefixWord, tailWord_5521418, baseEnd_5521418] using wordTrace_append hprefix tailTrace_5521418
  have hstable : (prefixWord ++ tailWord_5521418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521418).length < 2 ^ (prefixWord ++ tailWord_5521418).sum := by decide
  have hdescent : baseEnd_5521418 < baseStart_5521418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521424 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_5521424 : Nat := 118140960795 + 5521424 * 2 ^ 59
def prefixEnd_5521424 : Nat := 4983230072969 + 3 ^ 40 * 5521424 * 2
def baseEnd_5521424 : Nat := 945048136423503545635813

theorem tailTrace_5521424 : CollatzResearch.WordTrace tailWord_5521424 prefixEnd_5521424 945048136423503545635813 := by
  unfold tailWord_5521424
  simp only [CollatzResearch.WordTrace]
  refine ⟨100691438774415653494753663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134255251699220871326338217 100691438774415653494753663)
  ·
    refine ⟨151037158161623480242130495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100691438774415653494753663 151037158161623480242130495)
    ·
      refine ⟨226555737242435220363195743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151037158161623480242130495 226555737242435220363195743)
      ·
        refine ⟨339833605863652830544793615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226555737242435220363195743 339833605863652830544793615)
        ·
          refine ⟨509750408795479245817190423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339833605863652830544793615 509750408795479245817190423)
          ·
            refine ⟨764625613193218868725785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509750408795479245817190423 764625613193218868725785635)
            ·
              refine ⟨1146938419789828303088678453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764625613193218868725785635 1146938419789828303088678453)
              ·
                refine ⟨107525476855296403414563605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146938419789828303088678453 107525476855296403414563605)
                ·
                  refine ⟨5040256727592018910057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107525476855296403414563605 5040256727592018910057669)
                  ·
                    refine ⟨945048136423503545635813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040256727592018910057669 945048136423503545635813)
                    ·
                      rfl

theorem cell23_5521424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_5521424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521424 prefixEnd_5521424 := by exact prefixLift 5521424
  have htrace : WordTrace (prefixWord ++ tailWord_5521424) baseStart_5521424 baseEnd_5521424 := by
    simpa [prefixWord, tailWord_5521424, baseEnd_5521424] using wordTrace_append hprefix tailTrace_5521424
  have hstable : (prefixWord ++ tailWord_5521424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521424).length < 2 ^ (prefixWord ++ tailWord_5521424).sum := by decide
  have hdescent : baseEnd_5521424 < baseStart_5521424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521461 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5521461 : Nat := 118140960795 + 5521461 * 2 ^ 59
def prefixEnd_5521461 : Nat := 4983230072969 + 3 ^ 40 * 5521461 * 2
def baseEnd_5521461 : Nat := 2835163408054726992144769

theorem tailTrace_5521461 : CollatzResearch.WordTrace tailWord_5521461 prefixEnd_5521461 2835163408054726992144769 := by
  unfold tailWord_5521461
  simp only [CollatzResearch.WordTrace]
  refine ⟨201384227049697262308604237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134256151366464841539069491 201384227049697262308604237)
  ·
    refine ⟨75519085143636473365726589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201384227049697262308604237 75519085143636473365726589)
    ·
      refine ⟨28319656928863677512147471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75519085143636473365726589 28319656928863677512147471)
      ·
        refine ⟨42479485393295516268221207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28319656928863677512147471 42479485393295516268221207)
        ·
          refine ⟨63719228089943274402331811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42479485393295516268221207 63719228089943274402331811)
          ·
            refine ⟨95578842134914911603497717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63719228089943274402331811 95578842134914911603497717)
            ·
              refine ⟨8960516450148272962827911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95578842134914911603497717 8960516450148272962827911)
              ·
                refine ⟨13440774675222409444241867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960516450148272962827911 13440774675222409444241867)
                ·
                  refine ⟨20161162012833614166362801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13440774675222409444241867 20161162012833614166362801)
                  ·
                    refine ⟨15120871509625210624772101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20161162012833614166362801 15120871509625210624772101)
                    ·
                      refine ⟨2835163408054726992144769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15120871509625210624772101 2835163408054726992144769)
                      ·
                        rfl

theorem cell23_5521461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5521461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521461 prefixEnd_5521461 := by exact prefixLift 5521461
  have htrace : WordTrace (prefixWord ++ tailWord_5521461) baseStart_5521461 baseEnd_5521461 := by
    simpa [prefixWord, tailWord_5521461, baseEnd_5521461] using wordTrace_append hprefix tailTrace_5521461
  have hstable : (prefixWord ++ tailWord_5521461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521461).length < 2 ^ (prefixWord ++ tailWord_5521461).sum := by decide
  have hdescent : baseEnd_5521461 < baseStart_5521461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521468 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_5521468 : Nat := 118140960795 + 5521468 * 2 ^ 59
def prefixEnd_5521468 : Nat := 4983230072969 + 3 ^ 40 * 5521468 * 2
def baseEnd_5521468 : Nat := 2835167002419308464757237

theorem tailTrace_5521468 : CollatzResearch.WordTrace tailWord_5521468 prefixEnd_5521468 2835167002419308464757237 := by
  unfold tailWord_5521468
  simp only [CollatzResearch.WordTrace]
  refine ⟨100692241180335951252054529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134256321573781268336072705 100692241180335951252054529)
  ·
    refine ⟨75519180885251963439040897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100692241180335951252054529 75519180885251963439040897)
    ·
      refine ⟨56639385663938972579280673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75519180885251963439040897 56639385663938972579280673)
      ·
        refine ⟨42479539247954229434460505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56639385663938972579280673 42479539247954229434460505)
        ·
          refine ⟨31859654435965672075845379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42479539247954229434460505 31859654435965672075845379)
          ·
            refine ⟨47789481653948508113768069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31859654435965672075845379 47789481653948508113768069)
            ·
              refine ⟨8960527810115345271331513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47789481653948508113768069 8960527810115345271331513)
              ·
                refine ⟨6720395857586508953498635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8960527810115345271331513 6720395857586508953498635)
                ·
                  refine ⟨10080593786379763430247953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6720395857586508953498635 10080593786379763430247953)
                  ·
                    refine ⟨7560445339784822572685965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10080593786379763430247953 7560445339784822572685965)
                    ·
                      refine ⟨2835167002419308464757237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560445339784822572685965 2835167002419308464757237)
                      ·
                        rfl

theorem cell23_5521468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_5521468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521468 prefixEnd_5521468 := by exact prefixLift 5521468
  have htrace : WordTrace (prefixWord ++ tailWord_5521468) baseStart_5521468 baseEnd_5521468 := by
    simpa [prefixWord, tailWord_5521468, baseEnd_5521468] using wordTrace_append hprefix tailTrace_5521468
  have hstable : (prefixWord ++ tailWord_5521468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521468).length < 2 ^ (prefixWord ++ tailWord_5521468).sum := by decide
  have hdescent : baseEnd_5521468 < baseStart_5521468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521478 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5521478 : Nat := 118140960795 + 5521478 * 2 ^ 59
def prefixEnd_5521478 : Nat := 4983230072969 + 3 ^ 40 * 5521478 * 2
def baseEnd_5521478 : Nat := 2835172137225853425632191

theorem tailTrace_5521478 : CollatzResearch.WordTrace tailWord_5521478 prefixEnd_5521478 2835172137225853425632191 := by
  unfold tailWord_5521478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293276471582364819124159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134256564727090449474648725 6293276471582364819124159)
  ·
    refine ⟨9439914707373547228686239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6293276471582364819124159 9439914707373547228686239)
    ·
      refine ⟨14159872061060320843029359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9439914707373547228686239 14159872061060320843029359)
      ·
        refine ⟨21239808091590481264544039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159872061060320843029359 21239808091590481264544039)
        ·
          refine ⟨31859712137385721896816059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239808091590481264544039 31859712137385721896816059)
          ·
            refine ⟨47789568206078582845224089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31859712137385721896816059 47789568206078582845224089)
            ·
              refine ⟨35842176154558937133918067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47789568206078582845224089 35842176154558937133918067)
              ·
                refine ⟨53763264231838405700877101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35842176154558937133918067 53763264231838405700877101)
                ·
                  refine ⟨20161224086939402137828913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53763264231838405700877101 20161224086939402137828913)
                  ·
                    refine ⟨15120918065204551603371685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20161224086939402137828913 15120918065204551603371685)
                    ·
                      refine ⟨2835172137225853425632191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15120918065204551603371685 2835172137225853425632191)
                      ·
                        rfl

theorem cell23_5521478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5521478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521478 prefixEnd_5521478 := by exact prefixLift 5521478
  have htrace : WordTrace (prefixWord ++ tailWord_5521478) baseStart_5521478 baseEnd_5521478 := by
    simpa [prefixWord, tailWord_5521478, baseEnd_5521478] using wordTrace_append hprefix tailTrace_5521478
  have hstable : (prefixWord ++ tailWord_5521478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521478).length < 2 ^ (prefixWord ++ tailWord_5521478).sum := by decide
  have hdescent : baseEnd_5521478 < baseStart_5521478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521481 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_5521481 : Nat := 118140960795 + 5521481 * 2 ^ 59
def prefixEnd_5521481 : Nat := 4983230072969 + 3 ^ 40 * 5521481 * 2
def baseEnd_5521481 : Nat := 2835173677667816913894677

theorem tailTrace_5521481 : CollatzResearch.WordTrace tailWord_5521481 prefixEnd_5521481 2835173677667816913894677 := by
  unfold tailWord_5521481
  simp only [CollatzResearch.WordTrace]
  refine ⟨201384956509624805724332297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134256637673083203816221531 201384956509624805724332297)
  ·
    refine ⟨151038717382218604293249223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201384956509624805724332297 151038717382218604293249223)
    ·
      refine ⟨226558076073327906439873835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151038717382218604293249223 226558076073327906439873835)
      ·
        refine ⟨339837114109991859659810753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226558076073327906439873835 339837114109991859659810753)
        ·
          refine ⟨254877835582493894744858065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339837114109991859659810753 254877835582493894744858065)
          ·
            refine ⟨191158376686870421058643549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254877835582493894744858065 191158376686870421058643549)
            ·
              refine ⟨71684391257576407896991331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191158376686870421058643549 71684391257576407896991331)
              ·
                refine ⟨107526586886364611845486997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71684391257576407896991331 107526586886364611845486997)
                ·
                  refine ⟨5040308760298341180257203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107526586886364611845486997 5040308760298341180257203)
                  ·
                    refine ⟨7560463140447511770385805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5040308760298341180257203 7560463140447511770385805)
                    ·
                      refine ⟨2835173677667816913894677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560463140447511770385805 2835173677667816913894677)
                      ·
                        rfl

theorem cell23_5521481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_5521481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521481 prefixEnd_5521481 := by exact prefixLift 5521481
  have htrace : WordTrace (prefixWord ++ tailWord_5521481) baseStart_5521481 baseEnd_5521481 := by
    simpa [prefixWord, tailWord_5521481, baseEnd_5521481] using wordTrace_append hprefix tailTrace_5521481
  have hstable : (prefixWord ++ tailWord_5521481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521481).length < 2 ^ (prefixWord ++ tailWord_5521481).sum := by decide
  have hdescent : baseEnd_5521481 < baseStart_5521481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521498 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_5521498 : Nat := 118140960795 + 5521498 * 2 ^ 59
def prefixEnd_5521498 : Nat := 4983230072969 + 3 ^ 40 * 5521498 * 2
def baseEnd_5521498 : Nat := 2835182406838943347382099

theorem tailTrace_5521498 : CollatzResearch.WordTrace tailWord_5521498 prefixEnd_5521498 2835182406838943347382099 := by
  unfold tailWord_5521498
  simp only [CollatzResearch.WordTrace]
  refine ⟨50346394137640804406925287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134257051033708811751800765 50346394137640804406925287)
  ·
    refine ⟨75519591206461206610387931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50346394137640804406925287 75519591206461206610387931)
    ·
      refine ⟨113279386809691809915581897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75519591206461206610387931 113279386809691809915581897)
      ·
        refine ⟨84959540107268857436686423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113279386809691809915581897 84959540107268857436686423)
        ·
          refine ⟨127439310160903286155029635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84959540107268857436686423 127439310160903286155029635)
          ·
            refine ⟨191158965241354929232544453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127439310160903286155029635 191158965241354929232544453)
            ·
              refine ⟨35842305982754049231102085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191158965241354929232544453 35842305982754049231102085)
              ·
                refine ⟨6720432371766384230831641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35842305982754049231102085 6720432371766384230831641)
                ·
                  refine ⟨5040324278824788173123731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6720432371766384230831641 5040324278824788173123731)
                  ·
                    refine ⟨7560486418237182259685597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5040324278824788173123731 7560486418237182259685597)
                    ·
                      refine ⟨2835182406838943347382099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560486418237182259685597 2835182406838943347382099)
                      ·
                        rfl

theorem cell23_5521498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_5521498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521498 prefixEnd_5521498 := by exact prefixLift 5521498
  have htrace : WordTrace (prefixWord ++ tailWord_5521498) baseStart_5521498 baseEnd_5521498 := by
    simpa [prefixWord, tailWord_5521498, baseEnd_5521498] using wordTrace_append hprefix tailTrace_5521498
  have hstable : (prefixWord ++ tailWord_5521498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521498).length < 2 ^ (prefixWord ++ tailWord_5521498).sum := by decide
  have hdescent : baseEnd_5521498 < baseStart_5521498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521541 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_5521541 : Nat := 118140960795 + 5521541 * 2 ^ 59
def prefixEnd_5521541 : Nat := 4983230072969 + 3 ^ 40 * 5521541 * 2
def baseEnd_5521541 : Nat := 2835204486507086679144401

theorem tailTrace_5521541 : CollatzResearch.WordTrace tailWord_5521541 prefixEnd_5521541 2835204486507086679144401 := by
  unfold tailWord_5521541
  simp only [CollatzResearch.WordTrace]
  refine ⟨201387144889407435971516477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134258096592938290647677651 201387144889407435971516477)
  ·
    refine ⟨75520179333527788489318679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201387144889407435971516477 75520179333527788489318679)
    ·
      refine ⟨113280269000291682733978019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75520179333527788489318679 113280269000291682733978019)
      ·
        refine ⟨169920403500437524100967029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113280269000291682733978019 169920403500437524100967029)
        ·
          refine ⟨15930037828166017884465659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 169920403500437524100967029 15930037828166017884465659)
          ·
            refine ⟨23895056742249026826698489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15930037828166017884465659 23895056742249026826698489)
            ·
              refine ⟨17921292556686770120023867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23895056742249026826698489 17921292556686770120023867)
              ·
                refine ⟨26881938835030155180035801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17921292556686770120023867 26881938835030155180035801)
                ·
                  refine ⟨20161454126272616385026851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26881938835030155180035801 20161454126272616385026851)
                  ·
                    refine ⟨30242181189408924577540277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20161454126272616385026851 30242181189408924577540277)
                    ·
                      refine ⟨2835204486507086679144401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30242181189408924577540277 2835204486507086679144401)
                      ·
                        rfl

theorem cell23_5521541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_5521541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521541 prefixEnd_5521541 := by exact prefixLift 5521541
  have htrace : WordTrace (prefixWord ++ tailWord_5521541) baseStart_5521541 baseEnd_5521541 := by
    simpa [prefixWord, tailWord_5521541, baseEnd_5521541] using wordTrace_append hprefix tailTrace_5521541
  have hstable : (prefixWord ++ tailWord_5521541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521541).length < 2 ^ (prefixWord ++ tailWord_5521541).sum := by decide
  have hdescent : baseEnd_5521541 < baseStart_5521541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521591 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 1, 7]
def baseStart_5521591 : Nat := 118140960795 + 5521591 * 2 ^ 59
def prefixEnd_5521591 : Nat := 4983230072969 + 3 ^ 40 * 5521591 * 2
def baseEnd_5521591 : Nat := 945076720179937161173057

theorem tailTrace_5521591 : CollatzResearch.WordTrace tailWord_5521591 prefixEnd_5521591 945076720179937161173057 := by
  unfold tailWord_5521591
  simp only [CollatzResearch.WordTrace]
  refine ⟨201388968539226294510836627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134259312359484196340557751 201388968539226294510836627)
  ·
    refine ⟨302083452808839441766254941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201388968539226294510836627 302083452808839441766254941)
    ·
      refine ⟨113281294803314790662345603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302083452808839441766254941 113281294803314790662345603)
      ·
        refine ⟨169921942204972185993518405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113281294803314790662345603 169921942204972185993518405)
        ·
          refine ⟨31860364163432284873784701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169921942204972185993518405 31860364163432284873784701)
          ·
            refine ⟨11947636561287106827669263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31860364163432284873784701 11947636561287106827669263)
            ·
              refine ⟨17921454841930660241503895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11947636561287106827669263 17921454841930660241503895)
              ·
                refine ⟨26882182262895990362255843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17921454841930660241503895 26882182262895990362255843)
                ·
                  refine ⟨40323273394343985543383765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26882182262895990362255843 40323273394343985543383765)
                  ·
                    refine ⟨945076720179937161173057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40323273394343985543383765 945076720179937161173057)
                    ·
                      rfl

theorem cell23_5521591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_5521591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521591 prefixEnd_5521591 := by exact prefixLift 5521591
  have htrace : WordTrace (prefixWord ++ tailWord_5521591) baseStart_5521591 baseEnd_5521591 := by
    simpa [prefixWord, tailWord_5521591, baseEnd_5521591] using wordTrace_append hprefix tailTrace_5521591
  have hstable : (prefixWord ++ tailWord_5521591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521591).length < 2 ^ (prefixWord ++ tailWord_5521591).sum := by decide
  have hdescent : baseEnd_5521591 < baseStart_5521591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521611 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4]
def baseStart_5521611 : Nat := 118140960795 + 5521611 * 2 ^ 59
def prefixEnd_5521611 : Nat := 4983230072969 + 3 ^ 40 * 5521611 * 2
def baseEnd_5521611 : Nat := 2835240430152901405269079

theorem tailTrace_5521611 : CollatzResearch.WordTrace tailWord_5521611 prefixEnd_5521611 2835240430152901405269079 := by
  unfold tailWord_5521611
  simp only [CollatzResearch.WordTrace]
  refine ⟨201389697999153837926564687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134259798666102558617709791 201389697999153837926564687)
  ·
    refine ⟨302084546998730756889847031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201389697999153837926564687 302084546998730756889847031)
    ·
      refine ⟨453126820498096135334770547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302084546998730756889847031 453126820498096135334770547)
      ·
        refine ⟨679690230747144203002155821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453126820498096135334770547 679690230747144203002155821)
        ·
          refine ⟨254883836530179076125808433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679690230747144203002155821 254883836530179076125808433)
          ·
            refine ⟨191162877397634307094356325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254883836530179076125808433 191162877397634307094356325)
            ·
              refine ⟨35843039512056432580191811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191162877397634307094356325 35843039512056432580191811)
              ·
                refine ⟨53764559268084648870287717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35843039512056432580191811 53764559268084648870287717)
                ·
                  refine ⟨10080854862765871663178947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53764559268084648870287717 10080854862765871663178947)
                  ·
                    refine ⟨15121282294148807494768421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10080854862765871663178947 15121282294148807494768421)
                    ·
                      refine ⟨2835240430152901405269079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15121282294148807494768421 2835240430152901405269079)
                      ·
                        rfl

theorem cell23_5521611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_5521611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521611 prefixEnd_5521611 := by exact prefixLift 5521611
  have htrace : WordTrace (prefixWord ++ tailWord_5521611) baseStart_5521611 baseEnd_5521611 := by
    simpa [prefixWord, tailWord_5521611, baseEnd_5521611] using wordTrace_append hprefix tailTrace_5521611
  have hstable : (prefixWord ++ tailWord_5521611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521611).length < 2 ^ (prefixWord ++ tailWord_5521611).sum := by decide
  have hdescent : baseEnd_5521611 < baseStart_5521611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521711 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 3, 6]
def baseStart_5521711 : Nat := 118140960795 + 5521711 * 2 ^ 59
def prefixEnd_5521711 : Nat := 4983230072969 + 3 ^ 40 * 5521711 * 2
def baseEnd_5521711 : Nat := 945097259406117004672873

theorem tailTrace_5521711 : CollatzResearch.WordTrace tailWord_5521711 prefixEnd_5521711 945097259406117004672873 := by
  unfold tailWord_5521711
  simp only [CollatzResearch.WordTrace]
  refine ⟨201393345298791555005204987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134262230199194370003469991 201393345298791555005204987)
  ·
    refine ⟨302090017948187332507807481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201393345298791555005204987 302090017948187332507807481)
    ·
      refine ⟨226567513461140499380855611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302090017948187332507807481 226567513461140499380855611)
      ·
        refine ⟨339851270191710749071283417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226567513461140499380855611 339851270191710749071283417)
        ·
          refine ⟨254888452643783061803462563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339851270191710749071283417 254888452643783061803462563)
          ·
            refine ⟨382332678965674592705193845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254888452643783061803462563 382332678965674592705193845)
            ·
              refine ⟨35843688653031993066111923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 382332678965674592705193845 35843688653031993066111923)
              ·
                refine ⟨53765532979547989599167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35843688653031993066111923 53765532979547989599167885)
                ·
                  refine ⟨20162074867330496099687957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53765532979547989599167885 20162074867330496099687957)
                  ·
                    refine ⟨945097259406117004672873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20162074867330496099687957 945097259406117004672873)
                    ·
                      rfl

theorem cell23_5521711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_5521711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521711 prefixEnd_5521711 := by exact prefixLift 5521711
  have htrace : WordTrace (prefixWord ++ tailWord_5521711) baseStart_5521711 baseEnd_5521711 := by
    simpa [prefixWord, tailWord_5521711, baseEnd_5521711] using wordTrace_append hprefix tailTrace_5521711
  have hstable : (prefixWord ++ tailWord_5521711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521711).length < 2 ^ (prefixWord ++ tailWord_5521711).sum := by decide
  have hdescent : baseEnd_5521711 < baseStart_5521711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521715 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 1, 5]
def baseStart_5521715 : Nat := 118140960795 + 5521715 * 2 ^ 59
def prefixEnd_5521715 : Nat := 4983230072969 + 3 ^ 40 * 5521715 * 2
def baseEnd_5521715 : Nat := 945097944046989666122867

theorem tailTrace_5521715 : CollatzResearch.WordTrace tailWord_5521715 prefixEnd_5521715 945097944046989666122867 := by
  unfold tailWord_5521715
  simp only [CollatzResearch.WordTrace]
  refine ⟨201393491190777063688350599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134262327460518042458900399 201393491190777063688350599)
  ·
    refine ⟨302090236786165595532525899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201393491190777063688350599 302090236786165595532525899)
    ·
      refine ⟨453135355179248393298788849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302090236786165595532525899 453135355179248393298788849)
      ·
        refine ⟨339851516384436294974091637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453135355179248393298788849 339851516384436294974091637)
        ·
          refine ⟨31861079661040902653821091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 339851516384436294974091637 31861079661040902653821091)
          ·
            refine ⟨47791619491561353980731637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31861079661040902653821091 47791619491561353980731637)
            ·
              refine ⟨4480464327333876935693591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47791619491561353980731637 4480464327333876935693591)
              ·
                refine ⟨6720696491000815403540387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480464327333876935693591 6720696491000815403540387)
                ·
                  refine ⟨10081044736501223105310581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6720696491000815403540387 10081044736501223105310581)
                  ·
                    refine ⟨945097944046989666122867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10081044736501223105310581 945097944046989666122867)
                    ·
                      rfl

theorem cell23_5521715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 1, 5].length) (baseStart_5521715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521715 prefixEnd_5521715 := by exact prefixLift 5521715
  have htrace : WordTrace (prefixWord ++ tailWord_5521715) baseStart_5521715 baseEnd_5521715 := by
    simpa [prefixWord, tailWord_5521715, baseEnd_5521715] using wordTrace_append hprefix tailTrace_5521715
  have hstable : (prefixWord ++ tailWord_5521715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521715).length < 2 ^ (prefixWord ++ tailWord_5521715).sum := by decide
  have hdescent : baseEnd_5521715 < baseStart_5521715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521731 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5521731 : Nat := 118140960795 + 5521731 * 2 ^ 59
def prefixEnd_5521731 : Nat := 4983230072969 + 3 ^ 40 * 5521731 * 2
def baseEnd_5521731 : Nat := 2835302047831440935768527

theorem tailTrace_5521731 : CollatzResearch.WordTrace tailWord_5521731 prefixEnd_5521731 2835302047831440935768527 := by
  unfold tailWord_5521731
  simp only [CollatzResearch.WordTrace]
  refine ⟨201394074758719098420933047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134262716505812732280622031 201394074758719098420933047)
  ·
    refine ⟨302091112138078647631399571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201394074758719098420933047 302091112138078647631399571)
    ·
      refine ⟨453136668207117971447099357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302091112138078647631399571 453136668207117971447099357)
      ·
        refine ⟨169926250577669239292662259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453136668207117971447099357 169926250577669239292662259)
        ·
          refine ⟨254889375866503858938993389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169926250577669239292662259 254889375866503858938993389)
          ·
            refine ⟨95583515949938947102122521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254889375866503858938993389 95583515949938947102122521)
            ·
              refine ⟨71687636962454210326591891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95583515949938947102122521 71687636962454210326591891)
              ·
                refine ⟨107531455443681315489887837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71687636962454210326591891 107531455443681315489887837)
                ·
                  refine ⟨40324295791380493308707939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107531455443681315489887837 40324295791380493308707939)
                  ·
                    refine ⟨60486443687070739963061909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40324295791380493308707939 60486443687070739963061909)
                    ·
                      refine ⟨2835302047831440935768527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60486443687070739963061909 2835302047831440935768527)
                      ·
                        rfl

theorem cell23_5521731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5521731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521731 prefixEnd_5521731 := by exact prefixLift 5521731
  have htrace : WordTrace (prefixWord ++ tailWord_5521731) baseStart_5521731 baseEnd_5521731 := by
    simpa [prefixWord, tailWord_5521731, baseEnd_5521731] using wordTrace_append hprefix tailTrace_5521731
  have hstable : (prefixWord ++ tailWord_5521731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521731).length < 2 ^ (prefixWord ++ tailWord_5521731).sum := by decide
  have hdescent : baseEnd_5521731 < baseStart_5521731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521745 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_5521745 : Nat := 118140960795 + 5521745 * 2 ^ 59
def prefixEnd_5521745 : Nat := 4983230072969 + 3 ^ 40 * 5521745 * 2
def baseEnd_5521745 : Nat := 945103078853534626997821

theorem tailTrace_5521745 : CollatzResearch.WordTrace tailWord_5521745 prefixEnd_5521745 945103078853534626997821 := by
  unfold tailWord_5521745
  simp only [CollatzResearch.WordTrace]
  refine ⟨201394585380668378811942689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134263056920445585874628459 201394585380668378811942689)
  ·
    refine ⟨151045939035501284108957017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201394585380668378811942689 151045939035501284108957017)
    ·
      refine ⟨113284454276625963081717763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151045939035501284108957017 113284454276625963081717763)
      ·
        refine ⟨169926681414938944622576645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113284454276625963081717763 169926681414938944622576645)
        ·
          refine ⟨31861252765301052116733121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 169926681414938944622576645 31861252765301052116733121)
          ·
            refine ⟨23895939573975789087549841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31861252765301052116733121 23895939573975789087549841)
            ·
              refine ⟨17921954680481841815662381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23895939573975789087549841 17921954680481841815662381)
              ·
                refine ⟨6720733005180690680873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17921954680481841815662381 6720733005180690680873393)
                ·
                  refine ⟨5040549753885518010655045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6720733005180690680873393 5040549753885518010655045)
                  ·
                    refine ⟨945103078853534626997821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040549753885518010655045 945103078853534626997821)
                    ·
                      rfl

theorem cell23_5521745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_5521745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521745 prefixEnd_5521745 := by exact prefixLift 5521745
  have htrace : WordTrace (prefixWord ++ tailWord_5521745) baseStart_5521745 baseEnd_5521745 := by
    simpa [prefixWord, tailWord_5521745, baseEnd_5521745] using wordTrace_append hprefix tailTrace_5521745
  have hstable : (prefixWord ++ tailWord_5521745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521745).length < 2 ^ (prefixWord ++ tailWord_5521745).sum := by decide
  have hdescent : baseEnd_5521745 < baseStart_5521745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521756 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5521756 : Nat := 118140960795 + 5521756 * 2 ^ 59
def prefixEnd_5521756 : Nat := 4983230072969 + 3 ^ 40 * 5521756 * 2
def baseEnd_5521756 : Nat := 2835314884847803337955913

theorem tailTrace_5521756 : CollatzResearch.WordTrace tailWord_5521756 prefixEnd_5521756 2835314884847803337955913 := by
  unfold tailWord_5521756
  simp only [CollatzResearch.WordTrace]
  refine ⟨100697493291814263845296561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134263324389085685127062081 100697493291814263845296561)
  ·
    refine ⟨75523119968860697883972421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100697493291814263845296561 75523119968860697883972421)
    ·
      refine ⟨14160584994161380853244829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75523119968860697883972421 14160584994161380853244829)
      ·
        refine ⟨5310219372810517819966811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14160584994161380853244829 5310219372810517819966811)
        ·
          refine ⟨7965329059215776729950217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310219372810517819966811 7965329059215776729950217)
          ·
            refine ⟨5973996794411832547462663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7965329059215776729950217 5973996794411832547462663)
            ·
              refine ⟨8960995191617748821193995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5973996794411832547462663 8960995191617748821193995)
              ·
                refine ⟨13441492787426623231790993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8960995191617748821193995 13441492787426623231790993)
                ·
                  refine ⟨10081119590569967423843245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441492787426623231790993 10081119590569967423843245)
                  ·
                    refine ⟨3780419846463737783941217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10081119590569967423843245 3780419846463737783941217)
                    ·
                      refine ⟨2835314884847803337955913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780419846463737783941217 2835314884847803337955913)
                      ·
                        rfl

theorem cell23_5521756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5521756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521756 prefixEnd_5521756 := by exact prefixLift 5521756
  have htrace : WordTrace (prefixWord ++ tailWord_5521756) baseStart_5521756 baseEnd_5521756 := by
    simpa [prefixWord, tailWord_5521756, baseEnd_5521756] using wordTrace_append hprefix tailTrace_5521756
  have hstable : (prefixWord ++ tailWord_5521756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521756).length < 2 ^ (prefixWord ++ tailWord_5521756).sum := by decide
  have hdescent : baseEnd_5521756 < baseStart_5521756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521769 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 1, 2, 2]
def baseStart_5521769 : Nat := 118140960795 + 5521769 * 2 ^ 59
def prefixEnd_5521769 : Nat := 4983230072969 + 3 ^ 40 * 5521769 * 2
def baseEnd_5521769 : Nat := 2835321560096311787093353

theorem tailTrace_5521769 : CollatzResearch.WordTrace tailWord_5521769 prefixEnd_5521769 2835321560096311787093353 := by
  unfold tailWord_5521769
  simp only [CollatzResearch.WordTrace]
  refine ⟨201395460732581430910816361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134263640488387620607210907 201395460732581430910816361)
  ·
    refine ⟨151046595549436073183112271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201395460732581430910816361 151046595549436073183112271)
    ·
      refine ⟨226569893324154109774668407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151046595549436073183112271 226569893324154109774668407)
      ·
        refine ⟨339854839986231164662002611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226569893324154109774668407 339854839986231164662002611)
        ·
          refine ⟨509782259979346746993003917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339854839986231164662002611 509782259979346746993003917)
          ·
            refine ⟨191168347492255030122376469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509782259979346746993003917 191168347492255030122376469)
            ·
              refine ⟨8961016288699454536986397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191168347492255030122376469 8961016288699454536986397)
              ·
                refine ⟨3360381108262295451369899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8961016288699454536986397 3360381108262295451369899)
                ·
                  refine ⟨5040571662393443177054849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360381108262295451369899 5040571662393443177054849)
                  ·
                    refine ⟨3780428746795082382791137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040571662393443177054849 3780428746795082382791137)
                    ·
                      refine ⟨2835321560096311787093353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780428746795082382791137 2835321560096311787093353)
                      ·
                        rfl

theorem cell23_5521769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 1, 2, 2].length) (baseStart_5521769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521769 prefixEnd_5521769 := by exact prefixLift 5521769
  have htrace : WordTrace (prefixWord ++ tailWord_5521769) baseStart_5521769 baseEnd_5521769 := by
    simpa [prefixWord, tailWord_5521769, baseEnd_5521769] using wordTrace_append hprefix tailTrace_5521769
  have hstable : (prefixWord ++ tailWord_5521769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521769).length < 2 ^ (prefixWord ++ tailWord_5521769).sum := by decide
  have hdescent : baseEnd_5521769 < baseStart_5521769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521771 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 7]
def baseStart_5521771 : Nat := 118140960795 + 5521771 * 2 ^ 59
def prefixEnd_5521771 : Nat := 4983230072969 + 3 ^ 40 * 5521771 * 2
def baseEnd_5521771 : Nat := 945107529019206926422781

theorem tailTrace_5521771 : CollatzResearch.WordTrace tailWord_5521771 prefixEnd_5521771 945107529019206926422781 := by
  unfold tailWord_5521771
  simp only [CollatzResearch.WordTrace]
  refine ⟨201395533678574185252389167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134263689119049456834926111 201395533678574185252389167)
  ·
    refine ⟨302093300517861277878583751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201395533678574185252389167 302093300517861277878583751)
    ·
      refine ⟨453139950776791916817875627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302093300517861277878583751 453139950776791916817875627)
      ·
        refine ⟨679709926165187875226813441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453139950776791916817875627 679709926165187875226813441)
        ·
          refine ⟨509782444623890906420110081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679709926165187875226813441 509782444623890906420110081)
          ·
            refine ⟨382336833467918179815082561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509782444623890906420110081 382336833467918179815082561)
            ·
              refine ⟨286752625100938634861311921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382336833467918179815082561 286752625100938634861311921)
              ·
                refine ⟨215064468825703976145983941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286752625100938634861311921 215064468825703976145983941)
                ·
                  refine ⟨40324587904819495527371989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215064468825703976145983941 40324587904819495527371989)
                  ·
                    refine ⟨945107529019206926422781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40324587904819495527371989 945107529019206926422781)
                    ·
                      rfl

theorem cell23_5521771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_5521771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521771 prefixEnd_5521771 := by exact prefixLift 5521771
  have htrace : WordTrace (prefixWord ++ tailWord_5521771) baseStart_5521771 baseEnd_5521771 := by
    simpa [prefixWord, tailWord_5521771, baseEnd_5521771] using wordTrace_append hprefix tailTrace_5521771
  have hstable : (prefixWord ++ tailWord_5521771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521771).length < 2 ^ (prefixWord ++ tailWord_5521771).sum := by decide
  have hdescent : baseEnd_5521771 < baseStart_5521771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521772 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_5521772 : Nat := 118140960795 + 5521772 * 2 ^ 59
def prefixEnd_5521772 : Nat := 4983230072969 + 3 ^ 40 * 5521772 * 2
def baseEnd_5521772 : Nat := 2835323100538275275355839

theorem tailTrace_5521772 : CollatzResearch.WordTrace tailWord_5521772 prefixEnd_5521772 2835323100538275275355839 := by
  unfold tailWord_5521772
  simp only [CollatzResearch.WordTrace]
  refine ⟨100697785075785281211587785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134263713434380374948783713 100697785075785281211587785)
  ·
    refine ⟨75523338806838960908690839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100697785075785281211587785 75523338806838960908690839)
    ·
      refine ⟨113285008210258441363036259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75523338806838960908690839 113285008210258441363036259)
      ·
        refine ⟨169927512315387662044554389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113285008210258441363036259 169927512315387662044554389)
        ·
          refine ⟨7965352139783796658338487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169927512315387662044554389 7965352139783796658338487)
          ·
            refine ⟨11948028209675694987507731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965352139783796658338487 11948028209675694987507731)
            ·
              refine ⟨17922042314513542481261597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11948028209675694987507731 17922042314513542481261597)
              ·
                refine ⟨6720765867942578430473099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17922042314513542481261597 6720765867942578430473099)
                ·
                  refine ⟨10081148801913867645709649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6720765867942578430473099 10081148801913867645709649)
                  ·
                    refine ⟨7560861601435400734282237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10081148801913867645709649 7560861601435400734282237)
                    ·
                      refine ⟨2835323100538275275355839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7560861601435400734282237 2835323100538275275355839)
                      ·
                        rfl

theorem cell23_5521772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_5521772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521772 prefixEnd_5521772 := by exact prefixLift 5521772
  have htrace : WordTrace (prefixWord ++ tailWord_5521772) baseStart_5521772 baseEnd_5521772 := by
    simpa [prefixWord, tailWord_5521772, baseEnd_5521772] using wordTrace_append hprefix tailTrace_5521772
  have hstable : (prefixWord ++ tailWord_5521772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521772).length < 2 ^ (prefixWord ++ tailWord_5521772).sum := by decide
  have hdescent : baseEnd_5521772 < baseStart_5521772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521828 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_5521828 : Nat := 118140960795 + 5521828 * 2 ^ 59
def prefixEnd_5521828 : Nat := 4983230072969 + 3 ^ 40 * 5521828 * 2
def baseEnd_5521828 : Nat := 2835351855454927056255581

theorem tailTrace_5521828 : CollatzResearch.WordTrace tailWord_5521828 prefixEnd_5521828 2835351855454927056255581 := by
  unfold tailWord_5521828
  simp only [CollatzResearch.WordTrace]
  refine ⟨100698806319683841993607069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134265075092911789324809425 100698806319683841993607069)
  ·
    refine ⟨37762052369881440747602651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100698806319683841993607069 37762052369881440747602651)
    ·
      refine ⟨56643078554822161121403977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37762052369881440747602651 56643078554822161121403977)
      ·
        refine ⟨42482308916116620841052983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56643078554822161121403977 42482308916116620841052983)
        ·
          refine ⟨63723463374174931261579475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42482308916116620841052983 63723463374174931261579475)
          ·
            refine ⟨95585195061262396892369213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63723463374174931261579475 95585195061262396892369213)
            ·
              refine ⟨35844448147973398834638455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95585195061262396892369213 35844448147973398834638455)
              ·
                refine ⟨53766672221960098251957683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35844448147973398834638455 53766672221960098251957683)
                ·
                  refine ⟨80650008332940147377936525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53766672221960098251957683 80650008332940147377936525)
                  ·
                    refine ⟨30243753124852555266726197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80650008332940147377936525 30243753124852555266726197)
                    ·
                      refine ⟨2835351855454927056255581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30243753124852555266726197 2835351855454927056255581)
                      ·
                        rfl

theorem cell23_5521828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_5521828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521828 prefixEnd_5521828 := by exact prefixLift 5521828
  have htrace : WordTrace (prefixWord ++ tailWord_5521828) baseStart_5521828 baseEnd_5521828 := by
    simpa [prefixWord, tailWord_5521828, baseEnd_5521828] using wordTrace_append hprefix tailTrace_5521828
  have hstable : (prefixWord ++ tailWord_5521828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521828).length < 2 ^ (prefixWord ++ tailWord_5521828).sum := by decide
  have hdescent : baseEnd_5521828 < baseStart_5521828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521842 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_5521842 : Nat := 118140960795 + 5521842 * 2 ^ 59
def prefixEnd_5521842 : Nat := 4983230072969 + 3 ^ 40 * 5521842 * 2
def baseEnd_5521842 : Nat := 2835359044184090001480517

theorem tailTrace_5521842 : CollatzResearch.WordTrace tailWord_5521842 prefixEnd_5521842 2835359044184090001480517 := by
  unfold tailWord_5521842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50349530815329241094555945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134265415507544642918815853 50349530815329241094555945)
  ·
    refine ⟨37762148111496930820916959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50349530815329241094555945 37762148111496930820916959)
    ·
      refine ⟨56643222167245396231375439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37762148111496930820916959 56643222167245396231375439)
      ·
        refine ⟨84964833250868094347063159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56643222167245396231375439 84964833250868094347063159)
        ·
          refine ⟨127447249876302141520594739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84964833250868094347063159 127447249876302141520594739)
          ·
            refine ⟨191170874814453212280892109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127447249876302141520594739 191170874814453212280892109)
            ·
              refine ⟨71689078055419954605334541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191170874814453212280892109 71689078055419954605334541)
              ·
                refine ⟨26883404270782482977000453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71689078055419954605334541 26883404270782482977000453)
                ·
                  refine ⟨5040638300771715558187585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26883404270782482977000453 5040638300771715558187585)
                  ·
                    refine ⟨3780478725578786668640689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040638300771715558187585 3780478725578786668640689)
                    ·
                      refine ⟨2835359044184090001480517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780478725578786668640689 2835359044184090001480517)
                      ·
                        rfl

theorem cell23_5521842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_5521842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521842 prefixEnd_5521842 := by exact prefixLift 5521842
  have htrace : WordTrace (prefixWord ++ tailWord_5521842) baseStart_5521842 baseEnd_5521842 := by
    simpa [prefixWord, tailWord_5521842, baseEnd_5521842] using wordTrace_append hprefix tailTrace_5521842
  have hstable : (prefixWord ++ tailWord_5521842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521842).length < 2 ^ (prefixWord ++ tailWord_5521842).sum := by decide
  have hdescent : baseEnd_5521842 < baseStart_5521842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521888 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_5521888 : Nat := 118140960795 + 5521888 * 2 ^ 59
def prefixEnd_5521888 : Nat := 4983230072969 + 3 ^ 40 * 5521888 * 2
def baseEnd_5521888 : Nat := 2835382664294196821505305

theorem tailTrace_5521888 : CollatzResearch.WordTrace tailWord_5521888 prefixEnd_5521888 2835382664294196821505305 := by
  unfold tailWord_5521888
  simp only [CollatzResearch.WordTrace]
  refine ⟨100699900509575157117199159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134266534012766876156265545 100699900509575157117199159)
  ·
    refine ⟨151049850764362735675798739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100699900509575157117199159 151049850764362735675798739)
    ·
      refine ⟨226574776146544103513698109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151049850764362735675798739 226574776146544103513698109)
      ·
        refine ⟨84965541054954038817636791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226574776146544103513698109 84965541054954038817636791)
        ·
          refine ⟨127448311582431058226455187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84965541054954038817636791 127448311582431058226455187)
          ·
            refine ⟨191172467373646587339682781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127448311582431058226455187 191172467373646587339682781)
            ·
              refine ⟨71689675265117470252381043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191172467373646587339682781 71689675265117470252381043)
              ·
                refine ⟨107534512897676205378571565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71689675265117470252381043 107534512897676205378571565)
                ·
                  refine ⟨40325442336628577016964337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107534512897676205378571565 40325442336628577016964337)
                  ·
                    refine ⟨30244081752471432762723253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40325442336628577016964337 30244081752471432762723253)
                    ·
                      refine ⟨2835382664294196821505305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30244081752471432762723253 2835382664294196821505305)
                      ·
                        rfl

theorem cell23_5521888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_5521888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521888 prefixEnd_5521888 := by exact prefixLift 5521888
  have htrace : WordTrace (prefixWord ++ tailWord_5521888) baseStart_5521888 baseEnd_5521888 := by
    simpa [prefixWord, tailWord_5521888, baseEnd_5521888] using wordTrace_append hprefix tailTrace_5521888
  have hstable : (prefixWord ++ tailWord_5521888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521888).length < 2 ^ (prefixWord ++ tailWord_5521888).sum := by decide
  have hdescent : baseEnd_5521888 < baseStart_5521888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521895 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 2, 5]
def baseStart_5521895 : Nat := 118140960795 + 5521895 * 2 ^ 59
def prefixEnd_5521895 : Nat := 4983230072969 + 3 ^ 40 * 5521895 * 2
def baseEnd_5521895 : Nat := 945128752886259431372591

theorem tailTrace_5521895 : CollatzResearch.WordTrace tailWord_5521895 prefixEnd_5521895 945128752886259431372591 := by
  unfold tailWord_5521895
  simp only [CollatzResearch.WordTrace]
  refine ⟨201400056330124954429903139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134266704220083302953268759 201400056330124954429903139)
  ·
    refine ⟨302100084495187431644854709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201400056330124954429903139 302100084495187431644854709)
    ·
      refine ⟨28321882921423821716705129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302100084495187431644854709 28321882921423821716705129)
      ·
        refine ⟨21241412191067866287528847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28321882921423821716705129 21241412191067866287528847)
        ·
          refine ⟨31862118286601799431293271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21241412191067866287528847 31862118286601799431293271)
          ·
            refine ⟨47793177429902699146939907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31862118286601799431293271 47793177429902699146939907)
            ·
              refine ⟨71689766144854048720409861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47793177429902699146939907 71689766144854048720409861)
              ·
                refine ⟨13441831152160134135076849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71689766144854048720409861 13441831152160134135076849)
                ·
                  refine ⟨10081373364120100601307637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441831152160134135076849 10081373364120100601307637)
                  ·
                    refine ⟨945128752886259431372591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10081373364120100601307637 945128752886259431372591)
                    ·
                      rfl

theorem cell23_5521895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_5521895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521895 prefixEnd_5521895 := by exact prefixLift 5521895
  have htrace : WordTrace (prefixWord ++ tailWord_5521895) baseStart_5521895 baseEnd_5521895 := by
    simpa [prefixWord, tailWord_5521895, baseEnd_5521895] using wordTrace_append hprefix tailTrace_5521895
  have hstable : (prefixWord ++ tailWord_5521895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521895).length < 2 ^ (prefixWord ++ tailWord_5521895).sum := by decide
  have hdescent : baseEnd_5521895 < baseStart_5521895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521902 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_5521902 : Nat := 118140960795 + 5521902 * 2 ^ 59
def prefixEnd_5521902 : Nat := 4983230072969 + 3 ^ 40 * 5521902 * 2
def baseEnd_5521902 : Nat := 2835389853023359766730241

theorem tailTrace_5521902 : CollatzResearch.WordTrace tailWord_5521902 prefixEnd_5521902 2835389853023359766730241 := by
  unfold tailWord_5521902
  simp only [CollatzResearch.WordTrace]
  refine ⟨25175038955137449328175995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134266874427399729750271973 25175038955137449328175995)
  ·
    refine ⟨37762558432706173992263993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25175038955137449328175995 37762558432706173992263993)
    ·
      refine ⟨28321918824529630494197995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37762558432706173992263993 28321918824529630494197995)
      ·
        refine ⟨42482878236794445741296993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28321918824529630494197995 42482878236794445741296993)
        ·
          refine ⟨31862158677595834305972745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42482878236794445741296993 31862158677595834305972745)
          ·
            refine ⟨23896619008196875729479559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31862158677595834305972745 23896619008196875729479559)
            ·
              refine ⟨35844928512295313594219339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23896619008196875729479559 35844928512295313594219339)
              ·
                refine ⟨53767392768442970391329009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35844928512295313594219339 53767392768442970391329009)
                ·
                  refine ⟨40325544576332227793496757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53767392768442970391329009 40325544576332227793496757)
                  ·
                    refine ⟨3780519804031146355640321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40325544576332227793496757 3780519804031146355640321)
                    ·
                      refine ⟨2835389853023359766730241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780519804031146355640321 2835389853023359766730241)
                      ·
                        rfl

theorem cell23_5521902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_5521902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521902 prefixEnd_5521902 := by exact prefixLift 5521902
  have htrace : WordTrace (prefixWord ++ tailWord_5521902) baseStart_5521902 baseEnd_5521902 := by
    simpa [prefixWord, tailWord_5521902, baseEnd_5521902] using wordTrace_append hprefix tailTrace_5521902
  have hstable : (prefixWord ++ tailWord_5521902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521902).length < 2 ^ (prefixWord ++ tailWord_5521902).sum := by decide
  have hdescent : baseEnd_5521902 < baseStart_5521902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521909 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5521909 : Nat := 118140960795 + 5521909 * 2 ^ 59
def prefixEnd_5521909 : Nat := 4983230072969 + 3 ^ 40 * 5521909 * 2
def baseEnd_5521909 : Nat := 2835393447387941239342709

theorem tailTrace_5521909 : CollatzResearch.WordTrace tailWord_5521909 prefixEnd_5521909 2835393447387941239342709 := by
  unfold tailWord_5521909
  simp only [CollatzResearch.WordTrace]
  refine ⟨201400566952074234820912781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134267044634716156547275187 201400566952074234820912781)
  ·
    refine ⟨75525212607027838057842293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201400566952074234820912781 75525212607027838057842293)
    ·
      refine ⟨7080488681908859817922715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75525212607027838057842293 7080488681908859817922715)
      ·
        refine ⟨10620733022863289726884073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080488681908859817922715 10620733022863289726884073)
        ·
          refine ⟨7965549767147467295163055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10620733022863289726884073 7965549767147467295163055)
          ·
            refine ⟨11948324650721200942744583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965549767147467295163055 11948324650721200942744583)
            ·
              refine ⟨17922486976081801414116875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11948324650721200942744583 17922486976081801414116875)
              ·
                refine ⟨26883730464122702121175313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17922486976081801414116875 26883730464122702121175313)
                ·
                  refine ⟨20162797848092026590881485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26883730464122702121175313 20162797848092026590881485)
                  ·
                    refine ⟨7561049193034509971580557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20162797848092026590881485 7561049193034509971580557)
                    ·
                      refine ⟨2835393447387941239342709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561049193034509971580557 2835393447387941239342709)
                      ·
                        rfl

theorem cell23_5521909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5521909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521909 prefixEnd_5521909 := by exact prefixLift 5521909
  have htrace : WordTrace (prefixWord ++ tailWord_5521909) baseStart_5521909 baseEnd_5521909 := by
    simpa [prefixWord, tailWord_5521909, baseEnd_5521909] using wordTrace_append hprefix tailTrace_5521909
  have hstable : (prefixWord ++ tailWord_5521909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521909).length < 2 ^ (prefixWord ++ tailWord_5521909).sum := by decide
  have hdescent : baseEnd_5521909 < baseStart_5521909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521925 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_5521925 : Nat := 118140960795 + 5521925 * 2 ^ 59
def prefixEnd_5521925 : Nat := 4983230072969 + 3 ^ 40 * 5521925 * 2
def baseEnd_5521925 : Nat := 945133887692804392247545

theorem tailTrace_5521925 : CollatzResearch.WordTrace tailWord_5521925 prefixEnd_5521925 945133887692804392247545 := by
  unfold tailWord_5521925
  simp only [CollatzResearch.WordTrace]
  refine ⟨201401150520016269553495229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134267433680010846368996819 201401150520016269553495229)
  ·
    refine ⟨75525431445006101082560711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201401150520016269553495229 75525431445006101082560711)
    ·
      refine ⟨113288147167509151623841067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75525431445006101082560711 113288147167509151623841067)
      ·
        refine ⟨169932220751263727435761601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113288147167509151623841067 169932220751263727435761601)
        ·
          refine ⟨127449165563447795576821201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169932220751263727435761601 127449165563447795576821201)
          ·
            refine ⟨95586874172585846682615901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127449165563447795576821201 95586874172585846682615901)
            ·
              refine ⟨35845077814719692505980963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95586874172585846682615901 35845077814719692505980963)
              ·
                refine ⟨53767616722079538758971445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35845077814719692505980963 53767616722079538758971445)
                ·
                  refine ⟨5040714067694956758653573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53767616722079538758971445 5040714067694956758653573)
                  ·
                    refine ⟨945133887692804392247545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040714067694956758653573 945133887692804392247545)
                    ·
                      rfl

theorem cell23_5521925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_5521925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521925 prefixEnd_5521925 := by exact prefixLift 5521925
  have htrace : WordTrace (prefixWord ++ tailWord_5521925) baseStart_5521925 baseEnd_5521925 := by
    simpa [prefixWord, tailWord_5521925, baseEnd_5521925] using wordTrace_append hprefix tailTrace_5521925
  have hstable : (prefixWord ++ tailWord_5521925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521925).length < 2 ^ (prefixWord ++ tailWord_5521925).sum := by decide
  have hdescent : baseEnd_5521925 < baseStart_5521925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521932 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_5521932 : Nat := 118140960795 + 5521932 * 2 ^ 59
def prefixEnd_5521932 : Nat := 4983230072969 + 3 ^ 40 * 5521932 * 2
def baseEnd_5521932 : Nat := 2835405257442994649355103

theorem tailTrace_5521932 : CollatzResearch.WordTrace tailWord_5521932 prefixEnd_5521932 2835405257442994649355103 := by
  unfold tailWord_5521932
  simp only [CollatzResearch.WordTrace]
  refine ⟨100700702915495454874500025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134267603887327273166000033 100700702915495454874500025)
  ·
    refine ⟨75525527186621591155875019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100700702915495454874500025 75525527186621591155875019)
    ·
      refine ⟨113288290779932386733812529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75525527186621591155875019 113288290779932386733812529)
      ·
        refine ⟨84966218084949290050359397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113288290779932386733812529 84966218084949290050359397)
        ·
          refine ⟨15931165890927991884442387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84966218084949290050359397 15931165890927991884442387)
          ·
            refine ⟨23896748836391987826663581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931165890927991884442387 23896748836391987826663581)
            ·
              refine ⟨8961280813646995434998843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23896748836391987826663581 8961280813646995434998843)
              ·
                refine ⟨13441921220470493152498265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961280813646995434998843 13441921220470493152498265)
                ·
                  refine ⟨10081440915352869864373699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13441921220470493152498265 10081440915352869864373699)
                  ·
                    refine ⟨15122161373029304796560549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10081440915352869864373699 15122161373029304796560549)
                    ·
                      refine ⟨2835405257442994649355103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15122161373029304796560549 2835405257442994649355103)
                      ·
                        rfl

theorem cell23_5521932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_5521932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521932 prefixEnd_5521932 := by exact prefixLift 5521932
  have htrace : WordTrace (prefixWord ++ tailWord_5521932) baseStart_5521932 baseEnd_5521932 := by
    simpa [prefixWord, tailWord_5521932, baseEnd_5521932] using wordTrace_append hprefix tailTrace_5521932
  have hstable : (prefixWord ++ tailWord_5521932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521932).length < 2 ^ (prefixWord ++ tailWord_5521932).sum := by decide
  have hdescent : baseEnd_5521932 < baseStart_5521932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521955 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 8]
def baseStart_5521955 : Nat := 118140960795 + 5521955 * 2 ^ 59
def prefixEnd_5521955 : Nat := 4983230072969 + 3 ^ 40 * 5521955 * 2
def baseEnd_5521955 : Nat := 315046340833116451040833

theorem tailTrace_5521955 : CollatzResearch.WordTrace tailWord_5521955 prefixEnd_5521955 315046340833116451040833 := by
  unfold tailWord_5521955
  simp only [CollatzResearch.WordTrace]
  refine ⟨201402244709907584677087319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134268163139938389784724879 201402244709907584677087319)
  ·
    refine ⟨302103367064861377015630979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201402244709907584677087319 302103367064861377015630979)
    ·
      refine ⟨453155050597292065523446469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302103367064861377015630979 453155050597292065523446469)
      ·
        refine ⟨84966571986992262285646213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453155050597292065523446469 84966571986992262285646213)
        ·
          refine ⟨15931232247561049178558665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84966571986992262285646213 15931232247561049178558665)
          ·
            refine ⟨11948424185670786883918999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15931232247561049178558665 11948424185670786883918999)
            ·
              refine ⟨17922636278506180325878499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11948424185670786883918999 17922636278506180325878499)
              ·
                refine ⟨26883954417759270488817749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17922636278506180325878499 26883954417759270488817749)
                ·
                  refine ⟨315046340833116451040833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26883954417759270488817749 315046340833116451040833)
                  ·
                    rfl

theorem cell23_5521955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 8].length) (baseStart_5521955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521955 prefixEnd_5521955 := by exact prefixLift 5521955
  have htrace : WordTrace (prefixWord ++ tailWord_5521955) baseStart_5521955 baseEnd_5521955 := by
    simpa [prefixWord, tailWord_5521955, baseEnd_5521955] using wordTrace_append hprefix tailTrace_5521955
  have hstable : (prefixWord ++ tailWord_5521955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521955).length < 2 ^ (prefixWord ++ tailWord_5521955).sum := by decide
  have hdescent : baseEnd_5521955 < baseStart_5521955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5521992 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_5521992 : Nat := 118140960795 + 5521992 * 2 ^ 59
def prefixEnd_5521992 : Nat := 4983230072969 + 3 ^ 40 * 5521992 * 2
def baseEnd_5521992 : Nat := 2835436066282264414604827

theorem tailTrace_5521992 : CollatzResearch.WordTrace tailWord_5521992 prefixEnd_5521992 2835436066282264414604827 := by
  unfold tailWord_5521992
  simp only [CollatzResearch.WordTrace]
  refine ⟨100701797105386769998092115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134269062807182359997456153 100701797105386769998092115)
  ·
    refine ⟨151052695658080154997138173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100701797105386769998092115 151052695658080154997138173)
    ·
      refine ⟨56644760871780058123926815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151052695658080154997138173 56644760871780058123926815)
      ·
        refine ⟨84967141307670087185890223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56644760871780058123926815 84967141307670087185890223)
        ·
          refine ⟨127450711961505130778835335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84967141307670087185890223 127450711961505130778835335)
          ·
            refine ⟨191176067942257696168253003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127450711961505130778835335 191176067942257696168253003)
            ·
              refine ⟨286764101913386544252379505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191176067942257696168253003 286764101913386544252379505)
              ·
                refine ⟨215073076435039908189284629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286764101913386544252379505 215073076435039908189284629)
                ·
                  refine ⟨10081550457892495696372717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215073076435039908189284629 10081550457892495696372717)
                  ·
                    refine ⟨3780581421709685886139769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10081550457892495696372717 3780581421709685886139769)
                    ·
                      refine ⟨2835436066282264414604827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780581421709685886139769 2835436066282264414604827)
                      ·
                        rfl

theorem cell23_5521992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_5521992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5521992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5521992 prefixEnd_5521992 := by exact prefixLift 5521992
  have htrace : WordTrace (prefixWord ++ tailWord_5521992) baseStart_5521992 baseEnd_5521992 := by
    simpa [prefixWord, tailWord_5521992, baseEnd_5521992] using wordTrace_append hprefix tailTrace_5521992
  have hstable : (prefixWord ++ tailWord_5521992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5521992).length < 2 ^ (prefixWord ++ tailWord_5521992).sum := by decide
  have hdescent : baseEnd_5521992 < baseStart_5521992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5521992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522002 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_5522002 : Nat := 118140960795 + 5522002 * 2 ^ 59
def prefixEnd_5522002 : Nat := 4983230072969 + 3 ^ 40 * 5522002 * 2
def baseEnd_5522002 : Nat := 945147067029603125159927

theorem tailTrace_5522002 : CollatzResearch.WordTrace tailWord_5522002 prefixEnd_5522002 945147067029603125159927 := by
  unfold tailWord_5522002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50350989735184327926012065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134269305960491541136032173 50350989735184327926012065)
  ·
    refine ⟨37763242301388245944509049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50350989735184327926012065 37763242301388245944509049)
    ·
      refine ⟨28322431726041184458381787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37763242301388245944509049 28322431726041184458381787)
      ·
        refine ⟨42483647589061776687572681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28322431726041184458381787 42483647589061776687572681)
        ·
          refine ⟨31862735691796332515679511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42483647589061776687572681 31862735691796332515679511)
          ·
            refine ⟨47794103537694498773519267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31862735691796332515679511 47794103537694498773519267)
            ·
              refine ⟨71691155306541748160278901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47794103537694498773519267 71691155306541748160278901)
              ·
                refine ⟨6721045809988288890026147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71691155306541748160278901 6721045809988288890026147)
                ·
                  refine ⟨10081568714982433335039221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721045809988288890026147 10081568714982433335039221)
                  ·
                    refine ⟨945147067029603125159927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10081568714982433335039221 945147067029603125159927)
                    ·
                      rfl

theorem cell23_5522002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_5522002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522002 prefixEnd_5522002 := by exact prefixLift 5522002
  have htrace : WordTrace (prefixWord ++ tailWord_5522002) baseStart_5522002 baseEnd_5522002 := by
    simpa [prefixWord, tailWord_5522002, baseEnd_5522002] using wordTrace_append hprefix tailTrace_5522002
  have hstable : (prefixWord ++ tailWord_5522002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522002).length < 2 ^ (prefixWord ++ tailWord_5522002).sum := by decide
  have hdescent : baseEnd_5522002 < baseStart_5522002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
