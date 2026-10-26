import V185TrunkScan23Chunk0244

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1449306 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_1449306 : Nat := 118140960795 + 1449306 * 2 ^ 59
def prefixEnd_1449306 : Nat := 4983230072969 + 3 ^ 40 * 1449306 * 2
def baseEnd_1449306 : Nat := 744190593445211817309769

theorem tailTrace_1449306 : CollatzResearch.WordTrace tailWord_1449306 prefixEnd_1449306 744190593445211817309769 := by
  unfold tailWord_1449306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215133121854839650923943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35240354991612905735797181 13215133121854839650923943)
  ·
    refine ⟨19822699682782259476385915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13215133121854839650923943 19822699682782259476385915)
    ·
      refine ⟨29734049524173389214578873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19822699682782259476385915 29734049524173389214578873)
      ·
        refine ⟨22300537143130041910934155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29734049524173389214578873 22300537143130041910934155)
        ·
          refine ⟨33450805714695062866401233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22300537143130041910934155 33450805714695062866401233)
          ·
            refine ⟨25088104286021297149800925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33450805714695062866401233 25088104286021297149800925)
            ·
              refine ⟨9408039107257986431175347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25088104286021297149800925 9408039107257986431175347)
              ·
                refine ⟨14112058660886979646763021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408039107257986431175347 14112058660886979646763021)
                ·
                  refine ⟨5292021997832617367536133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14112058660886979646763021 5292021997832617367536133)
                  ·
                    refine ⟨992254124593615756413025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292021997832617367536133 992254124593615756413025)
                    ·
                      refine ⟨744190593445211817309769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992254124593615756413025 744190593445211817309769)
                      ·
                        rfl

theorem cell23_1449306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_1449306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449306 prefixEnd_1449306 := by exact prefixLift 1449306
  have htrace : WordTrace (prefixWord ++ tailWord_1449306) baseStart_1449306 baseEnd_1449306 := by
    simpa [prefixWord, tailWord_1449306, baseEnd_1449306] using wordTrace_append hprefix tailTrace_1449306
  have hstable : (prefixWord ++ tailWord_1449306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449306).length < 2 ^ (prefixWord ++ tailWord_1449306).sum := by decide
  have hdescent : baseEnd_1449306 < baseStart_1449306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449416 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1449416 : Nat := 118140960795 + 1449416 * 2 ^ 59
def prefixEnd_1449416 : Nat := 4983230072969 + 3 ^ 40 * 1449416 * 2
def baseEnd_1449416 : Nat := 744247076317206386934263

theorem tailTrace_1449416 : CollatzResearch.WordTrace tailWord_1449416 prefixEnd_1449416 744247076317206386934263 := by
  unfold tailWord_1449416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26432272258510423695100051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35243029678013898260133401 26432272258510423695100051)
  ·
    refine ⟨39648408387765635542650077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26432272258510423695100051 39648408387765635542650077)
    ·
      refine ⟨14868153145412113328493779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39648408387765635542650077 14868153145412113328493779)
      ·
        refine ⟨22302229718118169992740669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14868153145412113328493779 22302229718118169992740669)
        ·
          refine ⟨8363336144294313747277751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22302229718118169992740669 8363336144294313747277751)
          ·
            refine ⟨12545004216441470620916627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363336144294313747277751 12545004216441470620916627)
            ·
              refine ⟨18817506324662205931374941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545004216441470620916627 18817506324662205931374941)
              ·
                refine ⟨7056564871748327224265603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18817506324662205931374941 7056564871748327224265603)
                ·
                  refine ⟨10584847307622490836398405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056564871748327224265603 10584847307622490836398405)
                  ·
                    refine ⟨1984658870179217031824701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10584847307622490836398405 1984658870179217031824701)
                    ·
                      refine ⟨744247076317206386934263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984658870179217031824701 744247076317206386934263)
                      ·
                        rfl

theorem cell23_1449416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1449416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449416 prefixEnd_1449416 := by exact prefixLift 1449416
  have htrace : WordTrace (prefixWord ++ tailWord_1449416) baseStart_1449416 baseEnd_1449416 := by
    simpa [prefixWord, tailWord_1449416, baseEnd_1449416] using wordTrace_append hprefix tailTrace_1449416
  have hstable : (prefixWord ++ tailWord_1449416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449416).length < 2 ^ (prefixWord ++ tailWord_1449416).sum := by decide
  have hdescent : baseEnd_1449416 < baseStart_1449416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449419 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 8]
def baseStart_1449419 : Nat := 118140960795 + 1449419 * 2 ^ 59
def prefixEnd_1449419 : Nat := 4983230072969 + 3 ^ 40 * 1449419 * 2
def baseEnd_1449419 : Nat := 82694290751018875021861

theorem tailTrace_1449419 : CollatzResearch.WordTrace tailWord_1449419 prefixEnd_1449419 82694290751018875021861 := by
  unfold tailWord_1449419
  simp only [CollatzResearch.WordTrace]
  refine ⟨52864653936009978902559311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35243102624006652601706207 52864653936009978902559311)
  ·
    refine ⟨79296980904014968353838967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52864653936009978902559311 79296980904014968353838967)
    ·
      refine ⟨118945471356022452530758451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79296980904014968353838967 118945471356022452530758451)
      ·
        refine ⟨178418207034033678796137677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118945471356022452530758451 178418207034033678796137677)
        ·
          refine ⟨66906827637762629548551629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178418207034033678796137677 66906827637762629548551629)
          ·
            refine ⟨25090060364160986080706861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66906827637762629548551629 25090060364160986080706861)
            ·
              refine ⟨9408772636560369780265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25090060364160986080706861 9408772636560369780265073)
              ·
                refine ⟨7056579477420277335198805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408772636560369780265073 7056579477420277335198805)
                ·
                  refine ⟨82694290751018875021861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7056579477420277335198805 82694290751018875021861)
                  ·
                    rfl

theorem cell23_1449419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 8].length) (baseStart_1449419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449419 prefixEnd_1449419 := by exact prefixLift 1449419
  have htrace : WordTrace (prefixWord ++ tailWord_1449419) baseStart_1449419 baseEnd_1449419 := by
    simpa [prefixWord, tailWord_1449419, baseEnd_1449419] using wordTrace_append hprefix tailTrace_1449419
  have hstable : (prefixWord ++ tailWord_1449419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449419).length < 2 ^ (prefixWord ++ tailWord_1449419).sum := by decide
  have hdescent : baseEnd_1449419 < baseStart_1449419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449430 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1449430 : Nat := 118140960795 + 1449430 * 2 ^ 59
def prefixEnd_1449430 : Nat := 4983230072969 + 3 ^ 40 * 1449430 * 2
def baseEnd_1449430 : Nat := 744254265046369332159199

theorem tailTrace_1449430 : CollatzResearch.WordTrace tailWord_1449430 prefixEnd_1449430 744254265046369332159199 := by
  unfold tailWord_1449430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304065946185632986325609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35243370092646751854139829 3304065946185632986325609)
  ·
    refine ⟨2478049459639224739744207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3304065946185632986325609 2478049459639224739744207)
    ·
      refine ⟨3717074189458837109616311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478049459639224739744207 3717074189458837109616311)
      ·
        refine ⟨5575611284188255664424467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717074189458837109616311 5575611284188255664424467)
        ·
          refine ⟨8363416926282383496636701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575611284188255664424467 8363416926282383496636701)
          ·
            refine ⟨3136281347355893811238763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8363416926282383496636701 3136281347355893811238763)
            ·
              refine ⟨4704422021033840716858145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136281347355893811238763 4704422021033840716858145)
              ·
                refine ⟨3528316515775380537643609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704422021033840716858145 3528316515775380537643609)
                ·
                  refine ⟨2646237386831535403232707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528316515775380537643609 2646237386831535403232707)
                  ·
                    refine ⟨3969356080247303104849061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646237386831535403232707 3969356080247303104849061)
                    ·
                      refine ⟨744254265046369332159199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3969356080247303104849061 744254265046369332159199)
                      ·
                        rfl

theorem cell23_1449430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1449430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449430 prefixEnd_1449430 := by exact prefixLift 1449430
  have htrace : WordTrace (prefixWord ++ tailWord_1449430) baseStart_1449430 baseEnd_1449430 := by
    simpa [prefixWord, tailWord_1449430, baseEnd_1449430] using wordTrace_append hprefix tailTrace_1449430
  have hstable : (prefixWord ++ tailWord_1449430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449430).length < 2 ^ (prefixWord ++ tailWord_1449430).sum := by decide
  have hdescent : baseEnd_1449430 < baseStart_1449430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449433 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1449433 : Nat := 118140960795 + 1449433 * 2 ^ 59
def prefixEnd_1449433 : Nat := 4983230072969 + 3 ^ 40 * 1449433 * 2
def baseEnd_1449433 : Nat := 744255805488332820421685

theorem tailTrace_1449433 : CollatzResearch.WordTrace tailWord_1449433 prefixEnd_1449433 744255805488332820421685 := by
  unfold tailWord_1449433
  simp only [CollatzResearch.WordTrace]
  refine ⟨52865164557959259293568953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35243443038639506195712635 52865164557959259293568953)
  ·
    refine ⟨39648873418469444470176715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52865164557959259293568953 39648873418469444470176715)
    ·
      refine ⟨59473310127704166705265073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39648873418469444470176715 59473310127704166705265073)
      ·
        refine ⟨44604982595778125028948805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59473310127704166705265073 44604982595778125028948805)
        ·
          refine ⟨8363434236708398442927901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44604982595778125028948805 8363434236708398442927901)
          ·
            refine ⟨3136287838765649416097963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8363434236708398442927901 3136287838765649416097963)
            ·
              refine ⟨4704431758148474124146945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136287838765649416097963 4704431758148474124146945)
              ·
                refine ⟨3528323818611355593110209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704431758148474124146945 3528323818611355593110209)
                ·
                  refine ⟨2646242863958516694832657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528323818611355593110209 2646242863958516694832657)
                  ·
                    refine ⟨1984682147968887521124493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646242863958516694832657 1984682147968887521124493)
                    ·
                      refine ⟨744255805488332820421685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984682147968887521124493 744255805488332820421685)
                      ·
                        rfl

theorem cell23_1449433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1449433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449433 prefixEnd_1449433 := by exact prefixLift 1449433
  have htrace : WordTrace (prefixWord ++ tailWord_1449433) baseStart_1449433 baseEnd_1449433 := by
    simpa [prefixWord, tailWord_1449433, baseEnd_1449433] using wordTrace_append hprefix tailTrace_1449433
  have hstable : (prefixWord ++ tailWord_1449433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449433).length < 2 ^ (prefixWord ++ tailWord_1449433).sum := by decide
  have hdescent : baseEnd_1449433 < baseStart_1449433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449459 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1449459 : Nat := 118140960795 + 1449459 * 2 ^ 59
def prefixEnd_1449459 : Nat := 4983230072969 + 3 ^ 40 * 1449459 * 2
def baseEnd_1449459 : Nat := 744269155985349718696565

theorem tailTrace_1449459 : CollatzResearch.WordTrace tailWord_1449459 prefixEnd_1449459 744269155985349718696565 := by
  unfold tailWord_1449459
  simp only [CollatzResearch.WordTrace]
  refine ⟨52866112855865065734015431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35244075237243377156010287 52866112855865065734015431)
  ·
    refine ⟨79299169283797598601023147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52866112855865065734015431 79299169283797598601023147)
    ·
      refine ⟨118948753925696397901534721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79299169283797598601023147 118948753925696397901534721)
      ·
        refine ⟨89211565444272298426151041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118948753925696397901534721 89211565444272298426151041)
        ·
          refine ⟨66908674083204223819613281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89211565444272298426151041 66908674083204223819613281)
          ·
            refine ⟨50181505562403167864709961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66908674083204223819613281 50181505562403167864709961)
            ·
              refine ⟨37636129171802375898532471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50181505562403167864709961 37636129171802375898532471)
              ·
                refine ⟨56454193757703563847798707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37636129171802375898532471 56454193757703563847798707)
                ·
                  refine ⟨84681290636555345771698061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56454193757703563847798707 84681290636555345771698061)
                  ·
                    refine ⟨31755483988708254664386773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84681290636555345771698061 31755483988708254664386773)
                    ·
                      refine ⟨744269155985349718696565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31755483988708254664386773 744269155985349718696565)
                      ·
                        rfl

theorem cell23_1449459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1449459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449459 prefixEnd_1449459 := by exact prefixLift 1449459
  have htrace : WordTrace (prefixWord ++ tailWord_1449459) baseStart_1449459 baseEnd_1449459 := by
    simpa [prefixWord, tailWord_1449459, baseEnd_1449459] using wordTrace_append hprefix tailTrace_1449459
  have hstable : (prefixWord ++ tailWord_1449459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449459).length < 2 ^ (prefixWord ++ tailWord_1449459).sum := by decide
  have hdescent : baseEnd_1449459 < baseStart_1449459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449466 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_1449466 : Nat := 118140960795 + 1449466 * 2 ^ 59
def prefixEnd_1449466 : Nat := 4983230072969 + 3 ^ 40 * 1449466 * 2
def baseEnd_1449466 : Nat := 248090916783310397103011

theorem tailTrace_1449466 : CollatzResearch.WordTrace tailWord_1449466 prefixEnd_1449466 248090916783310397103011 := by
  unfold tailWord_1449466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216592041709926482380063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35244245444559803953013501 13216592041709926482380063)
  ·
    refine ⟨19824888062564889723570095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13216592041709926482380063 19824888062564889723570095)
    ·
      refine ⟨29737332093847334585355143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19824888062564889723570095 29737332093847334585355143)
      ·
        refine ⟨44605998140771001878032715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29737332093847334585355143 44605998140771001878032715)
        ·
          refine ⟨66908997211156502817049073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44605998140771001878032715 66908997211156502817049073)
          ·
            refine ⟨50181747908367377112786805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66908997211156502817049073 50181747908367377112786805)
            ·
              refine ⟨4704538866409441604323763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50181747908367377112786805 4704538866409441604323763)
              ·
                refine ⟨7056808299614162406485645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704538866409441604323763 7056808299614162406485645)
                ·
                  refine ⟨2646303112355310902432117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7056808299614162406485645 2646303112355310902432117)
                  ·
                    refine ⟨248090916783310397103011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2646303112355310902432117 248090916783310397103011)
                    ·
                      rfl

theorem cell23_1449466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_1449466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449466 prefixEnd_1449466 := by exact prefixLift 1449466
  have htrace : WordTrace (prefixWord ++ tailWord_1449466) baseStart_1449466 baseEnd_1449466 := by
    simpa [prefixWord, tailWord_1449466, baseEnd_1449466] using wordTrace_append hprefix tailTrace_1449466
  have hstable : (prefixWord ++ tailWord_1449466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449466).length < 2 ^ (prefixWord ++ tailWord_1449466).sum := by decide
  have hdescent : baseEnd_1449466 < baseStart_1449466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449523 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3]
def baseStart_1449523 : Nat := 118140960795 + 1449523 * 2 ^ 59
def prefixEnd_1449523 : Nat := 4983230072969 + 3 ^ 40 * 1449523 * 2
def baseEnd_1449523 : Nat := 744302018747237468296271

theorem tailTrace_1449523 : CollatzResearch.WordTrace tailWord_1449523 prefixEnd_1449523 744302018747237468296271 := by
  unfold tailWord_1449523
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868447127633204664345223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35245631418422136442896815 52868447127633204664345223)
  ·
    refine ⟨79302670691449806996517835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52868447127633204664345223 79302670691449806996517835)
    ·
      refine ⟨118954006037174710494776753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79302670691449806996517835 118954006037174710494776753)
      ·
        refine ⟨89215504527881032871082565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118954006037174710494776753 89215504527881032871082565)
        ·
          refine ⟨16727907098977693663327981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89215504527881032871082565 16727907098977693663327981)
          ·
            refine ⟨6272965162116635123747993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16727907098977693663327981 6272965162116635123747993)
            ·
              refine ⟨4704723871587476342810995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6272965162116635123747993 4704723871587476342810995)
              ·
                refine ⟨7057085807381214514216493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704723871587476342810995 7057085807381214514216493)
                ·
                  refine ⟨2646407177767955442831185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7057085807381214514216493 2646407177767955442831185)
                  ·
                    refine ⟨1984805383325966582123389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2646407177767955442831185 1984805383325966582123389)
                    ·
                      refine ⟨744302018747237468296271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1984805383325966582123389 744302018747237468296271)
                      ·
                        rfl

theorem cell23_1449523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_1449523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449523 prefixEnd_1449523 := by exact prefixLift 1449523
  have htrace : WordTrace (prefixWord ++ tailWord_1449523) baseStart_1449523 baseEnd_1449523 := by
    simpa [prefixWord, tailWord_1449523, baseEnd_1449523] using wordTrace_append hprefix tailTrace_1449523
  have hstable : (prefixWord ++ tailWord_1449523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449523).length < 2 ^ (prefixWord ++ tailWord_1449523).sum := by decide
  have hdescent : baseEnd_1449523 < baseStart_1449523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449554 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_1449554 : Nat := 118140960795 + 1449554 * 2 ^ 59
def prefixEnd_1449554 : Nat := 4983230072969 + 3 ^ 40 * 1449554 * 2
def baseEnd_1449554 : Nat := 744317936647526847008629

theorem tailTrace_1449554 : CollatzResearch.WordTrace tailWord_1449554 prefixEnd_1449554 744317936647526847008629 := by
  unfold tailWord_1449554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217394447630224239680929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35246385193680597972482477 13217394447630224239680929)
  ·
    refine ⟨9913045835722668179760697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13217394447630224239680929 9913045835722668179760697)
    ·
      refine ⟨7434784376792001134820523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9913045835722668179760697 7434784376792001134820523)
      ·
        refine ⟨11152176565188001702230785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434784376792001134820523 11152176565188001702230785)
        ·
          refine ⟨8364132423891001276673089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11152176565188001702230785 8364132423891001276673089)
          ·
            refine ⟨6273099317918250957504817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8364132423891001276673089 6273099317918250957504817)
            ·
              refine ⟨4704824488438688218128613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273099317918250957504817 4704824488438688218128613)
              ·
                refine ⟨882154591582254040899115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4704824488438688218128613 882154591582254040899115)
                ·
                  refine ⟨1323231887373381061348673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882154591582254040899115 1323231887373381061348673)
                  ·
                    refine ⟨992423915530035796011505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323231887373381061348673 992423915530035796011505)
                    ·
                      refine ⟨744317936647526847008629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992423915530035796011505 744317936647526847008629)
                      ·
                        rfl

theorem cell23_1449554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_1449554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449554 prefixEnd_1449554 := by exact prefixLift 1449554
  have htrace : WordTrace (prefixWord ++ tailWord_1449554) baseStart_1449554 baseEnd_1449554 := by
    simpa [prefixWord, tailWord_1449554, baseEnd_1449554] using wordTrace_append hprefix tailTrace_1449554
  have hstable : (prefixWord ++ tailWord_1449554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449554).length < 2 ^ (prefixWord ++ tailWord_1449554).sum := by decide
  have hdescent : baseEnd_1449554 < baseStart_1449554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449597 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_1449597 : Nat := 118140960795 + 1449597 * 2 ^ 59
def prefixEnd_1449597 : Nat := 4983230072969 + 3 ^ 40 * 1449597 * 2
def baseEnd_1449597 : Nat := 744340016315670178770931

theorem tailTrace_1449597 : CollatzResearch.WordTrace tailWord_1449597 prefixEnd_1449597 744340016315670178770931 := by
  unfold tailWord_1449597
  simp only [CollatzResearch.WordTrace]
  refine ⟨52871146129365115302539045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35247430752910076868359363 52871146129365115302539045)
  ·
    refine ⟨9913339899255959119226071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52871146129365115302539045 9913339899255959119226071)
    ·
      refine ⟨14870009848883938678839107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9913339899255959119226071 14870009848883938678839107)
      ·
        refine ⟨22305014773325908018258661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14870009848883938678839107 22305014773325908018258661)
        ·
          refine ⟨4182190269998607753423499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22305014773325908018258661 4182190269998607753423499)
          ·
            refine ⟨6273285404997911630135249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182190269998607753423499 6273285404997911630135249)
            ·
              refine ⟨4704964053748433722601437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273285404997911630135249 4704964053748433722601437)
              ·
                refine ⟨1764361520155662645975539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4704964053748433722601437 1764361520155662645975539)
                ·
                  refine ⟨2646542280233493968963309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764361520155662645975539 2646542280233493968963309)
                  ·
                    refine ⟨992453355087560238361241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646542280233493968963309 992453355087560238361241)
                    ·
                      refine ⟨744340016315670178770931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992453355087560238361241 744340016315670178770931)
                      ·
                        rfl

theorem cell23_1449597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_1449597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449597 prefixEnd_1449597 := by exact prefixLift 1449597
  have htrace : WordTrace (prefixWord ++ tailWord_1449597) baseStart_1449597 baseEnd_1449597 := by
    simpa [prefixWord, tailWord_1449597, baseEnd_1449597] using wordTrace_append hprefix tailTrace_1449597
  have hstable : (prefixWord ++ tailWord_1449597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449597).length < 2 ^ (prefixWord ++ tailWord_1449597).sum := by decide
  have hdescent : baseEnd_1449597 < baseStart_1449597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449630 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1449630 : Nat := 118140960795 + 1449630 * 2 ^ 59
def prefixEnd_1449630 : Nat := 4983230072969 + 3 ^ 40 * 1449630 * 2
def baseEnd_1449630 : Nat := 744356961177268549658279

theorem tailTrace_1449630 : CollatzResearch.WordTrace tailWord_1449630 prefixEnd_1449630 744356961177268549658279 := by
  unfold tailWord_1449630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609043717280695242311293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35248233158830374625660229 6609043717280695242311293)
  ·
    refine ⟨2478391393980260715866735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6609043717280695242311293 2478391393980260715866735)
    ·
      refine ⟨3717587090970391073800103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478391393980260715866735 3717587090970391073800103)
      ·
        refine ⟨5576380636455586610700155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717587090970391073800103 5576380636455586610700155)
        ·
          refine ⟨8364570954683379916050233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576380636455586610700155 8364570954683379916050233)
          ·
            refine ⟨6273428216012534937037675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8364570954683379916050233 6273428216012534937037675)
            ·
              refine ⟨9410142324018802405556513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273428216012534937037675 9410142324018802405556513)
              ·
                refine ⟨7057606743014101804167385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9410142324018802405556513 7057606743014101804167385)
                ·
                  refine ⟨5293205057260576353125539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057606743014101804167385 5293205057260576353125539)
                  ·
                    refine ⟨7939807585890864529688309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293205057260576353125539 7939807585890864529688309)
                    ·
                      refine ⟨744356961177268549658279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7939807585890864529688309 744356961177268549658279)
                      ·
                        rfl

theorem cell23_1449630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1449630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449630 prefixEnd_1449630 := by exact prefixLift 1449630
  have htrace : WordTrace (prefixWord ++ tailWord_1449630) baseStart_1449630 baseEnd_1449630 := by
    simpa [prefixWord, tailWord_1449630, baseEnd_1449630] using wordTrace_append hprefix tailTrace_1449630
  have hstable : (prefixWord ++ tailWord_1449630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449630).length < 2 ^ (prefixWord ++ tailWord_1449630).sum := by decide
  have hdescent : baseEnd_1449630 < baseStart_1449630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449631 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1449631 : Nat := 118140960795 + 1449631 * 2 ^ 59
def prefixEnd_1449631 : Nat := 4983230072969 + 3 ^ 40 * 1449631 * 2
def baseEnd_1449631 : Nat := 744357474657923045745775

theorem tailTrace_1449631 : CollatzResearch.WordTrace tailWord_1449631 prefixEnd_1449631 744357474657923045745775 := by
  unfold tailWord_1449631
  simp only [CollatzResearch.WordTrace]
  refine ⟨52872386211241939109276747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35248257474161292739517831 52872386211241939109276747)
  ·
    refine ⟨79308579316862908663915121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52872386211241939109276747 79308579316862908663915121)
    ·
      refine ⟨59481434487647181497936341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79308579316862908663915121 59481434487647181497936341)
      ·
        refine ⟨1394096120804230816357883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59481434487647181497936341 1394096120804230816357883)
        ·
          refine ⟨2091144181206346224536825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394096120804230816357883 2091144181206346224536825)
          ·
            refine ⟨1568358135904759668402619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091144181206346224536825 1568358135904759668402619)
            ·
              refine ⟨2352537203857139502603929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568358135904759668402619 2352537203857139502603929)
              ·
                refine ⟨1764402902892854626952947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352537203857139502603929 1764402902892854626952947)
                ·
                  refine ⟨2646604354339281940429421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764402902892854626952947 2646604354339281940429421)
                  ·
                    refine ⟨992476632877230727661033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646604354339281940429421 992476632877230727661033)
                    ·
                      refine ⟨744357474657923045745775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992476632877230727661033 744357474657923045745775)
                      ·
                        rfl

theorem cell23_1449631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1449631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449631 prefixEnd_1449631 := by exact prefixLift 1449631
  have htrace : WordTrace (prefixWord ++ tailWord_1449631) baseStart_1449631 baseEnd_1449631 := by
    simpa [prefixWord, tailWord_1449631, baseEnd_1449631] using wordTrace_append hprefix tailTrace_1449631
  have hstable : (prefixWord ++ tailWord_1449631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449631).length < 2 ^ (prefixWord ++ tailWord_1449631).sum := by decide
  have hdescent : baseEnd_1449631 < baseStart_1449631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449663 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 2, 5]
def baseStart_1449663 : Nat := 118140960795 + 1449663 * 2 ^ 59
def prefixEnd_1449663 : Nat := 4983230072969 + 3 ^ 40 * 1449663 * 2
def baseEnd_1449663 : Nat := 248124635346288973515209

theorem tailTrace_1449663 : CollatzResearch.WordTrace tailWord_1449663 prefixEnd_1449663 248124635346288973515209 := by
  unfold tailWord_1449663
  simp only [CollatzResearch.WordTrace]
  refine ⟨52873553347126008574441643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35249035564750672382961095 52873553347126008574441643)
  ·
    refine ⟨79310330020689012861662465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52873553347126008574441643 79310330020689012861662465)
    ·
      refine ⟨59482747515516759646246849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79310330020689012861662465 59482747515516759646246849)
      ·
        refine ⟨44612060636637569734685137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59482747515516759646246849 44612060636637569734685137)
        ·
          refine ⟨33459045477478177301013853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44612060636637569734685137 33459045477478177301013853)
          ·
            refine ⟨12547142054054316487880195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33459045477478177301013853 12547142054054316487880195)
            ·
              refine ⟨18820713081081474731820293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547142054054316487880195 18820713081081474731820293)
              ·
                refine ⟨3528883702702776512216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18820713081081474731820293 3528883702702776512216305)
                ·
                  refine ⟨2646662777027082384162229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528883702702776512216305 2646662777027082384162229)
                  ·
                    refine ⟨248124635346288973515209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2646662777027082384162229 248124635346288973515209)
                    ·
                      rfl

theorem cell23_1449663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_1449663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449663 prefixEnd_1449663 := by exact prefixLift 1449663
  have htrace : WordTrace (prefixWord ++ tailWord_1449663) baseStart_1449663 baseEnd_1449663 := by
    simpa [prefixWord, tailWord_1449663, baseEnd_1449663] using wordTrace_append hprefix tailTrace_1449663
  have hstable : (prefixWord ++ tailWord_1449663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449663).length < 2 ^ (prefixWord ++ tailWord_1449663).sum := by decide
  have hdescent : baseEnd_1449663 < baseStart_1449663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449677 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1449677 : Nat := 118140960795 + 1449677 * 2 ^ 59
def prefixEnd_1449677 : Nat := 4983230072969 + 3 ^ 40 * 1449677 * 2
def baseEnd_1449677 : Nat := 744381094768029865770563

theorem tailTrace_1449677 : CollatzResearch.WordTrace tailWord_1449677 prefixEnd_1449677 744381094768029865770563 := by
  unfold tailWord_1449677
  simp only [CollatzResearch.WordTrace]
  refine ⟨52874063969075288965451285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35249375979383525976967523 52874063969075288965451285)
  ·
    refine ⟨2478471748550404170255529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52874063969075288965451285 2478471748550404170255529)
    ·
      refine ⟨1858853811412803127691647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478471748550404170255529 1858853811412803127691647)
      ·
        refine ⟨2788280717119204691537471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858853811412803127691647 2788280717119204691537471)
        ·
          refine ⟨4182421075678807037306207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788280717119204691537471 4182421075678807037306207)
          ·
            refine ⟨6273631613518210555959311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182421075678807037306207 6273631613518210555959311)
            ·
              refine ⟨9410447420277315833938967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273631613518210555959311 9410447420277315833938967)
              ·
                refine ⟨14115671130415973750908451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410447420277315833938967 14115671130415973750908451)
                ·
                  refine ⟨21173506695623960626362677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14115671130415973750908451 21173506695623960626362677)
                  ·
                    refine ⟨1985016252714746308721501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21173506695623960626362677 1985016252714746308721501)
                    ·
                      refine ⟨744381094768029865770563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985016252714746308721501 744381094768029865770563)
                      ·
                        rfl

theorem cell23_1449677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1449677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449677 prefixEnd_1449677 := by exact prefixLift 1449677
  have htrace : WordTrace (prefixWord ++ tailWord_1449677) baseStart_1449677 baseEnd_1449677 := by
    simpa [prefixWord, tailWord_1449677, baseEnd_1449677] using wordTrace_append hprefix tailTrace_1449677
  have hstable : (prefixWord ++ tailWord_1449677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449677).length < 2 ^ (prefixWord ++ tailWord_1449677).sum := by decide
  have hdescent : baseEnd_1449677 < baseStart_1449677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449697 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1449697 : Nat := 118140960795 + 1449697 * 2 ^ 59
def prefixEnd_1449697 : Nat := 4983230072969 + 3 ^ 40 * 1449697 * 2
def baseEnd_1449697 : Nat := 248130454793706595840157

theorem tailTrace_1449697 : CollatzResearch.WordTrace tailWord_1449697 prefixEnd_1449697 248130454793706595840157 := by
  unfold tailWord_1449697
  simp only [CollatzResearch.WordTrace]
  refine ⟨52874793429002832381179345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35249862286001888254119563 52874793429002832381179345)
  ·
    refine ⟨39656095071752124285884509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52874793429002832381179345 39656095071752124285884509)
    ·
      refine ⟨14871035651907046607206691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39656095071752124285884509 14871035651907046607206691)
      ·
        refine ⟨22306553477860569910810037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14871035651907046607206691 22306553477860569910810037)
        ·
          refine ⟨2091239388549428429138441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22306553477860569910810037 2091239388549428429138441)
          ·
            refine ⟨1568429541412071321853831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091239388549428429138441 1568429541412071321853831)
            ·
              refine ⟨2352644312118106982780747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568429541412071321853831 2352644312118106982780747)
              ·
                refine ⟨3528966468177160474171121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352644312118106982780747 3528966468177160474171121)
                ·
                  refine ⟨2646724851132870355628341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3528966468177160474171121 2646724851132870355628341)
                  ·
                    refine ⟨248130454793706595840157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2646724851132870355628341 248130454793706595840157)
                    ·
                      rfl

theorem cell23_1449697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1449697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449697 prefixEnd_1449697 := by exact prefixLift 1449697
  have htrace : WordTrace (prefixWord ++ tailWord_1449697) baseStart_1449697 baseEnd_1449697 := by
    simpa [prefixWord, tailWord_1449697, baseEnd_1449697] using wordTrace_append hprefix tailTrace_1449697
  have hstable : (prefixWord ++ tailWord_1449697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449697).length < 2 ^ (prefixWord ++ tailWord_1449697).sum := by decide
  have hdescent : baseEnd_1449697 < baseStart_1449697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449700 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_1449700 : Nat := 118140960795 + 1449700 * 2 ^ 59
def prefixEnd_1449700 : Nat := 4983230072969 + 3 ^ 40 * 1449700 * 2
def baseEnd_1449700 : Nat := 744392904823083275782957

theorem tailTrace_1449700 : CollatzResearch.WordTrace tailWord_1449700 prefixEnd_1449700 744392904823083275782957 := by
  unfold tailWord_1449700
  simp only [CollatzResearch.WordTrace]
  refine ⟨26437451423995981946769277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35249935231994642595692369 26437451423995981946769277)
  ·
    refine ⟨9914044283998493230038479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26437451423995981946769277 9914044283998493230038479)
    ·
      refine ⟨14871066425997739845057719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914044283998493230038479 14871066425997739845057719)
      ·
        refine ⟨22306599638996609767586579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14871066425997739845057719 22306599638996609767586579)
        ·
          refine ⟨33459899458494914651379869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22306599638996609767586579 33459899458494914651379869)
          ·
            refine ⟨12547462296935592994267451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33459899458494914651379869 12547462296935592994267451)
            ·
              refine ⟨18821193445403389491401177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547462296935592994267451 18821193445403389491401177)
              ·
                refine ⟨14115895084052542118550883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18821193445403389491401177 14115895084052542118550883)
                ·
                  refine ⟨21173842626078813177826325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14115895084052542118550883 21173842626078813177826325)
                  ·
                    refine ⟨992523873097444367710609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21173842626078813177826325 992523873097444367710609)
                    ·
                      refine ⟨744392904823083275782957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992523873097444367710609 744392904823083275782957)
                      ·
                        rfl

theorem cell23_1449700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_1449700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449700 prefixEnd_1449700 := by exact prefixLift 1449700
  have htrace : WordTrace (prefixWord ++ tailWord_1449700) baseStart_1449700 baseEnd_1449700 := by
    simpa [prefixWord, tailWord_1449700, baseEnd_1449700] using wordTrace_append hprefix tailTrace_1449700
  have hstable : (prefixWord ++ tailWord_1449700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449700).length < 2 ^ (prefixWord ++ tailWord_1449700).sum := by decide
  have hdescent : baseEnd_1449700 < baseStart_1449700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449710 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1449710 : Nat := 118140960795 + 1449710 * 2 ^ 59
def prefixEnd_1449710 : Nat := 4983230072969 + 3 ^ 40 * 1449710 * 2
def baseEnd_1449710 : Nat := 248132679876542745552637

theorem tailTrace_1449710 : CollatzResearch.WordTrace tailWord_1449710 prefixEnd_1449710 248132679876542745552637 := by
  unfold tailWord_1449710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609408447244466950175323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35250178385303823734268389 6609408447244466950175323)
  ·
    refine ⟨9914112670866700425262985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609408447244466950175323 9914112670866700425262985)
    ·
      refine ⟨7435584503150025318947239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9914112670866700425262985 7435584503150025318947239)
      ·
        refine ⟨11153376754725037978420859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435584503150025318947239 11153376754725037978420859)
        ·
          refine ⟨16730065132087556967631289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153376754725037978420859 16730065132087556967631289)
          ·
            refine ⟨12547548849065667725723467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16730065132087556967631289 12547548849065667725723467)
            ·
              refine ⟨18821323273598501588585201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547548849065667725723467 18821323273598501588585201)
              ·
                refine ⟨14115992455198876191438901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18821323273598501588585201 14115992455198876191438901)
                ·
                  refine ⟨1323374292674894642947397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14115992455198876191438901 1323374292674894642947397)
                  ·
                    refine ⟨248132679876542745552637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1323374292674894642947397 248132679876542745552637)
                    ·
                      rfl

theorem cell23_1449710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1449710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449710 prefixEnd_1449710 := by exact prefixLift 1449710
  have htrace : WordTrace (prefixWord ++ tailWord_1449710) baseStart_1449710 baseEnd_1449710 := by
    simpa [prefixWord, tailWord_1449710, baseEnd_1449710] using wordTrace_append hprefix tailTrace_1449710
  have hstable : (prefixWord ++ tailWord_1449710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449710).length < 2 ^ (prefixWord ++ tailWord_1449710).sum := by decide
  have hdescent : baseEnd_1449710 < baseStart_1449710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449713 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1449713 : Nat := 118140960795 + 1449713 * 2 ^ 59
def prefixEnd_1449713 : Nat := 4983230072969 + 3 ^ 40 * 1449713 * 2
def baseEnd_1449713 : Nat := 744399580071591724920397

theorem tailTrace_1449713 : CollatzResearch.WordTrace tailWord_1449713 prefixEnd_1449713 744399580071591724920397 := by
  unfold tailWord_1449713
  simp only [CollatzResearch.WordTrace]
  refine ⟨52875376996944867113761793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35250251331296578075841195 52875376996944867113761793)
  ·
    refine ⟨39656532747708650335321345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52875376996944867113761793 39656532747708650335321345)
    ·
      refine ⟨29742399560781487751491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39656532747708650335321345 29742399560781487751491009)
      ·
        refine ⟨22306799670586115813618257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29742399560781487751491009 22306799670586115813618257)
        ·
          refine ⟨16730099752939586860213693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22306799670586115813618257 16730099752939586860213693)
          ·
            refine ⟨6273787407352345072580135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16730099752939586860213693 6273787407352345072580135)
            ·
              refine ⟨9410681111028517608870203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273787407352345072580135 9410681111028517608870203)
              ·
                refine ⟨14116021666542776413305305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410681111028517608870203 14116021666542776413305305)
                ·
                  refine ⟨10587016249907082309978979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14116021666542776413305305 10587016249907082309978979)
                  ·
                    refine ⟨15880524374860623464968469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10587016249907082309978979 15880524374860623464968469)
                    ·
                      refine ⟨744399580071591724920397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15880524374860623464968469 744399580071591724920397)
                      ·
                        rfl

theorem cell23_1449713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1449713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449713 prefixEnd_1449713 := by exact prefixLift 1449713
  have htrace : WordTrace (prefixWord ++ tailWord_1449713) baseStart_1449713 baseEnd_1449713 := by
    simpa [prefixWord, tailWord_1449713, baseEnd_1449713] using wordTrace_append hprefix tailTrace_1449713
  have hstable : (prefixWord ++ tailWord_1449713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449713).length < 2 ^ (prefixWord ++ tailWord_1449713).sum := by decide
  have hdescent : baseEnd_1449713 < baseStart_1449713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449723 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 6]
def baseStart_1449723 : Nat := 118140960795 + 1449723 * 2 ^ 59
def prefixEnd_1449723 : Nat := 4983230072969 + 3 ^ 40 * 1449723 * 2
def baseEnd_1449723 : Nat := 82711634986459631755039

theorem tailTrace_1449723 : CollatzResearch.WordTrace tailWord_1449723 prefixEnd_1449723 82711634986459631755039 := by
  unfold tailWord_1449723
  simp only [CollatzResearch.WordTrace]
  refine ⟨52875741726908638821625823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35250494484605759214417215 52875741726908638821625823)
  ·
    refine ⟨79313612590362958232438735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52875741726908638821625823 79313612590362958232438735)
    ·
      refine ⟨118970418885544437348658103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79313612590362958232438735 118970418885544437348658103)
      ·
        refine ⟨178455628328316656022987155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118970418885544437348658103 178455628328316656022987155)
        ·
          refine ⟨267683442492474984034480733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178455628328316656022987155 267683442492474984034480733)
          ·
            refine ⟨100381290934678119012930275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267683442492474984034480733 100381290934678119012930275)
            ·
              refine ⟨150571936402017178519395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100381290934678119012930275 150571936402017178519395413)
              ·
                refine ⟨1764514879711138810774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 150571936402017178519395413 1764514879711138810774165)
                ·
                  refine ⟨82711634986459631755039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1764514879711138810774165 82711634986459631755039)
                  ·
                    rfl

theorem cell23_1449723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 6].length) (baseStart_1449723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449723 prefixEnd_1449723 := by exact prefixLift 1449723
  have htrace : WordTrace (prefixWord ++ tailWord_1449723) baseStart_1449723 baseEnd_1449723 := by
    simpa [prefixWord, tailWord_1449723, baseEnd_1449723] using wordTrace_append hprefix tailTrace_1449723
  have hstable : (prefixWord ++ tailWord_1449723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449723).length < 2 ^ (prefixWord ++ tailWord_1449723).sum := by decide
  have hdescent : baseEnd_1449723 < baseStart_1449723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449727 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 1, 4]
def baseStart_1449727 : Nat := 118140960795 + 1449727 * 2 ^ 59
def prefixEnd_1449727 : Nat := 4983230072969 + 3 ^ 40 * 1449727 * 2
def baseEnd_1449727 : Nat := 248135589600251556715111

theorem tailTrace_1449727 : CollatzResearch.WordTrace tailWord_1449727 prefixEnd_1449727 248135589600251556715111 := by
  unfold tailWord_1449727
  simp only [CollatzResearch.WordTrace]
  refine ⟨52875887618894147504771435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35250591745929431669847623 52875887618894147504771435)
  ·
    refine ⟨79313831428341221257157153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52875887618894147504771435 79313831428341221257157153)
    ·
      refine ⟨59485373571255915942867865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79313831428341221257157153 59485373571255915942867865)
      ·
        refine ⟨44614030178441936957150899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59485373571255915942867865 44614030178441936957150899)
        ·
          refine ⟨66921045267662905435726349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44614030178441936957150899 66921045267662905435726349)
          ·
            refine ⟨25095391975373589538397381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66921045267662905435726349 25095391975373589538397381)
            ·
              refine ⟨4705385995382548038449509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25095391975373589538397381 4705385995382548038449509)
              ·
                refine ⟨882259874134227757209283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4705385995382548038449509 882259874134227757209283)
                ·
                  refine ⟨1323389811201341635813925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882259874134227757209283 1323389811201341635813925)
                  ·
                    refine ⟨248135589600251556715111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1323389811201341635813925 248135589600251556715111)
                    ·
                      rfl

theorem cell23_1449727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 1, 4].length) (baseStart_1449727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449727 prefixEnd_1449727 := by exact prefixLift 1449727
  have htrace : WordTrace (prefixWord ++ tailWord_1449727) baseStart_1449727 baseEnd_1449727 := by
    simpa [prefixWord, tailWord_1449727, baseEnd_1449727] using wordTrace_append hprefix tailTrace_1449727
  have hstable : (prefixWord ++ tailWord_1449727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449727).length < 2 ^ (prefixWord ++ tailWord_1449727).sum := by decide
  have hdescent : baseEnd_1449727 < baseStart_1449727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449730 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1449730 : Nat := 118140960795 + 1449730 * 2 ^ 59
def prefixEnd_1449730 : Nat := 4983230072969 + 3 ^ 40 * 1449730 * 2
def baseEnd_1449730 : Nat := 744408309242718158407819

theorem tailTrace_1449730 : CollatzResearch.WordTrace tailWord_1449730 prefixEnd_1449730 744408309242718158407819 := by
  unfold tailWord_1449730
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218999259470819754282661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35250664691922186011420429 13218999259470819754282661)
  ·
    refine ⟨2478562361150778703927999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13218999259470819754282661 2478562361150778703927999)
    ·
      refine ⟨3717843541726168055891999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478562361150778703927999 3717843541726168055891999)
      ·
        refine ⟨5576765312589252083837999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717843541726168055891999 5576765312589252083837999)
        ·
          refine ⟨8365147968883878125756999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576765312589252083837999 8365147968883878125756999)
          ·
            refine ⟨12547721953325817188635499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8365147968883878125756999 12547721953325817188635499)
            ·
              refine ⟨18821582929988725782953249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547721953325817188635499 18821582929988725782953249)
              ·
                refine ⟨14116187197491544337214937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18821582929988725782953249 14116187197491544337214937)
                ·
                  refine ⟨10587140398118658252911203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14116187197491544337214937 10587140398118658252911203)
                  ·
                    refine ⟨15880710597177987379366805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10587140398118658252911203 15880710597177987379366805)
                    ·
                      refine ⟨744408309242718158407819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15880710597177987379366805 744408309242718158407819)
                      ·
                        rfl

theorem cell23_1449730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1449730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449730 prefixEnd_1449730 := by exact prefixLift 1449730
  have htrace : WordTrace (prefixWord ++ tailWord_1449730) baseStart_1449730 baseEnd_1449730 := by
    simpa [prefixWord, tailWord_1449730, baseEnd_1449730] using wordTrace_append hprefix tailTrace_1449730
  have hstable : (prefixWord ++ tailWord_1449730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449730).length < 2 ^ (prefixWord ++ tailWord_1449730).sum := by decide
  have hdescent : baseEnd_1449730 < baseStart_1449730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449753 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 7, 5]
def baseStart_1449753 : Nat := 118140960795 + 1449753 * 2 ^ 59
def prefixEnd_1449753 : Nat := 4983230072969 + 3 ^ 40 * 1449753 * 2
def baseEnd_1449753 : Nat := 248140039765923856140071

theorem tailTrace_1449753 : CollatzResearch.WordTrace tailWord_1449753 prefixEnd_1449753 248140039765923856140071 := by
  unfold tailWord_1449753
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876835916799953945217913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35251223944533302630145275 52876835916799953945217913)
  ·
    refine ⟨39657626937599965458913435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52876835916799953945217913 39657626937599965458913435)
    ·
      refine ⟨59486440406399948188370153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39657626937599965458913435 59486440406399948188370153)
      ·
        refine ⟨44614830304799961141277615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59486440406399948188370153 44614830304799961141277615)
        ·
          refine ⟨66922245457199941711916423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44614830304799961141277615 66922245457199941711916423)
          ·
            refine ⟨100383368185799912567874635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66922245457199941711916423 100383368185799912567874635)
            ·
              refine ⟨150575052278699868851811953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100383368185799912567874635 150575052278699868851811953)
              ·
                refine ⟨112931289209024901638858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150575052278699868851811953 112931289209024901638858965)
                ·
                  refine ⟨2646827090836521132160757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112931289209024901638858965 2646827090836521132160757)
                  ·
                    refine ⟨248140039765923856140071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2646827090836521132160757 248140039765923856140071)
                    ·
                      rfl

theorem cell23_1449753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_1449753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449753 prefixEnd_1449753 := by exact prefixLift 1449753
  have htrace : WordTrace (prefixWord ++ tailWord_1449753) baseStart_1449753 baseEnd_1449753 := by
    simpa [prefixWord, tailWord_1449753, baseEnd_1449753] using wordTrace_append hprefix tailTrace_1449753
  have hstable : (prefixWord ++ tailWord_1449753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449753).length < 2 ^ (prefixWord ++ tailWord_1449753).sum := by decide
  have hdescent : baseEnd_1449753 < baseStart_1449753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449777 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_1449777 : Nat := 118140960795 + 1449777 * 2 ^ 59
def prefixEnd_1449777 : Nat := 4983230072969 + 3 ^ 40 * 1449777 * 2
def baseEnd_1449777 : Nat := 744432442833479474520103

theorem tailTrace_1449777 : CollatzResearch.WordTrace tailWord_1449777 prefixEnd_1449777 744432442833479474520103 := by
  unfold tailWord_1449777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877711268713006044091585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35251807512475337362727723 52877711268713006044091585)
  ·
    refine ⟨39658283451534754533068689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52877711268713006044091585 39658283451534754533068689)
    ·
      refine ⟨29743712588651065899801517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39658283451534754533068689 29743712588651065899801517)
      ·
        refine ⟨11153892220744149712425569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29743712588651065899801517 11153892220744149712425569)
        ·
          refine ⟨8365419165558112284319177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153892220744149712425569 8365419165558112284319177)
          ·
            refine ⟨6274064374168584213239383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8365419165558112284319177 6274064374168584213239383)
            ·
              refine ⟨9411096561252876319859075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274064374168584213239383 9411096561252876319859075)
              ·
                refine ⟨14116644841879314479788613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411096561252876319859075 14116644841879314479788613)
                ·
                  refine ⟨2646870907852371464960365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14116644841879314479788613 2646870907852371464960365)
                  ·
                    refine ⟨992576590444639299360137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2646870907852371464960365 992576590444639299360137)
                    ·
                      refine ⟨744432442833479474520103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992576590444639299360137 744432442833479474520103)
                      ·
                        rfl

theorem cell23_1449777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_1449777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449777 prefixEnd_1449777 := by exact prefixLift 1449777
  have htrace : WordTrace (prefixWord ++ tailWord_1449777) baseStart_1449777 baseEnd_1449777 := by
    simpa [prefixWord, tailWord_1449777, baseEnd_1449777] using wordTrace_append hprefix tailTrace_1449777
  have hstable : (prefixWord ++ tailWord_1449777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449777).length < 2 ^ (prefixWord ++ tailWord_1449777).sum := by decide
  have hdescent : baseEnd_1449777 < baseStart_1449777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449783 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 6]
def baseStart_1449783 : Nat := 118140960795 + 1449783 * 2 ^ 59
def prefixEnd_1449783 : Nat := 4983230072969 + 3 ^ 40 * 1449783 * 2
def baseEnd_1449783 : Nat := 248145174572468817015025

theorem tailTrace_1449783 : CollatzResearch.WordTrace tailWord_1449783 prefixEnd_1449783 248145174572468817015025 := by
  unfold tailWord_1449783
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877930106691269068810003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35251953404460846045873335 52877930106691269068810003)
  ·
    refine ⟨79316895160036903603215005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52877930106691269068810003 79316895160036903603215005)
    ·
      refine ⟨29743835685013838851205627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79316895160036903603215005 29743835685013838851205627)
      ·
        refine ⟨44615753527520758276808441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29743835685013838851205627 44615753527520758276808441)
        ·
          refine ⟨33461815145640568707606331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44615753527520758276808441 33461815145640568707606331)
          ·
            refine ⟨50192722718460853061409497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33461815145640568707606331 50192722718460853061409497)
            ·
              refine ⟨37644542038845639796057123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50192722718460853061409497 37644542038845639796057123)
              ·
                refine ⟨56466813058268459694085685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37644542038845639796057123 56466813058268459694085685)
                ·
                  refine ⟨5293763724212668096320533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56466813058268459694085685 5293763724212668096320533)
                  ·
                    refine ⟨248145174572468817015025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5293763724212668096320533 248145174572468817015025)
                    ·
                      rfl

theorem cell23_1449783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_1449783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449783 prefixEnd_1449783 := by exact prefixLift 1449783
  have htrace : WordTrace (prefixWord ++ tailWord_1449783) baseStart_1449783 baseEnd_1449783 := by
    simpa [prefixWord, tailWord_1449783, baseEnd_1449783] using wordTrace_append hprefix tailTrace_1449783
  have hstable : (prefixWord ++ tailWord_1449783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449783).length < 2 ^ (prefixWord ++ tailWord_1449783).sum := by decide
  have hdescent : baseEnd_1449783 < baseStart_1449783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449784 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1449784 : Nat := 118140960795 + 1449784 * 2 ^ 59
def prefixEnd_1449784 : Nat := 4983230072969 + 3 ^ 40 * 1449784 * 2
def baseEnd_1449784 : Nat := 744436037198060947132571

theorem tailTrace_1449784 : CollatzResearch.WordTrace tailWord_1449784 prefixEnd_1449784 744436037198060947132571 := by
  unfold tailWord_1449784
  simp only [CollatzResearch.WordTrace]
  refine ⟨26438983289843823119798203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35251977719791764159730937 26438983289843823119798203)
  ·
    refine ⟨39658474934765734679697305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26438983289843823119798203 39658474934765734679697305)
    ·
      refine ⟨29743856201074301009772979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39658474934765734679697305 29743856201074301009772979)
      ·
        refine ⟨44615784301611451514659469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29743856201074301009772979 44615784301611451514659469)
        ·
          refine ⟨16730919113104294317997301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44615784301611451514659469 16730919113104294317997301)
          ·
            refine ⟨1568523666853527592312247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16730919113104294317997301 1568523666853527592312247)
            ·
              refine ⟨2352785500280291388468371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568523666853527592312247 2352785500280291388468371)
              ·
                refine ⟨3529178250420437082702557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352785500280291388468371 3529178250420437082702557)
                ·
                  refine ⟨1323441843907663906013459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3529178250420437082702557 1323441843907663906013459)
                  ·
                    refine ⟨1985162765861495859020189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1323441843907663906013459 1985162765861495859020189)
                    ·
                      refine ⟨744436037198060947132571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985162765861495859020189 744436037198060947132571)
                      ·
                        rfl

theorem cell23_1449784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1449784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449784 prefixEnd_1449784 := by exact prefixLift 1449784
  have htrace : WordTrace (prefixWord ++ tailWord_1449784) baseStart_1449784 baseEnd_1449784 := by
    simpa [prefixWord, tailWord_1449784, baseEnd_1449784] using wordTrace_append hprefix tailTrace_1449784
  have hstable : (prefixWord ++ tailWord_1449784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449784).length < 2 ^ (prefixWord ++ tailWord_1449784).sum := by decide
  have hdescent : baseEnd_1449784 < baseStart_1449784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449804 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_1449804 : Nat := 118140960795 + 1449804 * 2 ^ 59
def prefixEnd_1449804 : Nat := 4983230072969 + 3 ^ 40 * 1449804 * 2
def baseEnd_1449804 : Nat := 248148768937050289627493

theorem tailTrace_1449804 : CollatzResearch.WordTrace tailWord_1449804 prefixEnd_1449804 248148768937050289627493 := by
  unfold tailWord_1449804
  simp only [CollatzResearch.WordTrace]
  refine ⟨26439348019807594827662233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35252464026410126436882977 26439348019807594827662233)
  ·
    refine ⟨19829511014855696120746675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26439348019807594827662233 19829511014855696120746675)
    ·
      refine ⟨29744266522283544181120013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19829511014855696120746675 29744266522283544181120013)
      ·
        refine ⟨11154099945856329067920005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29744266522283544181120013 11154099945856329067920005)
        ·
          refine ⟨2091393739848061700235001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11154099945856329067920005 2091393739848061700235001)
          ·
            refine ⟨1568545304886046275176251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091393739848061700235001 1568545304886046275176251)
            ·
              refine ⟨2352817957329069412764377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568545304886046275176251 2352817957329069412764377)
              ·
                refine ⟨1764613467996802059573283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352817957329069412764377 1764613467996802059573283)
                ·
                  refine ⟨2646920201995203089359925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764613467996802059573283 2646920201995203089359925)
                  ·
                    refine ⟨248148768937050289627493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2646920201995203089359925 248148768937050289627493)
                    ·
                      rfl

theorem cell23_1449804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_1449804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449804 prefixEnd_1449804 := by exact prefixLift 1449804
  have htrace : WordTrace (prefixWord ++ tailWord_1449804) baseStart_1449804 baseEnd_1449804 := by
    simpa [prefixWord, tailWord_1449804, baseEnd_1449804] using wordTrace_append hprefix tailTrace_1449804
  have hstable : (prefixWord ++ tailWord_1449804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449804).length < 2 ^ (prefixWord ++ tailWord_1449804).sum := by decide
  have hdescent : baseEnd_1449804 < baseStart_1449804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449824 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4]
def baseStart_1449824 : Nat := 118140960795 + 1449824 * 2 ^ 59
def prefixEnd_1449824 : Nat := 4983230072969 + 3 ^ 40 * 1449824 * 2
def baseEnd_1449824 : Nat := 744456576424240790632387

theorem tailTrace_1449824 : CollatzResearch.WordTrace tailWord_1449824 prefixEnd_1449824 744456576424240790632387 := by
  unfold tailWord_1449824
  simp only [CollatzResearch.WordTrace]
  refine ⟨26439712749771366535526263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35252950333028488714035017 26439712749771366535526263)
  ·
    refine ⟨39659569124657049803289395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26439712749771366535526263 39659569124657049803289395)
    ·
      refine ⟨59489353686985574704934093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39659569124657049803289395 59489353686985574704934093)
      ·
        refine ⟨22308507632619590514350285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59489353686985574704934093 22308507632619590514350285)
        ·
          refine ⟨8365690362232346442881357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22308507632619590514350285 8365690362232346442881357)
          ·
            refine ⟨3137133885837129916080509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8365690362232346442881357 3137133885837129916080509)
            ·
              refine ⟨1176425207188923718530191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3137133885837129916080509 1176425207188923718530191)
              ·
                refine ⟨1764637810783385577795287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176425207188923718530191 1764637810783385577795287)
                ·
                  refine ⟨2646956716175078366692931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764637810783385577795287 2646956716175078366692931)
                  ·
                    refine ⟨3970435074262617550039397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2646956716175078366692931 3970435074262617550039397)
                    ·
                      refine ⟨744456576424240790632387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3970435074262617550039397 744456576424240790632387)
                      ·
                        rfl

theorem cell23_1449824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_1449824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449824 prefixEnd_1449824 := by exact prefixLift 1449824
  have htrace : WordTrace (prefixWord ++ tailWord_1449824) baseStart_1449824 baseEnd_1449824 := by
    simpa [prefixWord, tailWord_1449824, baseEnd_1449824] using wordTrace_append hprefix tailTrace_1449824
  have hstable : (prefixWord ++ tailWord_1449824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449824).length < 2 ^ (prefixWord ++ tailWord_1449824).sum := by decide
  have hdescent : baseEnd_1449824 < baseStart_1449824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449840 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_1449840 : Nat := 118140960795 + 1449840 * 2 ^ 59
def prefixEnd_1449840 : Nat := 4983230072969 + 3 ^ 40 * 1449840 * 2
def baseEnd_1449840 : Nat := 744464792114712728032313

theorem tailTrace_1449840 : CollatzResearch.WordTrace tailWord_1449840 prefixEnd_1449840 744464792114712728032313 := by
  unfold tailWord_1449840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26440004533742383901817487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35253339378323178535756649 26440004533742383901817487)
  ·
    refine ⟨39660006800613575852726231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26440004533742383901817487 39660006800613575852726231)
    ·
      refine ⟨59490010200920363779089347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39660006800613575852726231 59490010200920363779089347)
      ·
        refine ⟨89235015301380545668634021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59490010200920363779089347 89235015301380545668634021)
        ·
          refine ⟨16731565369008852312868879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89235015301380545668634021 16731565369008852312868879)
          ·
            refine ⟨25097348053513278469303319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731565369008852312868879 25097348053513278469303319)
            ·
              refine ⟨37646022080269917703954979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25097348053513278469303319 37646022080269917703954979)
              ·
                refine ⟨56469033120404876555932469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37646022080269917703954979 56469033120404876555932469)
                ·
                  refine ⟨5293971855037957177118669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56469033120404876555932469 5293971855037957177118669)
                  ·
                    refine ⟨1985239445639233941419501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5293971855037957177118669 1985239445639233941419501)
                    ·
                      refine ⟨744464792114712728032313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985239445639233941419501 744464792114712728032313)
                      ·
                        rfl

theorem cell23_1449840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_1449840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449840 prefixEnd_1449840 := by exact prefixLift 1449840
  have htrace : WordTrace (prefixWord ++ tailWord_1449840) baseStart_1449840 baseEnd_1449840 := by
    simpa [prefixWord, tailWord_1449840, baseEnd_1449840] using wordTrace_append hprefix tailTrace_1449840
  have hstable : (prefixWord ++ tailWord_1449840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449840).length < 2 ^ (prefixWord ++ tailWord_1449840).sum := by decide
  have hdescent : baseEnd_1449840 < baseStart_1449840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449841 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_1449841 : Nat := 118140960795 + 1449841 * 2 ^ 59
def prefixEnd_1449841 : Nat := 4983230072969 + 3 ^ 40 * 1449841 * 2
def baseEnd_1449841 : Nat := 744465305595367224119809

theorem tailTrace_1449841 : CollatzResearch.WordTrace tailWord_1449841 prefixEnd_1449841 744465305595367224119809 := by
  unfold tailWord_1449841
  simp only [CollatzResearch.WordTrace]
  refine ⟨52880045540481144974421377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35253363693654096649614251 52880045540481144974421377)
  ·
    refine ⟨39660034155360858730816033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52880045540481144974421377 39660034155360858730816033)
    ·
      refine ⟨29745025616520644048112025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39660034155360858730816033 29745025616520644048112025)
      ·
        refine ⟨22308769212390483036084019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29745025616520644048112025 22308769212390483036084019)
        ·
          refine ⟨33463153818585724554126029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22308769212390483036084019 33463153818585724554126029)
          ·
            refine ⟨12548682681969646707797261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33463153818585724554126029 12548682681969646707797261)
            ·
              refine ⟨4705756005738617515423973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12548682681969646707797261 4705756005738617515423973)
              ·
                refine ⟨882329251075990784141995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4705756005738617515423973 882329251075990784141995)
                ·
                  refine ⟨1323493876613986176212993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882329251075990784141995 1323493876613986176212993)
                  ·
                    refine ⟨992620407460489632159745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323493876613986176212993 992620407460489632159745)
                    ·
                      refine ⟨744465305595367224119809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992620407460489632159745 744465305595367224119809)
                      ·
                        rfl

theorem cell23_1449841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_1449841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449841 prefixEnd_1449841 := by exact prefixLift 1449841
  have htrace : WordTrace (prefixWord ++ tailWord_1449841) baseStart_1449841 baseEnd_1449841 := by
    simpa [prefixWord, tailWord_1449841, baseEnd_1449841] using wordTrace_append hprefix tailTrace_1449841
  have hstable : (prefixWord ++ tailWord_1449841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449841).length < 2 ^ (prefixWord ++ tailWord_1449841).sum := by decide
  have hdescent : baseEnd_1449841 < baseStart_1449841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449854 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1449854 : Nat := 118140960795 + 1449854 * 2 ^ 59
def prefixEnd_1449854 : Nat := 4983230072969 + 3 ^ 40 * 1449854 * 2
def baseEnd_1449854 : Nat := 744471980843875673257249

theorem tailTrace_1449854 : CollatzResearch.WordTrace tailWord_1449854 prefixEnd_1449854 744471980843875673257249 := by
  unfold tailWord_1449854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610064961179256024330577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35253679792956032129763077 6610064961179256024330577)
  ·
    refine ⟨4957548720884442018247933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6610064961179256024330577 4957548720884442018247933)
    ·
      refine ⟨1859080770331665756842975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4957548720884442018247933 1859080770331665756842975)
      ·
        refine ⟨2788621155497498635264463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859080770331665756842975 2788621155497498635264463)
        ·
          refine ⟨4182931733246247952896695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788621155497498635264463 4182931733246247952896695)
          ·
            refine ⟨6274397599869371929345043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182931733246247952896695 6274397599869371929345043)
            ·
              refine ⟨9411596399804057894017565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274397599869371929345043 9411596399804057894017565)
              ·
                refine ⟨3529348649926521710256587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9411596399804057894017565 3529348649926521710256587)
                ·
                  refine ⟨5294022974889782565384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529348649926521710256587 5294022974889782565384881)
                  ·
                    refine ⟨3970517231167336924038661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5294022974889782565384881 3970517231167336924038661)
                    ·
                      refine ⟨744471980843875673257249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3970517231167336924038661 744471980843875673257249)
                      ·
                        rfl

theorem cell23_1449854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1449854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449854 prefixEnd_1449854 := by exact prefixLift 1449854
  have htrace : WordTrace (prefixWord ++ tailWord_1449854) baseStart_1449854 baseEnd_1449854 := by
    simpa [prefixWord, tailWord_1449854, baseEnd_1449854] using wordTrace_append hprefix tailTrace_1449854
  have hstable : (prefixWord ++ tailWord_1449854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449854).length < 2 ^ (prefixWord ++ tailWord_1449854).sum := by decide
  have hdescent : baseEnd_1449854 < baseStart_1449854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449874 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1449874 : Nat := 118140960795 + 1449874 * 2 ^ 59
def prefixEnd_1449874 : Nat := 4983230072969 + 3 ^ 40 * 1449874 * 2
def baseEnd_1449874 : Nat := 744482250456965595007157

theorem tailTrace_1449874 : CollatzResearch.WordTrace tailWord_1449874 prefixEnd_1449874 744482250456965595007157 := by
  unfold tailWord_1449874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13220312287340397902593169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35254166099574394406915117 13220312287340397902593169)
  ·
    refine ⟨9915234215505298426944877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13220312287340397902593169 9915234215505298426944877)
    ·
      refine ⟨3718212830814486910104329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9915234215505298426944877 3718212830814486910104329)
      ·
        refine ⟨2788659623110865182578247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3718212830814486910104329 2788659623110865182578247)
        ·
          refine ⟨4182989434666297773867371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788659623110865182578247 4182989434666297773867371)
          ·
            refine ⟨6274484151999446660801057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182989434666297773867371 6274484151999446660801057)
            ·
              refine ⟨4705863113999584995600793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274484151999446660801057 4705863113999584995600793)
              ·
                refine ⟨3529397335499688746700595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705863113999584995600793 3529397335499688746700595)
                ·
                  refine ⟨5294096003249533120050893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529397335499688746700595 5294096003249533120050893)
                  ·
                    refine ⟨1985286001218574920019085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5294096003249533120050893 1985286001218574920019085)
                    ·
                      refine ⟨744482250456965595007157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985286001218574920019085 744482250456965595007157)
                      ·
                        rfl

theorem cell23_1449874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1449874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449874 prefixEnd_1449874 := by exact prefixLift 1449874
  have htrace : WordTrace (prefixWord ++ tailWord_1449874) baseStart_1449874 baseEnd_1449874 := by
    simpa [prefixWord, tailWord_1449874, baseEnd_1449874] using wordTrace_append hprefix tailTrace_1449874
  have hstable : (prefixWord ++ tailWord_1449874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449874).length < 2 ^ (prefixWord ++ tailWord_1449874).sum := by decide
  have hdescent : baseEnd_1449874 < baseStart_1449874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449908 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1449908 : Nat := 118140960795 + 1449908 * 2 ^ 59
def prefixEnd_1449908 : Nat := 4983230072969 + 3 ^ 40 * 1449908 * 2
def baseEnd_1449908 : Nat := 744499708799218461982001

theorem tailTrace_1449908 : CollatzResearch.WordTrace tailWord_1449908 prefixEnd_1449908 744499708799218461982001 := by
  unfold tailWord_1449908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26441244615619207708555189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35254992820825610278073585 26441244615619207708555189)
  ·
    refine ⟨2478866682714300722677049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26441244615619207708555189 2478866682714300722677049)
    ·
      refine ⟨1859150012035725542007787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478866682714300722677049 1859150012035725542007787)
      ·
        refine ⟨2788725018053588313011681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859150012035725542007787 2788725018053588313011681)
        ·
          refine ⟨2091543763540191234758761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788725018053588313011681 2091543763540191234758761)
          ·
            refine ⟨1568657822655143426069071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091543763540191234758761 1568657822655143426069071)
            ·
              refine ⟨2352986733982715139103607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568657822655143426069071 2352986733982715139103607)
              ·
                refine ⟨3529480100974072708655411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352986733982715139103607 3529480100974072708655411)
                ·
                  refine ⟨5294220151461109062983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529480100974072708655411 5294220151461109062983117)
                  ·
                    refine ⟨1985332556797915898618669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5294220151461109062983117 1985332556797915898618669)
                    ·
                      refine ⟨744499708799218461982001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985332556797915898618669 744499708799218461982001)
                      ·
                        rfl

theorem cell23_1449908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1449908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449908 prefixEnd_1449908 := by exact prefixLift 1449908
  have htrace : WordTrace (prefixWord ++ tailWord_1449908) baseStart_1449908 baseEnd_1449908 := by
    simpa [prefixWord, tailWord_1449908, baseEnd_1449908] using wordTrace_append hprefix tailTrace_1449908
  have hstable : (prefixWord ++ tailWord_1449908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449908).length < 2 ^ (prefixWord ++ tailWord_1449908).sum := by decide
  have hdescent : baseEnd_1449908 < baseStart_1449908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449920 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 7]
def baseStart_1449920 : Nat := 118140960795 + 1449920 * 2 ^ 59
def prefixEnd_1449920 : Nat := 4983230072969 + 3 ^ 40 * 1449920 * 2
def baseEnd_1449920 : Nat := 82722874507452490559105

theorem tailTrace_1449920 : CollatzResearch.WordTrace tailWord_1449920 prefixEnd_1449920 82722874507452490559105 := by
  unfold tailWord_1449920
  simp only [CollatzResearch.WordTrace]
  refine ⟨26441463453597470733273607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35255284604796627644364809 26441463453597470733273607)
  ·
    refine ⟨39662195180396206099910411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26441463453597470733273607 39662195180396206099910411)
    ·
      refine ⟨59493292770594309149865617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39662195180396206099910411 59493292770594309149865617)
      ·
        refine ⟨44619969577945731862399213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59493292770594309149865617 44619969577945731862399213)
        ·
          refine ⟨16732488591729649448399705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44619969577945731862399213 16732488591729649448399705)
          ·
            refine ⟨12549366443797237086299779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16732488591729649448399705 12549366443797237086299779)
            ·
              refine ⟨18824049665695855629449669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12549366443797237086299779 18824049665695855629449669)
              ·
                refine ⟨3529509312317972930521813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18824049665695855629449669 3529509312317972930521813)
                ·
                  refine ⟨82722874507452490559105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3529509312317972930521813 82722874507452490559105)
                  ·
                    rfl

theorem cell23_1449920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_1449920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449920 prefixEnd_1449920 := by exact prefixLift 1449920
  have htrace : WordTrace (prefixWord ++ tailWord_1449920) baseStart_1449920 baseEnd_1449920 := by
    simpa [prefixWord, tailWord_1449920, baseEnd_1449920] using wordTrace_append hprefix tailTrace_1449920
  have hstable : (prefixWord ++ tailWord_1449920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449920).length < 2 ^ (prefixWord ++ tailWord_1449920).sum := by decide
  have hdescent : baseEnd_1449920 < baseStart_1449920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449937 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 5]
def baseStart_1449937 : Nat := 118140960795 + 1449937 * 2 ^ 59
def prefixEnd_1449937 : Nat := 4983230072969 + 3 ^ 40 * 1449937 * 2
def baseEnd_1449937 : Nat := 82723844415355427613263

theorem tailTrace_1449937 : CollatzResearch.WordTrace tailWord_1449937 prefixEnd_1449937 82723844415355427613263 := by
  unfold tailWord_1449937
  simp only [CollatzResearch.WordTrace]
  refine ⟨52883546948133353369916065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35255697965422235579944043 52883546948133353369916065)
  ·
    refine ⟨39662660211100015027437049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52883546948133353369916065 39662660211100015027437049)
    ·
      refine ⟨29746995158325011270577787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39662660211100015027437049 29746995158325011270577787)
      ·
        refine ⟨44620492737487516905866681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29746995158325011270577787 44620492737487516905866681)
        ·
          refine ⟨33465369553115637679400011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44620492737487516905866681 33465369553115637679400011)
          ·
            refine ⟨50198054329673456519100017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33465369553115637679400011 50198054329673456519100017)
            ·
              refine ⟨37648540747255092389325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50198054329673456519100017 37648540747255092389325013)
              ·
                refine ⟨882387673763791227874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37648540747255092389325013 882387673763791227874805)
                ·
                  refine ⟨82723844415355427613263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882387673763791227874805 82723844415355427613263)
                  ·
                    rfl

theorem cell23_1449937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 5].length) (baseStart_1449937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449937 prefixEnd_1449937 := by exact prefixLift 1449937
  have htrace : WordTrace (prefixWord ++ tailWord_1449937) baseStart_1449937 baseEnd_1449937 := by
    simpa [prefixWord, tailWord_1449937, baseEnd_1449937] using wordTrace_append hprefix tailTrace_1449937
  have hstable : (prefixWord ++ tailWord_1449937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449937).length < 2 ^ (prefixWord ++ tailWord_1449937).sum := by decide
  have hdescent : baseEnd_1449937 < baseStart_1449937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449965 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1449965 : Nat := 118140960795 + 1449965 * 2 ^ 59
def prefixEnd_1449965 : Nat := 4983230072969 + 3 ^ 40 * 1449965 * 2
def baseEnd_1449965 : Nat := 744528977196524738969239

theorem tailTrace_1449965 : CollatzResearch.WordTrace tailWord_1449965 prefixEnd_1449965 744528977196524738969239 := by
  unfold tailWord_1449965
  simp only [CollatzResearch.WordTrace]
  refine ⟨52884568192031914151935349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35256378794687942767956899 52884568192031914151935349)
  ·
    refine ⟨4957928268002991951743939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52884568192031914151935349 4957928268002991951743939)
    ·
      refine ⟨7436892402004487927615909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4957928268002991951743939 7436892402004487927615909)
      ·
        refine ⟨1394417325375841486427983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7436892402004487927615909 1394417325375841486427983)
        ·
          refine ⟨2091625988063762229641975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394417325375841486427983 2091625988063762229641975)
          ·
            refine ⟨3137438982095643344462963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091625988063762229641975 3137438982095643344462963)
            ·
              refine ⟨4706158473143465016694445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137438982095643344462963 4706158473143465016694445)
              ·
                refine ⟨1764809427428799381260417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706158473143465016694445 1764809427428799381260417)
                ·
                  refine ⟨1323607070571599535945313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1764809427428799381260417 1323607070571599535945313)
                  ·
                    refine ⟨992705302928699651958985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323607070571599535945313 992705302928699651958985)
                    ·
                      refine ⟨744528977196524738969239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992705302928699651958985 744528977196524738969239)
                      ·
                        rfl

theorem cell23_1449965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1449965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1449965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1449965 prefixEnd_1449965 := by exact prefixLift 1449965
  have htrace : WordTrace (prefixWord ++ tailWord_1449965) baseStart_1449965 baseEnd_1449965 := by
    simpa [prefixWord, tailWord_1449965, baseEnd_1449965] using wordTrace_append hprefix tailTrace_1449965
  have hstable : (prefixWord ++ tailWord_1449965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449965).length < 2 ^ (prefixWord ++ tailWord_1449965).sum := by decide
  have hdescent : baseEnd_1449965 < baseStart_1449965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450000 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_1450000 : Nat := 118140960795 + 1450000 * 2 ^ 59
def prefixEnd_1450000 : Nat := 4983230072969 + 3 ^ 40 * 1450000 * 2
def baseEnd_1450000 : Nat := 744546949019432102031577

theorem tailTrace_1450000 : CollatzResearch.WordTrace tailWord_1450000 prefixEnd_1450000 744546949019432102031577 := by
  unfold tailWord_1450000
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442922373452557564729727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35257229831270076752972969 26442922373452557564729727)
  ·
    refine ⟨39664383560178836347094591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26442922373452557564729727 39664383560178836347094591)
    ·
      refine ⟨59496575340268254520641887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39664383560178836347094591 59496575340268254520641887)
      ·
        refine ⟨89244863010402381780962831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59496575340268254520641887 89244863010402381780962831)
        ·
          refine ⟨133867294515603572671444247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89244863010402381780962831 133867294515603572671444247)
          ·
            refine ⟨200800941773405359007166371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133867294515603572671444247 200800941773405359007166371)
            ·
              refine ⟨301201412660108038510749557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200800941773405359007166371 301201412660108038510749557)
              ·
                refine ⟨28237632436885128610382771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301201412660108038510749557 28237632436885128610382771)
                ·
                  refine ⟨42356448655327692915574157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28237632436885128610382771 42356448655327692915574157)
                  ·
                    refine ⟨15883668245747884843340309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42356448655327692915574157 15883668245747884843340309)
                    ·
                      refine ⟨744546949019432102031577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15883668245747884843340309 744546949019432102031577)
                      ·
                        rfl

theorem cell23_1450000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_1450000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450000 prefixEnd_1450000 := by exact prefixLift 1450000
  have htrace : WordTrace (prefixWord ++ tailWord_1450000) baseStart_1450000 baseEnd_1450000 := by
    simpa [prefixWord, tailWord_1450000, baseEnd_1450000] using wordTrace_append hprefix tailTrace_1450000
  have hstable : (prefixWord ++ tailWord_1450000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450000).length < 2 ^ (prefixWord ++ tailWord_1450000).sum := by decide
  have hdescent : baseEnd_1450000 < baseStart_1450000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450097 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1450097 : Nat := 118140960795 + 1450097 * 2 ^ 59
def prefixEnd_1450097 : Nat := 4983230072969 + 3 ^ 40 * 1450097 * 2
def baseEnd_1450097 : Nat := 744596756642918222518631

theorem tailTrace_1450097 : CollatzResearch.WordTrace tailWord_1450097 prefixEnd_1450097 744596756642918222518631 := by
  unfold tailWord_1450097
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889382627553700695740545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35259588418369133797160363 52889382627553700695740545)
  ·
    refine ⟨39667036970665275521805409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52889382627553700695740545 39667036970665275521805409)
    ·
      refine ⟨29750277727998956641354057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39667036970665275521805409 29750277727998956641354057)
      ·
        refine ⟨22312708295999217481015543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29750277727998956641354057 22312708295999217481015543)
        ·
          refine ⟨33469062443998826221523315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312708295999217481015543 33469062443998826221523315)
          ·
            refine ⟨50203593665998239332284973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33469062443998826221523315 50203593665998239332284973)
            ·
              refine ⟨18826347624749339749606865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50203593665998239332284973 18826347624749339749606865)
              ·
                refine ⟨14119760718562004812205149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18826347624749339749606865 14119760718562004812205149)
                ·
                  refine ⟨5294910269460751804576931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14119760718562004812205149 5294910269460751804576931)
                  ·
                    refine ⟨7942365404191127706865397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294910269460751804576931 7942365404191127706865397)
                    ·
                      refine ⟨744596756642918222518631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7942365404191127706865397 744596756642918222518631)
                      ·
                        rfl

theorem cell23_1450097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1450097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450097 prefixEnd_1450097 := by exact prefixLift 1450097
  have htrace : WordTrace (prefixWord ++ tailWord_1450097) baseStart_1450097 baseEnd_1450097 := by
    simpa [prefixWord, tailWord_1450097, baseEnd_1450097] using wordTrace_append hprefix tailTrace_1450097
  have hstable : (prefixWord ++ tailWord_1450097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450097).length < 2 ^ (prefixWord ++ tailWord_1450097).sum := by decide
  have hdescent : baseEnd_1450097 < baseStart_1450097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450105 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 1, 1, 3]
def baseStart_1450105 : Nat := 118140960795 + 1450105 * 2 ^ 59
def prefixEnd_1450105 : Nat := 4983230072969 + 3 ^ 40 * 1450105 * 2
def baseEnd_1450105 : Nat := 744600864488154191218595

theorem tailTrace_1450105 : CollatzResearch.WordTrace tailWord_1450105 prefixEnd_1450105 744600864488154191218595 := by
  unfold tailWord_1450105
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889674411524718062031769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35259782941016478708021179 52889674411524718062031769)
  ·
    refine ⟨39667255808643538546523827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52889674411524718062031769 39667255808643538546523827)
    ·
      refine ⟨59500883712965307819785741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39667255808643538546523827 59500883712965307819785741)
      ·
        refine ⟨22312831392361990432419653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59500883712965307819785741 22312831392361990432419653)
        ·
          refine ⟨4183655886067873206078685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22312831392361990432419653 4183655886067873206078685)
          ·
            refine ⟨1568870957275452452279507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4183655886067873206078685 1568870957275452452279507)
            ·
              refine ⟨2353306435913178678419261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568870957275452452279507 2353306435913178678419261)
              ·
                refine ⟨882489913467442004407223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353306435913178678419261 882489913467442004407223)
                ·
                  refine ⟨1323734870201163006610835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882489913467442004407223 1323734870201163006610835)
                  ·
                    refine ⟨1985602305301744509916253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1323734870201163006610835 1985602305301744509916253)
                    ·
                      refine ⟨744600864488154191218595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985602305301744509916253 744600864488154191218595)
                      ·
                        rfl

theorem cell23_1450105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_1450105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450105 prefixEnd_1450105 := by exact prefixLift 1450105
  have htrace : WordTrace (prefixWord ++ tailWord_1450105) baseStart_1450105 baseEnd_1450105 := by
    simpa [prefixWord, tailWord_1450105, baseEnd_1450105] using wordTrace_append hprefix tailTrace_1450105
  have hstable : (prefixWord ++ tailWord_1450105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450105).length < 2 ^ (prefixWord ++ tailWord_1450105).sum := by decide
  have hdescent : baseEnd_1450105 < baseStart_1450105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450117 : List Nat := [1, 3, 1, 1, 5, 1, 11]
def baseStart_1450117 : Nat := 118140960795 + 1450117 * 2 ^ 59
def prefixEnd_1450117 : Nat := 4983230072969 + 3 ^ 40 * 1450117 * 2
def baseEnd_1450117 : Nat := 9192679336493927707019

theorem tailTrace_1450117 : CollatzResearch.WordTrace tailWord_1450117 prefixEnd_1450117 9192679336493927707019 := by
  unfold tailWord_1450117
  simp only [CollatzResearch.WordTrace]
  refine ⟨52890112087481244111468605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35260074724987496074312403 52890112087481244111468605)
  ·
    refine ⟨19833792032805466541800727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52890112087481244111468605 19833792032805466541800727)
    ·
      refine ⟨29750688049208199812701091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19833792032805466541800727 29750688049208199812701091)
      ·
        refine ⟨44626032073812299719051637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29750688049208199812701091 44626032073812299719051637)
        ·
          refine ⟨4183690506919903098661091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44626032073812299719051637 4183690506919903098661091)
          ·
            refine ⟨6275535760379854647991637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183690506919903098661091 6275535760379854647991637)
            ·
              refine ⟨9192679336493927707019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6275535760379854647991637 9192679336493927707019)
              ·
                rfl

theorem cell23_1450117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 11].length) (baseStart_1450117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450117 prefixEnd_1450117 := by exact prefixLift 1450117
  have htrace : WordTrace (prefixWord ++ tailWord_1450117) baseStart_1450117 baseEnd_1450117 := by
    simpa [prefixWord, tailWord_1450117, baseEnd_1450117] using wordTrace_append hprefix tailTrace_1450117
  have hstable : (prefixWord ++ tailWord_1450117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450117).length < 2 ^ (prefixWord ++ tailWord_1450117).sum := by decide
  have hdescent : baseEnd_1450117 < baseStart_1450117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450138 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_1450138 : Nat := 118140960795 + 1450138 * 2 ^ 59
def prefixEnd_1450138 : Nat := 4983230072969 + 3 ^ 40 * 1450138 * 2
def baseEnd_1450138 : Nat := 248205936449917520701981

theorem tailTrace_1450138 : CollatzResearch.WordTrace tailWord_1450138 prefixEnd_1450138 248205936449917520701981 := by
  unfold tailWord_1450138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222719505101291174495767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35260585346936776465322045 13222719505101291174495767)
  ·
    refine ⟨19834079257651936761743651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13222719505101291174495767 19834079257651936761743651)
    ·
      refine ⟨29751118886477905142615477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19834079257651936761743651 29751118886477905142615477)
      ·
        refine ⟨2789167395607303607120201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29751118886477905142615477 2789167395607303607120201)
        ·
          refine ⟨2091875546705477705340151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789167395607303607120201 2091875546705477705340151)
          ·
            refine ⟨3137813320058216558010227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091875546705477705340151 3137813320058216558010227)
            ·
              refine ⟨4706719980087324837015341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137813320058216558010227 4706719980087324837015341)
              ·
                refine ⟨1765019992532746813880753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706719980087324837015341 1765019992532746813880753)
                ·
                  refine ⟨1323764994399560110410565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765019992532746813880753 1323764994399560110410565)
                  ·
                    refine ⟨248205936449917520701981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1323764994399560110410565 248205936449917520701981)
                    ·
                      rfl

theorem cell23_1450138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_1450138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450138 prefixEnd_1450138 := by exact prefixLift 1450138
  have htrace : WordTrace (prefixWord ++ tailWord_1450138) baseStart_1450138 baseEnd_1450138 := by
    simpa [prefixWord, tailWord_1450138, baseEnd_1450138] using wordTrace_append hprefix tailTrace_1450138
  have hstable : (prefixWord ++ tailWord_1450138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450138).length < 2 ^ (prefixWord ++ tailWord_1450138).sum := by decide
  have hdescent : baseEnd_1450138 < baseStart_1450138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450165 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1450165 : Nat := 118140960795 + 1450165 * 2 ^ 59
def prefixEnd_1450165 : Nat := 4983230072969 + 3 ^ 40 * 1450165 * 2
def baseEnd_1450165 : Nat := 744631673327423956468319

theorem tailTrace_1450165 : CollatzResearch.WordTrace tailWord_1450165 prefixEnd_1450165 744631673327423956468319 := by
  unfold tailWord_1450165
  simp only [CollatzResearch.WordTrace]
  refine ⟨52891862791307348309215949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35261241860871565539477299 52891862791307348309215949)
  ·
    refine ⟨19834448546740255615955981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52891862791307348309215949 19834448546740255615955981)
    ·
      refine ⟨7437918205027595855983493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19834448546740255615955981 7437918205027595855983493)
      ·
        refine ⟨1394609663442674222996905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7437918205027595855983493 1394609663442674222996905)
        ·
          refine ⟨1045957247582005667247679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394609663442674222996905 1045957247582005667247679)
          ·
            refine ⟨1568935871373008500871519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045957247582005667247679 1568935871373008500871519)
            ·
              refine ⟨2353403807059512751307279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568935871373008500871519 2353403807059512751307279)
              ·
                refine ⟨3530105710589269126960919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353403807059512751307279 3530105710589269126960919)
                ·
                  refine ⟨5295158565883903690441379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530105710589269126960919 5295158565883903690441379)
                  ·
                    refine ⟨7942737848825855535662069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295158565883903690441379 7942737848825855535662069)
                    ·
                      refine ⟨744631673327423956468319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7942737848825855535662069 744631673327423956468319)
                      ·
                        rfl

theorem cell23_1450165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1450165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450165 prefixEnd_1450165 := by exact prefixLift 1450165
  have htrace : WordTrace (prefixWord ++ tailWord_1450165) baseStart_1450165 baseEnd_1450165 := by
    simpa [prefixWord, tailWord_1450165, baseEnd_1450165] using wordTrace_append hprefix tailTrace_1450165
  have hstable : (prefixWord ++ tailWord_1450165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450165).length < 2 ^ (prefixWord ++ tailWord_1450165).sum := by decide
  have hdescent : baseEnd_1450165 < baseStart_1450165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450194 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1450194 : Nat := 118140960795 + 1450194 * 2 ^ 59
def prefixEnd_1450194 : Nat := 4983230072969 + 3 ^ 40 * 1450194 * 2
def baseEnd_1450194 : Nat := 248215521422134781001895

theorem tailTrace_1450194 : CollatzResearch.WordTrace tailWord_1450194 prefixEnd_1450194 248215521422134781001895 := by
  unfold tailWord_1450194
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223230127050571565505409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35261947005468190841347757 13223230127050571565505409)
  ·
    refine ⟨9917422595287928674129057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13223230127050571565505409 9917422595287928674129057)
    ·
      refine ⟨7438066946465946505596793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9917422595287928674129057 7438066946465946505596793)
      ·
        refine ⟨5578550209849459879197595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7438066946465946505596793 5578550209849459879197595)
        ·
          refine ⟨8367825314774189818796393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578550209849459879197595 8367825314774189818796393)
          ·
            refine ⟨6275868986080642364097295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367825314774189818796393 6275868986080642364097295)
            ·
              refine ⟨9413803479120963546145943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275868986080642364097295 9413803479120963546145943)
              ·
                refine ⟨14120705218681445319218915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9413803479120963546145943 14120705218681445319218915)
                ·
                  refine ⟨21181057828022167978828373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14120705218681445319218915 21181057828022167978828373)
                  ·
                    refine ⟨248215521422134781001895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21181057828022167978828373 248215521422134781001895)
                    ·
                      rfl

theorem cell23_1450194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1450194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450194 prefixEnd_1450194 := by exact prefixLift 1450194
  have htrace : WordTrace (prefixWord ++ tailWord_1450194) baseStart_1450194 baseEnd_1450194 := by
    simpa [prefixWord, tailWord_1450194, baseEnd_1450194] using wordTrace_append hprefix tailTrace_1450194
  have hstable : (prefixWord ++ tailWord_1450194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450194).length < 2 ^ (prefixWord ++ tailWord_1450194).sum := by decide
  have hdescent : baseEnd_1450194 < baseStart_1450194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450201 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 4, 2]
def baseStart_1450201 : Nat := 118140960795 + 1450201 * 2 ^ 59
def prefixEnd_1450201 : Nat := 4983230072969 + 3 ^ 40 * 1450201 * 2
def baseEnd_1450201 : Nat := 744650158630985815618153

theorem tailTrace_1450201 : CollatzResearch.WordTrace tailWord_1450201 prefixEnd_1450201 744650158630985815618153 := by
  unfold tailWord_1450201
  simp only [CollatzResearch.WordTrace]
  refine ⟨52893175819176926457526457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35262117212784617638350971 52893175819176926457526457)
  ·
    refine ⟨39669881864382694843144843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52893175819176926457526457 39669881864382694843144843)
    ·
      refine ⟨59504822796574042264717265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39669881864382694843144843 59504822796574042264717265)
      ·
        refine ⟨44628617097430531698537949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59504822796574042264717265 44628617097430531698537949)
        ·
          refine ⟨16735731411536449386951731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44628617097430531698537949 16735731411536449386951731)
          ·
            refine ⟨25103597117304674080427597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16735731411536449386951731 25103597117304674080427597)
            ·
              refine ⟨9413848918989252780160349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25103597117304674080427597 9413848918989252780160349)
              ·
                refine ⟨3530193344620969792560131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9413848918989252780160349 3530193344620969792560131)
                ·
                  refine ⟨5295290016931454688840197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530193344620969792560131 5295290016931454688840197)
                  ·
                    refine ⟨992866878174647754157537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295290016931454688840197 992866878174647754157537)
                    ·
                      refine ⟨744650158630985815618153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992866878174647754157537 744650158630985815618153)
                      ·
                        rfl

theorem cell23_1450201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_1450201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450201 prefixEnd_1450201 := by exact prefixLift 1450201
  have htrace : WordTrace (prefixWord ++ tailWord_1450201) baseStart_1450201 baseEnd_1450201 := by
    simpa [prefixWord, tailWord_1450201, baseEnd_1450201] using wordTrace_append hprefix tailTrace_1450201
  have hstable : (prefixWord ++ tailWord_1450201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450201).length < 2 ^ (prefixWord ++ tailWord_1450201).sum := by decide
  have hdescent : baseEnd_1450201 < baseStart_1450201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450218 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_1450218 : Nat := 118140960795 + 1450218 * 2 ^ 59
def prefixEnd_1450218 : Nat := 4983230072969 + 3 ^ 40 * 1450218 * 2
def baseEnd_1450218 : Nat := 744658887802112249105575

theorem tailTrace_1450218 : CollatzResearch.WordTrace tailWord_1450218 prefixEnd_1450218 744658887802112249105575 := by
  unfold tailWord_1450218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223448965028834590223827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35262530573410225573930205 13223448965028834590223827)
  ·
    refine ⟨19835173447543251885335741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223448965028834590223827 19835173447543251885335741)
    ·
      refine ⟨7438190042828719457000903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19835173447543251885335741 7438190042828719457000903)
      ·
        refine ⟨11157285064243079185501355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438190042828719457000903 11157285064243079185501355)
        ·
          refine ⟨16735927596364618778252033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157285064243079185501355 16735927596364618778252033)
          ·
            refine ⟨12551945697273464083689025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16735927596364618778252033 12551945697273464083689025)
            ·
              refine ⟨9413959272955098062766769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12551945697273464083689025 9413959272955098062766769)
              ·
                refine ⟨7060469454716323547075077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9413959272955098062766769 7060469454716323547075077)
                ·
                  refine ⟨1323838022759310665076577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7060469454716323547075077 1323838022759310665076577)
                  ·
                    refine ⟨992878517069482998807433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1323838022759310665076577 992878517069482998807433)
                    ·
                      refine ⟨744658887802112249105575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992878517069482998807433 744658887802112249105575)
                      ·
                        rfl

theorem cell23_1450218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_1450218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450218 prefixEnd_1450218 := by exact prefixLift 1450218
  have htrace : WordTrace (prefixWord ++ tailWord_1450218) baseStart_1450218 baseEnd_1450218 := by
    simpa [prefixWord, tailWord_1450218, baseEnd_1450218] using wordTrace_append hprefix tailTrace_1450218
  have hstable : (prefixWord ++ tailWord_1450218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450218).length < 2 ^ (prefixWord ++ tailWord_1450218).sum := by decide
  have hdescent : baseEnd_1450218 < baseStart_1450218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450241 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 5]
def baseStart_1450241 : Nat := 118140960795 + 1450241 * 2 ^ 59
def prefixEnd_1450241 : Nat := 4983230072969 + 3 ^ 40 * 1450241 * 2
def baseEnd_1450241 : Nat := 82741188650796184346441

theorem tailTrace_1450241 : CollatzResearch.WordTrace tailWord_1450241 prefixEnd_1450241 82741188650796184346441 := by
  unfold tailWord_1450241
  simp only [CollatzResearch.WordTrace]
  refine ⟨52894634739032013288982577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35263089826021342192655051 52894634739032013288982577)
  ·
    refine ⟨39670976054274009966736933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52894634739032013288982577 39670976054274009966736933)
    ·
      refine ⟨7438308010176376868763175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39670976054274009966736933 7438308010176376868763175)
      ·
        refine ⟨11157462015264565303144763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438308010176376868763175 11157462015264565303144763)
        ·
          refine ⟨16736193022896847954717145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157462015264565303144763 16736193022896847954717145)
          ·
            refine ⟨12552144767172635966037859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16736193022896847954717145 12552144767172635966037859)
            ·
              refine ⟨18828217150758953949056789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12552144767172635966037859 18828217150758953949056789)
              ·
                refine ⟨882572678941825966362037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18828217150758953949056789 882572678941825966362037)
                ·
                  refine ⟨82741188650796184346441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882572678941825966362037 82741188650796184346441)
                  ·
                    rfl

theorem cell23_1450241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 5].length) (baseStart_1450241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450241 prefixEnd_1450241 := by exact prefixLift 1450241
  have htrace : WordTrace (prefixWord ++ tailWord_1450241) baseStart_1450241 baseEnd_1450241 := by
    simpa [prefixWord, tailWord_1450241, baseEnd_1450241] using wordTrace_append hprefix tailTrace_1450241
  have hstable : (prefixWord ++ tailWord_1450241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450241).length < 2 ^ (prefixWord ++ tailWord_1450241).sum := by decide
  have hdescent : baseEnd_1450241 < baseStart_1450241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450254 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1450254 : Nat := 118140960795 + 1450254 * 2 ^ 59
def prefixEnd_1450254 : Nat := 4983230072969 + 3 ^ 40 * 1450254 * 2
def baseEnd_1450254 : Nat := 248225791035224702751803

theorem tailTrace_1450254 : CollatzResearch.WordTrace tailWord_1450254 prefixEnd_1450254 248225791035224702751803 := by
  unfold tailWord_1450254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611888610998114563650727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35263405925323277672803877 6611888610998114563650727)
  ·
    refine ⟨9917832916497171845476091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611888610998114563650727 9917832916497171845476091)
    ·
      refine ⟨14876749374745757768214137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917832916497171845476091 14876749374745757768214137)
      ·
        refine ⟨11157562031059318326160603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14876749374745757768214137 11157562031059318326160603)
        ·
          refine ⟨16736343046588977489240905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157562031059318326160603 16736343046588977489240905)
          ·
            refine ⟨12552257284941733116930679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16736343046588977489240905 12552257284941733116930679)
            ·
              refine ⟨18828385927412599675396019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12552257284941733116930679 18828385927412599675396019)
              ·
                refine ⟨28242578891118899513094029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18828385927412599675396019 28242578891118899513094029)
                ·
                  refine ⟨10590967084169587317410261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28242578891118899513094029 10590967084169587317410261)
                  ·
                    refine ⟨248225791035224702751803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10590967084169587317410261 248225791035224702751803)
                    ·
                      rfl

theorem cell23_1450254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1450254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450254 prefixEnd_1450254 := by exact prefixLift 1450254
  have htrace : WordTrace (prefixWord ++ tailWord_1450254) baseStart_1450254 baseEnd_1450254 := by
    simpa [prefixWord, tailWord_1450254, baseEnd_1450254] using wordTrace_append hprefix tailTrace_1450254
  have hstable : (prefixWord ++ tailWord_1450254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450254).length < 2 ^ (prefixWord ++ tailWord_1450254).sum := by decide
  have hdescent : baseEnd_1450254 < baseStart_1450254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450261 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_1450261 : Nat := 118140960795 + 1450261 * 2 ^ 59
def prefixEnd_1450261 : Nat := 4983230072969 + 3 ^ 40 * 1450261 * 2
def baseEnd_1450261 : Nat := 744680967470255580867877

theorem tailTrace_1450261 : CollatzResearch.WordTrace tailWord_1450261 prefixEnd_1450261 744680967470255580867877 := by
  unfold tailWord_1450261
  simp only [CollatzResearch.WordTrace]
  refine ⟨52895364198959556704710637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35263576132639704469807091 52895364198959556704710637)
  ·
    refine ⟨19835761574609833764266489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52895364198959556704710637 19835761574609833764266489)
    ·
      refine ⟨14876821180957375323199867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19835761574609833764266489 14876821180957375323199867)
      ·
        refine ⟨22315231771436062984799801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876821180957375323199867 22315231771436062984799801)
        ·
          refine ⟨16736423828577047238599851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22315231771436062984799801 16736423828577047238599851)
          ·
            refine ⟨25104635742865570857899777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16736423828577047238599851 25104635742865570857899777)
            ·
              refine ⟨18828476807149178143424833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25104635742865570857899777 18828476807149178143424833)
              ·
                refine ⟨14121357605361883607568625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18828476807149178143424833 14121357605361883607568625)
                ·
                  refine ⟨10591018204021412705676469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14121357605361883607568625 10591018204021412705676469)
                  ·
                    refine ⟨992907956627007441157169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10591018204021412705676469 992907956627007441157169)
                    ·
                      refine ⟨744680967470255580867877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 992907956627007441157169 744680967470255580867877)
                      ·
                        rfl

theorem cell23_1450261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_1450261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450261 prefixEnd_1450261 := by exact prefixLift 1450261
  have htrace : WordTrace (prefixWord ++ tailWord_1450261) baseStart_1450261 baseEnd_1450261 := by
    simpa [prefixWord, tailWord_1450261, baseEnd_1450261] using wordTrace_append hprefix tailTrace_1450261
  have hstable : (prefixWord ++ tailWord_1450261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450261).length < 2 ^ (prefixWord ++ tailWord_1450261).sum := by decide
  have hdescent : baseEnd_1450261 < baseStart_1450261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450291 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4]
def baseStart_1450291 : Nat := 118140960795 + 1450291 * 2 ^ 59
def prefixEnd_1450291 : Nat := 4983230072969 + 3 ^ 40 * 1450291 * 2
def baseEnd_1450291 : Nat := 744696371889890463492739

theorem tailTrace_1450291 : CollatzResearch.WordTrace tailWord_1450291 prefixEnd_1450291 744696371889890463492739 := by
  unfold tailWord_1450291
  simp only [CollatzResearch.WordTrace]
  refine ⟨52896458388850871828302727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35264305592567247885535151 52896458388850871828302727)
  ·
    refine ⟨79344687583276307742454091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52896458388850871828302727 79344687583276307742454091)
    ·
      refine ⟨119017031374914461613681137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79344687583276307742454091 119017031374914461613681137)
      ·
        refine ⟨89262773531185846210260853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119017031374914461613681137 89262773531185846210260853)
        ·
          refine ⟨8368385018548673082211955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89262773531185846210260853 8368385018548673082211955)
          ·
            refine ⟨12552577527823009623317933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368385018548673082211955 12552577527823009623317933)
            ·
              refine ⟨4707216572933628608744225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12552577527823009623317933 4707216572933628608744225)
              ·
                refine ⟨3530412429700221456558169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707216572933628608744225 3530412429700221456558169)
                ·
                  refine ⟨2647809322275166092418627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3530412429700221456558169 2647809322275166092418627)
                  ·
                    refine ⟨3971713983412749138627941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2647809322275166092418627 3971713983412749138627941)
                    ·
                      refine ⟨744696371889890463492739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3971713983412749138627941 744696371889890463492739)
                      ·
                        rfl

theorem cell23_1450291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_1450291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450291 prefixEnd_1450291 := by exact prefixLift 1450291
  have htrace : WordTrace (prefixWord ++ tailWord_1450291) baseStart_1450291 baseEnd_1450291 := by
    simpa [prefixWord, tailWord_1450291, baseEnd_1450291] using wordTrace_append hprefix tailTrace_1450291
  have hstable : (prefixWord ++ tailWord_1450291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450291).length < 2 ^ (prefixWord ++ tailWord_1450291).sum := by decide
  have hdescent : baseEnd_1450291 < baseStart_1450291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450304 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_1450304 : Nat := 118140960795 + 1450304 * 2 ^ 59
def prefixEnd_1450304 : Nat := 4983230072969 + 3 ^ 40 * 1450304 * 2
def baseEnd_1450304 : Nat := 744703047138398912630179

theorem tailTrace_1450304 : CollatzResearch.WordTrace tailWord_1450304 prefixEnd_1450304 744703047138398912630179 := by
  unfold tailWord_1450304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26448466268901887524262983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35264621691869183365683977 26448466268901887524262983)
  ·
    refine ⟨39672699403352831286394475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26448466268901887524262983 39672699403352831286394475)
    ·
      refine ⟨59509049105029246929591713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39672699403352831286394475 59509049105029246929591713)
      ·
        refine ⟨44631786828771935197193785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59509049105029246929591713 44631786828771935197193785)
        ·
          refine ⟨33473840121578951397895339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44631786828771935197193785 33473840121578951397895339)
          ·
            refine ⟨50210760182368427096843009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33473840121578951397895339 50210760182368427096843009)
            ·
              refine ⟨37658070136776320322632257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50210760182368427096843009 37658070136776320322632257)
              ·
                refine ⟨28243552602582240241974193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37658070136776320322632257 28243552602582240241974193)
                ·
                  refine ⟨21182664451936680181480645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28243552602582240241974193 21182664451936680181480645)
                  ·
                    refine ⟨3971749584738127534027621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21182664451936680181480645 3971749584738127534027621)
                    ·
                      refine ⟨744703047138398912630179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3971749584738127534027621 744703047138398912630179)
                      ·
                        rfl

theorem cell23_1450304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_1450304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450304 prefixEnd_1450304 := by exact prefixLift 1450304
  have htrace : WordTrace (prefixWord ++ tailWord_1450304) baseStart_1450304 baseEnd_1450304 := by
    simpa [prefixWord, tailWord_1450304, baseEnd_1450304] using wordTrace_append hprefix tailTrace_1450304
  have hstable : (prefixWord ++ tailWord_1450304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450304).length < 2 ^ (prefixWord ++ tailWord_1450304).sum := by decide
  have hdescent : baseEnd_1450304 < baseStart_1450304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450311 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1450311 : Nat := 118140960795 + 1450311 * 2 ^ 59
def prefixEnd_1450311 : Nat := 4983230072969 + 3 ^ 40 * 1450311 * 2
def baseEnd_1450311 : Nat := 744706641502980385242647

theorem tailTrace_1450311 : CollatzResearch.WordTrace tailWord_1450311 prefixEnd_1450311 744706641502980385242647 := by
  unfold tailWord_1450311
  simp only [CollatzResearch.WordTrace]
  refine ⟨52897187848778415244030787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35264791899185610162687191 52897187848778415244030787)
  ·
    refine ⟨79345781773167622866046181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52897187848778415244030787 79345781773167622866046181)
    ·
      refine ⟨14877334082468929287383659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79345781773167622866046181 14877334082468929287383659)
      ·
        refine ⟨22316001123703393931075489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14877334082468929287383659 22316001123703393931075489)
        ·
          refine ⟨16737000842777545448306617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22316001123703393931075489 16737000842777545448306617)
          ·
            refine ⟨12552750632083159086229963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16737000842777545448306617 12552750632083159086229963)
            ·
              refine ⟨18829125948124738629344945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12552750632083159086229963 18829125948124738629344945)
              ·
                refine ⟨14121844461093553972008709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18829125948124738629344945 14121844461093553972008709)
                ·
                  refine ⟨2647845836455041369751633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14121844461093553972008709 2647845836455041369751633)
                  ·
                    refine ⟨1985884377341281027313725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2647845836455041369751633 1985884377341281027313725)
                    ·
                      refine ⟨744706641502980385242647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985884377341281027313725 744706641502980385242647)
                      ·
                        rfl

theorem cell23_1450311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1450311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450311 prefixEnd_1450311 := by exact prefixLift 1450311
  have htrace : WordTrace (prefixWord ++ tailWord_1450311) baseStart_1450311 baseEnd_1450311 := by
    simpa [prefixWord, tailWord_1450311, baseEnd_1450311] using wordTrace_append hprefix tailTrace_1450311
  have hstable : (prefixWord ++ tailWord_1450311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450311).length < 2 ^ (prefixWord ++ tailWord_1450311).sum := by decide
  have hdescent : baseEnd_1450311 < baseStart_1450311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450348 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 6]
def baseStart_1450348 : Nat := 118140960795 + 1450348 * 2 ^ 59
def prefixEnd_1450348 : Nat := 4983230072969 + 3 ^ 40 * 1450348 * 2
def baseEnd_1450348 : Nat := 82747293365244082275553

theorem tailTrace_1450348 : CollatzResearch.WordTrace tailWord_1450348 prefixEnd_1450348 82747293365244082275553 := by
  unfold tailWord_1450348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26449268674822185281563849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35265691566429580375418465 26449268674822185281563849)
  ·
    refine ⟨19836951506116638961172887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26449268674822185281563849 19836951506116638961172887)
    ·
      refine ⟨29755427259174958441759331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836951506116638961172887 29755427259174958441759331)
      ·
        refine ⟨44633140888762437662638997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29755427259174958441759331 44633140888762437662638997)
        ·
          refine ⟨2092178479160739265436203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44633140888762437662638997 2092178479160739265436203)
          ·
            refine ⟨3138267718741108898154305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092178479160739265436203 3138267718741108898154305)
            ·
              refine ⟨2353700789055831673615729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138267718741108898154305 2353700789055831673615729)
              ·
                refine ⟨1765275591791873755211797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353700789055831673615729 1765275591791873755211797)
                ·
                  refine ⟨82747293365244082275553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1765275591791873755211797 82747293365244082275553)
                  ·
                    rfl

theorem cell23_1450348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_1450348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450348 prefixEnd_1450348 := by exact prefixLift 1450348
  have htrace : WordTrace (prefixWord ++ tailWord_1450348) baseStart_1450348 baseEnd_1450348 := by
    simpa [prefixWord, tailWord_1450348, baseEnd_1450348] using wordTrace_append hprefix tailTrace_1450348
  have hstable : (prefixWord ++ tailWord_1450348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450348).length < 2 ^ (prefixWord ++ tailWord_1450348).sum := by decide
  have hdescent : baseEnd_1450348 < baseStart_1450348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450352 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 1, 4]
def baseStart_1450352 : Nat := 118140960795 + 1450352 * 2 ^ 59
def prefixEnd_1450352 : Nat := 4983230072969 + 3 ^ 40 * 1450352 * 2
def baseEnd_1450352 : Nat := 248242564736604908276653

theorem tailTrace_1450352 : CollatzResearch.WordTrace tailWord_1450352 prefixEnd_1450352 248242564736604908276653 := by
  unfold tailWord_1450352
  simp only [CollatzResearch.WordTrace]
  refine ⟨26449341620814939623136655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35265788827753252830848873 26449341620814939623136655)
  ·
    refine ⟨39674012431222409434704983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26449341620814939623136655 39674012431222409434704983)
    ·
      refine ⟨59511018646833614152057475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39674012431222409434704983 59511018646833614152057475)
      ·
        refine ⟨89266527970250421228086213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59511018646833614152057475 89266527970250421228086213)
        ·
          refine ⟨16737473994421953980266165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89266527970250421228086213 16737473994421953980266165)
          ·
            refine ⟨1569138186977058185649953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16737473994421953980266165 1569138186977058185649953)
            ·
              refine ⟨1176853640232793639237465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569138186977058185649953 1176853640232793639237465)
              ·
                refine ⟨882640230174595229428099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176853640232793639237465 882640230174595229428099)
                ·
                  refine ⟨1323960345261892844142149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882640230174595229428099 1323960345261892844142149)
                  ·
                    refine ⟨248242564736604908276653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1323960345261892844142149 248242564736604908276653)
                    ·
                      rfl

theorem cell23_1450352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_1450352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450352 prefixEnd_1450352 := by exact prefixLift 1450352
  have htrace : WordTrace (prefixWord ++ tailWord_1450352) baseStart_1450352 baseEnd_1450352 := by
    simpa [prefixWord, tailWord_1450352, baseEnd_1450352] using wordTrace_append hprefix tailTrace_1450352
  have hstable : (prefixWord ++ tailWord_1450352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450352).length < 2 ^ (prefixWord ++ tailWord_1450352).sum := by decide
  have hdescent : baseEnd_1450352 < baseStart_1450352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450391 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 6]
def baseStart_1450391 : Nat := 118140960795 + 1450391 * 2 ^ 59
def prefixEnd_1450391 : Nat := 4983230072969 + 3 ^ 40 * 1450391 * 2
def baseEnd_1450391 : Nat := 248249239985113357414093

theorem tailTrace_1450391 : CollatzResearch.WordTrace tailWord_1450391 prefixEnd_1450391 248249239985113357414093 := by
  unfold tailWord_1450391
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900105688488588906943027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35266737125659059271295351 52900105688488588906943027)
  ·
    refine ⟨79350158532732883360414541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52900105688488588906943027 79350158532732883360414541)
    ·
      refine ⟨29756309449774831260155453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79350158532732883360414541 29756309449774831260155453)
      ·
        refine ⟨11158616043665561722558295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29756309449774831260155453 11158616043665561722558295)
        ·
          refine ⟨16737924065498342583837443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11158616043665561722558295 16737924065498342583837443)
          ·
            refine ⟨25106886098247513875756165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16737924065498342583837443 25106886098247513875756165)
            ·
              refine ⟨4707541143421408851704281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25106886098247513875756165 4707541143421408851704281)
              ·
                refine ⟨3530655857566056638778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707541143421408851704281 3530655857566056638778211)
                ·
                  refine ⟨5295983786349084958167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530655857566056638778211 5295983786349084958167317)
                  ·
                    refine ⟨248249239985113357414093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5295983786349084958167317 248249239985113357414093)
                    ·
                      rfl

theorem cell23_1450391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_1450391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450391 prefixEnd_1450391 := by exact prefixLift 1450391
  have htrace : WordTrace (prefixWord ++ tailWord_1450391) baseStart_1450391 baseEnd_1450391 := by
    simpa [prefixWord, tailWord_1450391, baseEnd_1450391] using wordTrace_append hprefix tailTrace_1450391
  have hstable : (prefixWord ++ tailWord_1450391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450391).length < 2 ^ (prefixWord ++ tailWord_1450391).sum := by decide
  have hdescent : baseEnd_1450391 < baseStart_1450391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450392 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1450392 : Nat := 118140960795 + 1450392 * 2 ^ 59
def prefixEnd_1450392 : Nat := 4983230072969 + 3 ^ 40 * 1450392 * 2
def baseEnd_1450392 : Nat := 744748233435994568329775

theorem tailTrace_1450392 : CollatzResearch.WordTrace tailWord_1450392 prefixEnd_1450392 744748233435994568329775 := by
  unfold tailWord_1450392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450071080742483038864715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35266761440989977385152953 26450071080742483038864715)
  ·
    refine ⟨39675106621113724558297073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26450071080742483038864715 39675106621113724558297073)
    ·
      refine ⟨29756329965835293418722805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39675106621113724558297073 29756329965835293418722805)
      ·
        refine ⟨2789655934297058758005263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29756329965835293418722805 2789655934297058758005263)
        ·
          refine ⟨4184483901445588137007895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789655934297058758005263 4184483901445588137007895)
          ·
            refine ⟨6276725852168382205511843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184483901445588137007895 6276725852168382205511843)
            ·
              refine ⟨9415088778252573308267765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276725852168382205511843 9415088778252573308267765)
              ·
                refine ⟨882664572961178747650103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9415088778252573308267765 882664572961178747650103)
                ·
                  refine ⟨1323996859441768121475155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882664572961178747650103 1323996859441768121475155)
                  ·
                    refine ⟨1985995289162652182212733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1323996859441768121475155 1985995289162652182212733)
                    ·
                      refine ⟨744748233435994568329775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1985995289162652182212733 744748233435994568329775)
                      ·
                        rfl

theorem cell23_1450392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1450392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450392 prefixEnd_1450392 := by exact prefixLift 1450392
  have htrace : WordTrace (prefixWord ++ tailWord_1450392) baseStart_1450392 baseEnd_1450392 := by
    simpa [prefixWord, tailWord_1450392, baseEnd_1450392] using wordTrace_append hprefix tailTrace_1450392
  have hstable : (prefixWord ++ tailWord_1450392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450392).length < 2 ^ (prefixWord ++ tailWord_1450392).sum := by decide
  have hdescent : baseEnd_1450392 < baseStart_1450392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450428 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1450428 : Nat := 118140960795 + 1450428 * 2 ^ 59
def prefixEnd_1450428 : Nat := 4983230072969 + 3 ^ 40 * 1450428 * 2
def baseEnd_1450428 : Nat := 744766718739556427479609

theorem tailTrace_1450428 : CollatzResearch.WordTrace tailWord_1450428 prefixEnd_1450428 744766718739556427479609 := by
  unfold tailWord_1450428
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450727594677272113019969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35267636792903029484026625 26450727594677272113019969)
  ·
    refine ⟨19838045696007954084764977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26450727594677272113019969 19838045696007954084764977)
    ·
      refine ⟨14878534272005965563573733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19838045696007954084764977 14878534272005965563573733)
      ·
        refine ⟨2789725176001118543170075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14878534272005965563573733 2789725176001118543170075)
        ·
          refine ⟨4184587764001677814755113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789725176001118543170075 4184587764001677814755113)
          ·
            refine ⟨3138440823001258361066335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4184587764001677814755113 3138440823001258361066335)
            ·
              refine ⟨4707661234501887541599503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138440823001258361066335 4707661234501887541599503)
              ·
                refine ⟨7061491851752831312399255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707661234501887541599503 7061491851752831312399255)
                ·
                  refine ⟨10592237777629246968598883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061491851752831312399255 10592237777629246968598883)
                  ·
                    refine ⟨15888356666443870452898325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10592237777629246968598883 15888356666443870452898325)
                    ·
                      refine ⟨744766718739556427479609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15888356666443870452898325 744766718739556427479609)
                      ·
                        rfl

theorem cell23_1450428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1450428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450428 prefixEnd_1450428 := by exact prefixLift 1450428
  have htrace : WordTrace (prefixWord ++ tailWord_1450428) baseStart_1450428 baseEnd_1450428 := by
    simpa [prefixWord, tailWord_1450428, baseEnd_1450428] using wordTrace_append hprefix tailTrace_1450428
  have hstable : (prefixWord ++ tailWord_1450428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450428).length < 2 ^ (prefixWord ++ tailWord_1450428).sum := by decide
  have hdescent : baseEnd_1450428 < baseStart_1450428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450465 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_1450465 : Nat := 118140960795 + 1450465 * 2 ^ 59
def prefixEnd_1450465 : Nat := 4983230072969 + 3 ^ 40 * 1450465 * 2
def baseEnd_1450465 : Nat := 744785717523772782716939

theorem tailTrace_1450465 : CollatzResearch.WordTrace tailWord_1450465 prefixEnd_1450465 744785717523772782716939 := by
  unfold tailWord_1450465
  simp only [CollatzResearch.WordTrace]
  refine ⟨52902804690220499545136849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35268536460146999696757899 52902804690220499545136849)
  ·
    refine ⟨39677103517665374658852637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52902804690220499545136849 39677103517665374658852637)
    ·
      refine ⟨14878913819124515497069739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39677103517665374658852637 14878913819124515497069739)
      ·
        refine ⟨22318370728686773245604609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878913819124515497069739 22318370728686773245604609)
        ·
          refine ⟨16738778046515079934203457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22318370728686773245604609 16738778046515079934203457)
          ·
            refine ⟨12554083534886309950652593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16738778046515079934203457 12554083534886309950652593)
            ·
              refine ⟨9415562651164732462989445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12554083534886309950652593 9415562651164732462989445)
              ·
                refine ⟨1765417997093387336810521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9415562651164732462989445 1765417997093387336810521)
                ·
                  refine ⟨1324063497820040502607891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765417997093387336810521 1324063497820040502607891)
                  ·
                    refine ⟨1986095246730060753911837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324063497820040502607891 1986095246730060753911837)
                    ·
                      refine ⟨744785717523772782716939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986095246730060753911837 744785717523772782716939)
                      ·
                        rfl

theorem cell23_1450465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_1450465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450465 prefixEnd_1450465 := by exact prefixLift 1450465
  have htrace : WordTrace (prefixWord ++ tailWord_1450465) baseStart_1450465 baseEnd_1450465 := by
    simpa [prefixWord, tailWord_1450465, baseEnd_1450465] using wordTrace_append hprefix tailTrace_1450465
  have hstable : (prefixWord ++ tailWord_1450465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450465).length < 2 ^ (prefixWord ++ tailWord_1450465).sum := by decide
  have hdescent : baseEnd_1450465 < baseStart_1450465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450481 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_1450481 : Nat := 118140960795 + 1450481 * 2 ^ 59
def prefixEnd_1450481 : Nat := 4983230072969 + 3 ^ 40 * 1450481 * 2
def baseEnd_1450481 : Nat := 248264644404748240038955

theorem tailTrace_1450481 : CollatzResearch.WordTrace tailWord_1450481 prefixEnd_1450481 248264644404748240038955 := by
  unfold tailWord_1450481
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903388258162534277719297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35268925505441689518479531 52903388258162534277719297)
  ·
    refine ⟨39677541193621900708289473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52903388258162534277719297 39677541193621900708289473)
    ·
      refine ⟨29758155895216425531217105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39677541193621900708289473 29758155895216425531217105)
      ·
        refine ⟨22318616921412319148412829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29758155895216425531217105 22318616921412319148412829)
        ·
          refine ⟨8369481345529619680654811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22318616921412319148412829 8369481345529619680654811)
          ·
            refine ⟨12554222018294429520982217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369481345529619680654811 12554222018294429520982217)
            ·
              refine ⟨9415666513720822140736663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12554222018294429520982217 9415666513720822140736663)
              ·
                refine ⟨14123499770581233211104995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415666513720822140736663 14123499770581233211104995)
                ·
                  refine ⟨21185249655871849816657493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14123499770581233211104995 21185249655871849816657493)
                  ·
                    refine ⟨248264644404748240038955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21185249655871849816657493 248264644404748240038955)
                    ·
                      rfl

theorem cell23_1450481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_1450481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450481 prefixEnd_1450481 := by exact prefixLift 1450481
  have htrace : WordTrace (prefixWord ++ tailWord_1450481) baseStart_1450481 baseEnd_1450481 := by
    simpa [prefixWord, tailWord_1450481, baseEnd_1450481] using wordTrace_append hprefix tailTrace_1450481
  have hstable : (prefixWord ++ tailWord_1450481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450481).length < 2 ^ (prefixWord ++ tailWord_1450481).sum := by decide
  have hdescent : baseEnd_1450481 < baseStart_1450481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450505 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 4, 2, 2]
def baseStart_1450505 : Nat := 118140960795 + 1450505 * 2 ^ 59
def prefixEnd_1450505 : Nat := 4983230072969 + 3 ^ 40 * 1450505 * 2
def baseEnd_1450505 : Nat := 744806256749952626216755

theorem tailTrace_1450505 : CollatzResearch.WordTrace tailWord_1450505 prefixEnd_1450505 744806256749952626216755 := by
  unfold tailWord_1450505
  simp only [CollatzResearch.WordTrace]
  refine ⟨52904263610075586376592969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35269509073383724251061979 52904263610075586376592969)
  ·
    refine ⟨39678197707556689782444727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52904263610075586376592969 39678197707556689782444727)
    ·
      refine ⟨59517296561335034673667091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39678197707556689782444727 59517296561335034673667091)
      ·
        refine ⟨89275944842002552010500637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59517296561335034673667091 89275944842002552010500637)
        ·
          refine ⟨33478479315750957003937739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89275944842002552010500637 33478479315750957003937739)
          ·
            refine ⟨50217718973626435505906609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33478479315750957003937739 50217718973626435505906609)
            ·
              refine ⟨37663289230219826629429957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50217718973626435505906609 37663289230219826629429957)
              ·
                refine ⟨7061866730666217493018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37663289230219826629429957 7061866730666217493018117)
                ·
                  refine ⟨1324100011999915779940897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7061866730666217493018117 1324100011999915779940897)
                  ·
                    refine ⟨993075008999936834955673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324100011999915779940897 993075008999936834955673)
                    ·
                      refine ⟨744806256749952626216755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993075008999936834955673 744806256749952626216755)
                      ·
                        rfl

theorem cell23_1450505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2, 2].length) (baseStart_1450505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450505 prefixEnd_1450505 := by exact prefixLift 1450505
  have htrace : WordTrace (prefixWord ++ tailWord_1450505) baseStart_1450505 baseEnd_1450505 := by
    simpa [prefixWord, tailWord_1450505, baseEnd_1450505] using wordTrace_append hprefix tailTrace_1450505
  have hstable : (prefixWord ++ tailWord_1450505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450505).length < 2 ^ (prefixWord ++ tailWord_1450505).sum := by decide
  have hdescent : baseEnd_1450505 < baseStart_1450505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450508 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1450508 : Nat := 118140960795 + 1450508 * 2 ^ 59
def prefixEnd_1450508 : Nat := 4983230072969 + 3 ^ 40 * 1450508 * 2
def baseEnd_1450508 : Nat := 744807797191916114479241

theorem tailTrace_1450508 : CollatzResearch.WordTrace tailWord_1450508 prefixEnd_1450508 744807797191916114479241 := by
  unfold tailWord_1450508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452186514532358944476089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35269582019376478592634785 26452186514532358944476089)
  ·
    refine ⟨19839139885899269208357067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26452186514532358944476089 19839139885899269208357067)
    ·
      refine ⟨29758709828848903812535601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19839139885899269208357067 29758709828848903812535601)
      ·
        refine ⟨22319032371636677859401701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29758709828848903812535601 22319032371636677859401701)
        ·
          refine ⟨4184818569681877098637819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22319032371636677859401701 4184818569681877098637819)
          ·
            refine ⟨6277227854522815647956729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184818569681877098637819 6277227854522815647956729)
            ·
              refine ⟨4707920890892111735967547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6277227854522815647956729 4707920890892111735967547)
              ·
                refine ⟨7061881336338167603951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707920890892111735967547 7061881336338167603951321)
                ·
                  refine ⟨5296411002253625702963491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061881336338167603951321 5296411002253625702963491)
                  ·
                    refine ⟨7944616503380438554445237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5296411002253625702963491 7944616503380438554445237)
                    ·
                      refine ⟨744807797191916114479241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7944616503380438554445237 744807797191916114479241)
                      ·
                        rfl

theorem cell23_1450508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1450508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450508 prefixEnd_1450508 := by exact prefixLift 1450508
  have htrace : WordTrace (prefixWord ++ tailWord_1450508) baseStart_1450508 baseEnd_1450508 := by
    simpa [prefixWord, tailWord_1450508, baseEnd_1450508] using wordTrace_append hprefix tailTrace_1450508
  have hstable : (prefixWord ++ tailWord_1450508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450508).length < 2 ^ (prefixWord ++ tailWord_1450508).sum := by decide
  have hdescent : baseEnd_1450508 < baseStart_1450508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450522 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_1450522 : Nat := 118140960795 + 1450522 * 2 ^ 59
def prefixEnd_1450522 : Nat := 4983230072969 + 3 ^ 40 * 1450522 * 2
def baseEnd_1450522 : Nat := 744814985921079059704177

theorem tailTrace_1450522 : CollatzResearch.WordTrace tailWord_1450522 prefixEnd_1450522 744814985921079059704177 := by
  unfold tailWord_1450522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13226220912753499569990455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35269922434009332186641213 13226220912753499569990455)
  ·
    refine ⟨19839331369130249354985683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13226220912753499569990455 19839331369130249354985683)
    ·
      refine ⟨29758997053695374032478525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19839331369130249354985683 29758997053695374032478525)
      ·
        refine ⟨11159623895135765262179447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29758997053695374032478525 11159623895135765262179447)
        ·
          refine ⟨16739435842703647893269171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11159623895135765262179447 16739435842703647893269171)
          ·
            refine ⟨25109153764055471839903757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16739435842703647893269171 25109153764055471839903757)
            ·
              refine ⟨9415932661520801939963909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25109153764055471839903757 9415932661520801939963909)
              ·
                refine ⟨1765487374035150363743233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9415932661520801939963909 1765487374035150363743233)
                ·
                  refine ⟨1324115530526362772807425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765487374035150363743233 1324115530526362772807425)
                  ·
                    refine ⟨993086647894772079605569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324115530526362772807425 993086647894772079605569)
                    ·
                      refine ⟨744814985921079059704177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993086647894772079605569 744814985921079059704177)
                      ·
                        rfl

theorem cell23_1450522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_1450522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450522 prefixEnd_1450522 := by exact prefixLift 1450522
  have htrace : WordTrace (prefixWord ++ tailWord_1450522) baseStart_1450522 baseEnd_1450522 := by
    simpa [prefixWord, tailWord_1450522, baseEnd_1450522] using wordTrace_append hprefix tailTrace_1450522
  have hstable : (prefixWord ++ tailWord_1450522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450522).length < 2 ^ (prefixWord ++ tailWord_1450522).sum := by decide
  have hdescent : baseEnd_1450522 < baseStart_1450522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450590 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1450590 : Nat := 118140960795 + 1450590 * 2 ^ 59
def prefixEnd_1450590 : Nat := 4983230072969 + 3 ^ 40 * 1450590 * 2
def baseEnd_1450590 : Nat := 744849902605584793653865

theorem tailTrace_1450590 : CollatzResearch.WordTrace tailWord_1450590 prefixEnd_1450590 744849902605584793653865 := by
  unfold tailWord_1450590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613420476845955736679653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35271575876511763928958149 6613420476845955736679653)
  ·
    refine ⟨1240016339408616700627435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6613420476845955736679653 1240016339408616700627435)
    ·
      refine ⟨1860024509112925050941153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1240016339408616700627435 1860024509112925050941153)
      ·
        refine ⟨1395018381834693788205865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860024509112925050941153 1395018381834693788205865)
        ·
          refine ⟨1046263786376020341154399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395018381834693788205865 1046263786376020341154399)
          ·
            refine ⟨1569395679564030511731599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046263786376020341154399 1569395679564030511731599)
            ·
              refine ⟨2354093519346045767597399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569395679564030511731599 2354093519346045767597399)
              ·
                refine ⟨3531140279019068651396099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354093519346045767597399 3531140279019068651396099)
                ·
                  refine ⟨5296710418528602977094149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531140279019068651396099 5296710418528602977094149)
                  ·
                    refine ⟨993133203474113058205153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296710418528602977094149 993133203474113058205153)
                    ·
                      refine ⟨744849902605584793653865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993133203474113058205153 744849902605584793653865)
                      ·
                        rfl

theorem cell23_1450590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1450590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450590 prefixEnd_1450590 := by exact prefixLift 1450590
  have htrace : WordTrace (prefixWord ++ tailWord_1450590) baseStart_1450590 baseEnd_1450590 := by
    simpa [prefixWord, tailWord_1450590, baseEnd_1450590] using wordTrace_append hprefix tailTrace_1450590
  have hstable : (prefixWord ++ tailWord_1450590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450590).length < 2 ^ (prefixWord ++ tailWord_1450590).sum := by decide
  have hdescent : baseEnd_1450590 < baseStart_1450590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450595 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 4, 2]
def baseStart_1450595 : Nat := 118140960795 + 1450595 * 2 ^ 59
def prefixEnd_1450595 : Nat := 4983230072969 + 3 ^ 40 * 1450595 * 2
def baseEnd_1450595 : Nat := 744852470008857274091341

theorem tailTrace_1450595 : CollatzResearch.WordTrace tailWord_1450595 prefixEnd_1450595 744852470008857274091341 := by
  unfold tailWord_1450595
  simp only [CollatzResearch.WordTrace]
  refine ⟨52907546179749531747369239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35271697453166354498246159 52907546179749531747369239)
  ·
    refine ⟨79361319269624297621053859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52907546179749531747369239 79361319269624297621053859)
    ·
      refine ⟨119041978904436446431580789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79361319269624297621053859 119041978904436446431580789)
      ·
        refine ⟨11160185522290916852960699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119041978904436446431580789 11160185522290916852960699)
        ·
          refine ⟨16740278283436375279441049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160185522290916852960699 16740278283436375279441049)
          ·
            refine ⟨12555208712577281459580787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16740278283436375279441049 12555208712577281459580787)
            ·
              refine ⟨18832813068865922189371181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555208712577281459580787 18832813068865922189371181)
              ·
                refine ⟨7062304900824720821014193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18832813068865922189371181 7062304900824720821014193)
                ·
                  refine ⟨5296728675618540615760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062304900824720821014193 5296728675618540615760645)
                  ·
                    refine ⟨993136626678476365455121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296728675618540615760645 993136626678476365455121)
                    ·
                      refine ⟨744852470008857274091341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993136626678476365455121 744852470008857274091341)
                      ·
                        rfl

theorem cell23_1450595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_1450595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450595 prefixEnd_1450595 := by exact prefixLift 1450595
  have htrace : WordTrace (prefixWord ++ tailWord_1450595) baseStart_1450595 baseEnd_1450595 := by
    simpa [prefixWord, tailWord_1450595, baseEnd_1450595] using wordTrace_append hprefix tailTrace_1450595
  have hstable : (prefixWord ++ tailWord_1450595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450595).length < 2 ^ (prefixWord ++ tailWord_1450595).sum := by decide
  have hdescent : baseEnd_1450595 < baseStart_1450595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450626 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1450626 : Nat := 118140960795 + 1450626 * 2 ^ 59
def prefixEnd_1450626 : Nat := 4983230072969 + 3 ^ 40 * 1450626 * 2
def baseEnd_1450626 : Nat := 248289462636382217601233

theorem tailTrace_1450626 : CollatzResearch.WordTrace tailWord_1450626 prefixEnd_1450626 248289462636382217601233 := by
  unfold tailWord_1450626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227169210659306010436933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35272451228424816027831821 13227169210659306010436933)
  ·
    refine ⟨2480094226998619876956925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13227169210659306010436933 2480094226998619876956925)
    ·
      refine ⟨930035335124482453858847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2480094226998619876956925 930035335124482453858847)
      ·
        refine ⟨1395053002686723680788271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930035335124482453858847 1395053002686723680788271)
        ·
          refine ⟨2092579504030085521182407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395053002686723680788271 2092579504030085521182407)
          ·
            refine ⟨3138869256045128281773611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092579504030085521182407 3138869256045128281773611)
            ·
              refine ⟨4708303884067692422660417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138869256045128281773611 4708303884067692422660417)
              ·
                refine ⟨3531227913050769316995313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708303884067692422660417 3531227913050769316995313)
                ·
                  refine ⟨2648420934788076987746485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531227913050769316995313 2648420934788076987746485)
                  ·
                    refine ⟨248289462636382217601233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2648420934788076987746485 248289462636382217601233)
                    ·
                      rfl

theorem cell23_1450626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1450626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450626 prefixEnd_1450626 := by exact prefixLift 1450626
  have htrace : WordTrace (prefixWord ++ tailWord_1450626) baseStart_1450626 baseEnd_1450626 := by
    simpa [prefixWord, tailWord_1450626, baseEnd_1450626] using wordTrace_append hprefix tailTrace_1450626
  have hstable : (prefixWord ++ tailWord_1450626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450626).length < 2 ^ (prefixWord ++ tailWord_1450626).sum := by decide
  have hdescent : baseEnd_1450626 < baseStart_1450626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450652 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 6]
def baseStart_1450652 : Nat := 118140960795 + 1450652 * 2 ^ 59
def prefixEnd_1450652 : Nat := 4983230072969 + 3 ^ 40 * 1450652 * 2
def baseEnd_1450652 : Nat := 82764637600684839008731

theorem tailTrace_1450652 : CollatzResearch.WordTrace tailWord_1450652 prefixEnd_1450652 82764637600684839008731 := by
  unfold tailWord_1450652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26454812570271515241097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35273083427028686988129473 26454812570271515241097105)
  ·
    refine ⟨19841109427703636430822829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26454812570271515241097105 19841109427703636430822829)
    ·
      refine ⟨7440416035388863661558561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19841109427703636430822829 7440416035388863661558561)
      ·
        refine ⟨5580312026541647746168921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7440416035388863661558561 5580312026541647746168921)
        ·
          refine ⟨4185234019906235809626691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580312026541647746168921 4185234019906235809626691)
          ·
            refine ⟨6277851029859353714440037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185234019906235809626691 6277851029859353714440037)
            ·
              refine ⟨1177097068098628821457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6277851029859353714440037 1177097068098628821457507)
              ·
                refine ⟨1765645602147943232186261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177097068098628821457507 1765645602147943232186261)
                ·
                  refine ⟨82764637600684839008731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1765645602147943232186261 82764637600684839008731)
                  ·
                    rfl

theorem cell23_1450652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_1450652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450652 prefixEnd_1450652 := by exact prefixLift 1450652
  have htrace : WordTrace (prefixWord ++ tailWord_1450652) baseStart_1450652 baseEnd_1450652 := by
    simpa [prefixWord, tailWord_1450652, baseEnd_1450652] using wordTrace_append hprefix tailTrace_1450652
  have hstable : (prefixWord ++ tailWord_1450652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450652).length < 2 ^ (prefixWord ++ tailWord_1450652).sum := by decide
  have hdescent : baseEnd_1450652 < baseStart_1450652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450666 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1450666 : Nat := 118140960795 + 1450666 * 2 ^ 59
def prefixEnd_1450666 : Nat := 4983230072969 + 3 ^ 40 * 1450666 * 2
def baseEnd_1450666 : Nat := 744888927135326496303515

theorem tailTrace_1450666 : CollatzResearch.WordTrace tailWord_1450666 prefixEnd_1450666 744888927135326496303515 := by
  unfold tailWord_1450666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227533940623077718300963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35273423841661540582135901 13227533940623077718300963)
  ·
    refine ⟨19841300910934616577451445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13227533940623077718300963 19841300910934616577451445)
    ·
      refine ⟨1860121960400120304136073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19841300910934616577451445 1860121960400120304136073)
      ·
        refine ⟨1395091470300090228102055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860121960400120304136073 1395091470300090228102055)
        ·
          refine ⟨2092637205450135342153083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395091470300090228102055 2092637205450135342153083)
          ·
            refine ⟨3138955808175203013229625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092637205450135342153083 3138955808175203013229625)
            ·
              refine ⟨2354216856131402259922219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3138955808175203013229625 2354216856131402259922219)
              ·
                refine ⟨3531325284197103389883329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354216856131402259922219 3531325284197103389883329)
                ·
                  refine ⟨2648493963147827542412497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3531325284197103389883329 2648493963147827542412497)
                  ·
                    refine ⟨1986370472360870656809373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648493963147827542412497 1986370472360870656809373)
                    ·
                      refine ⟨744888927135326496303515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986370472360870656809373 744888927135326496303515)
                      ·
                        rfl

theorem cell23_1450666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1450666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450666 prefixEnd_1450666 := by exact prefixLift 1450666
  have htrace : WordTrace (prefixWord ++ tailWord_1450666) baseStart_1450666 baseEnd_1450666 := by
    simpa [prefixWord, tailWord_1450666, baseEnd_1450666] using wordTrace_append hprefix tailTrace_1450666
  have hstable : (prefixWord ++ tailWord_1450666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450666).length < 2 ^ (prefixWord ++ tailWord_1450666).sum := by decide
  have hdescent : baseEnd_1450666 < baseStart_1450666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450682 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_1450682 : Nat := 118140960795 + 1450682 * 2 ^ 59
def prefixEnd_1450682 : Nat := 4983230072969 + 3 ^ 40 * 1450682 * 2
def baseEnd_1450682 : Nat := 248299047608599477901147

theorem tailTrace_1450682 : CollatzResearch.WordTrace tailWord_1450682 prefixEnd_1450682 248299047608599477901147 := by
  unfold tailWord_1450682
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227679832608586401446575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35273812886956230403857533 13227679832608586401446575)
  ·
    refine ⟨19841519748912879602169863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13227679832608586401446575 19841519748912879602169863)
    ·
      refine ⟨29762279623369319403254795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841519748912879602169863 29762279623369319403254795)
      ·
        refine ⟨44643419435053979104882193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29762279623369319403254795 44643419435053979104882193)
        ·
          refine ⟨33482564576290484328661645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44643419435053979104882193 33482564576290484328661645)
          ·
            refine ⟨12555961716108931623248117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33482564576290484328661645 12555961716108931623248117)
            ·
              refine ⟨1177121410885212339679511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12555961716108931623248117 1177121410885212339679511)
              ·
                refine ⟨1765682116327818509519267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177121410885212339679511 1765682116327818509519267)
                ·
                  refine ⟨2648523174491727764278901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765682116327818509519267 2648523174491727764278901)
                  ·
                    refine ⟨248299047608599477901147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2648523174491727764278901 248299047608599477901147)
                    ·
                      rfl

theorem cell23_1450682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_1450682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450682 prefixEnd_1450682 := by exact prefixLift 1450682
  have htrace : WordTrace (prefixWord ++ tailWord_1450682) baseStart_1450682 baseEnd_1450682 := by
    simpa [prefixWord, tailWord_1450682, baseEnd_1450682] using wordTrace_append hprefix tailTrace_1450682
  have hstable : (prefixWord ++ tailWord_1450682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450682).length < 2 ^ (prefixWord ++ tailWord_1450682).sum := by decide
  have hdescent : baseEnd_1450682 < baseStart_1450682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450696 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_1450696 : Nat := 118140960795 + 1450696 * 2 ^ 59
def prefixEnd_1450696 : Nat := 4983230072969 + 3 ^ 40 * 1450696 * 2
def baseEnd_1450696 : Nat := 744904331554961378928377

theorem tailTrace_1450696 : CollatzResearch.WordTrace tailWord_1450696 prefixEnd_1450696 744904331554961378928377 := by
  unfold tailWord_1450696
  simp only [CollatzResearch.WordTrace]
  refine ⟨26455614976191812998397971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35274153301589083997863961 26455614976191812998397971)
  ·
    refine ⟨39683422464287719497596957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26455614976191812998397971 39683422464287719497596957)
    ·
      refine ⟨14881283424107894811598859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39683422464287719497596957 14881283424107894811598859)
      ·
        refine ⟨22321925136161842217398289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14881283424107894811598859 22321925136161842217398289)
        ·
          refine ⟨16741443852121381663048717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22321925136161842217398289 16741443852121381663048717)
          ·
            refine ⟨6278041444545518123643269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16741443852121381663048717 6278041444545518123643269)
            ·
              refine ⟨1177132770852284648183113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6278041444545518123643269 1177132770852284648183113)
              ·
                refine ⟨882849578139213486137335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177132770852284648183113 882849578139213486137335)
                ·
                  refine ⟨1324274367208820229206003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882849578139213486137335 1324274367208820229206003)
                  ·
                    refine ⟨1986411550813230343809005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324274367208820229206003 1986411550813230343809005)
                    ·
                      refine ⟨744904331554961378928377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986411550813230343809005 744904331554961378928377)
                      ·
                        rfl

theorem cell23_1450696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_1450696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450696 prefixEnd_1450696 := by exact prefixLift 1450696
  have htrace : WordTrace (prefixWord ++ tailWord_1450696) baseStart_1450696 baseEnd_1450696 := by
    simpa [prefixWord, tailWord_1450696, baseEnd_1450696] using wordTrace_append hprefix tailTrace_1450696
  have hstable : (prefixWord ++ tailWord_1450696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450696).length < 2 ^ (prefixWord ++ tailWord_1450696).sum := by decide
  have hdescent : baseEnd_1450696 < baseStart_1450696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450705 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_1450705 : Nat := 118140960795 + 1450705 * 2 ^ 59
def prefixEnd_1450705 : Nat := 4983230072969 + 3 ^ 40 * 1450705 * 2
def baseEnd_1450705 : Nat := 744908952880851843715835

theorem tailTrace_1450705 : CollatzResearch.WordTrace tailWord_1450705 prefixEnd_1450705 744908952880851843715835 := by
  unfold tailWord_1450705
  simp only [CollatzResearch.WordTrace]
  refine ⟨52911558209351020533873569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35274372139567347022582379 52911558209351020533873569)
  ·
    refine ⟨39683668657013265400405177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52911558209351020533873569 39683668657013265400405177)
    ·
      refine ⟨29762751492759949050303883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39683668657013265400405177 29762751492759949050303883)
      ·
        refine ⟨44644127239139923575455825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29762751492759949050303883 44644127239139923575455825)
        ·
          refine ⟨33483095429354942681591869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44644127239139923575455825 33483095429354942681591869)
          ·
            refine ⟨12556160786008103505596951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33483095429354942681591869 12556160786008103505596951)
            ·
              refine ⟨18834241179012155258395427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12556160786008103505596951 18834241179012155258395427)
              ·
                refine ⟨28251361768518232887593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18834241179012155258395427 28251361768518232887593141)
                ·
                  refine ⟨2648565165798584333211857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28251361768518232887593141 2648565165798584333211857)
                  ·
                    refine ⟨1986423874348938249908893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2648565165798584333211857 1986423874348938249908893)
                    ·
                      refine ⟨744908952880851843715835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986423874348938249908893 744908952880851843715835)
                      ·
                        rfl

theorem cell23_1450705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_1450705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450705 prefixEnd_1450705 := by exact prefixLift 1450705
  have htrace : WordTrace (prefixWord ++ tailWord_1450705) baseStart_1450705 baseEnd_1450705 := by
    simpa [prefixWord, tailWord_1450705, baseEnd_1450705] using wordTrace_append hprefix tailTrace_1450705
  have hstable : (prefixWord ++ tailWord_1450705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450705).length < 2 ^ (prefixWord ++ tailWord_1450705).sum := by decide
  have hdescent : baseEnd_1450705 < baseStart_1450705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450712 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_1450712 : Nat := 118140960795 + 1450712 * 2 ^ 59
def prefixEnd_1450712 : Nat := 4983230072969 + 3 ^ 40 * 1450712 * 2
def baseEnd_1450712 : Nat := 248304182415144438776101

theorem tailTrace_1450712 : CollatzResearch.WordTrace tailWord_1450712 prefixEnd_1450712 248304182415144438776101 := by
  unfold tailWord_1450712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26455906760162830364689195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35274542346883773819585593 26455906760162830364689195)
  ·
    refine ⟨39683860140244245547033793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26455906760162830364689195 39683860140244245547033793)
    ·
      refine ⟨29762895105183184160275345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39683860140244245547033793 29762895105183184160275345)
      ·
        refine ⟨22322171328887388120206509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29762895105183184160275345 22322171328887388120206509)
        ·
          refine ⟨8370814248332770545077441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22322171328887388120206509 8370814248332770545077441)
          ·
            refine ⟨6278110686249577908808081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8370814248332770545077441 6278110686249577908808081)
            ·
              refine ⟨4708583014687183431606061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6278110686249577908808081 4708583014687183431606061)
              ·
                refine ⟨1765718630507693786852273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4708583014687183431606061 1765718630507693786852273)
                ·
                  refine ⟨1324288972880770340139205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765718630507693786852273 1324288972880770340139205)
                  ·
                    refine ⟨248304182415144438776101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1324288972880770340139205 248304182415144438776101)
                    ·
                      rfl

theorem cell23_1450712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_1450712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450712 prefixEnd_1450712 := by exact prefixLift 1450712
  have htrace : WordTrace (prefixWord ++ tailWord_1450712) baseStart_1450712 baseEnd_1450712 := by
    simpa [prefixWord, tailWord_1450712, baseEnd_1450712] using wordTrace_append hprefix tailTrace_1450712
  have hstable : (prefixWord ++ tailWord_1450712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450712).length < 2 ^ (prefixWord ++ tailWord_1450712).sum := by decide
  have hdescent : baseEnd_1450712 < baseStart_1450712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450719 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 3, 2, 2]
def baseStart_1450719 : Nat := 118140960795 + 1450719 * 2 ^ 59
def prefixEnd_1450719 : Nat := 4983230072969 + 3 ^ 40 * 1450719 * 2
def baseEnd_1450719 : Nat := 744916141610014788940771

theorem tailTrace_1450719 : CollatzResearch.WordTrace tailWord_1450719 prefixEnd_1450719 744916141610014788940771 := by
  unfold tailWord_1450719
  simp only [CollatzResearch.WordTrace]
  refine ⟨52912068831300300924883211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35274712554200200616588807 52912068831300300924883211)
  ·
    refine ⟨79368103246950451387324817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52912068831300300924883211 79368103246950451387324817)
    ·
      refine ⟨59526077435212838540493613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79368103246950451387324817 59526077435212838540493613)
      ·
        refine ⟨22322279038204814452685105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59526077435212838540493613 22322279038204814452685105)
        ·
          refine ⟨16741709278653610839513829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22322279038204814452685105 16741709278653610839513829)
          ·
            refine ⟨3139070489747552032408843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16741709278653610839513829 3139070489747552032408843)
            ·
              refine ⟨4708605734621328048613265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139070489747552032408843 4708605734621328048613265)
              ·
                refine ⟨3531454300965996036459949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708605734621328048613265 3531454300965996036459949)
                ·
                  refine ⟨1324295362862248513672481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3531454300965996036459949 1324295362862248513672481)
                  ·
                    refine ⟨993221522146686385254361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324295362862248513672481 993221522146686385254361)
                    ·
                      refine ⟨744916141610014788940771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993221522146686385254361 744916141610014788940771)
                      ·
                        rfl

theorem cell23_1450719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_1450719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450719 prefixEnd_1450719 := by exact prefixLift 1450719
  have htrace : WordTrace (prefixWord ++ tailWord_1450719) baseStart_1450719 baseEnd_1450719 := by
    simpa [prefixWord, tailWord_1450719, baseEnd_1450719] using wordTrace_append hprefix tailTrace_1450719
  have hstable : (prefixWord ++ tailWord_1450719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450719).length < 2 ^ (prefixWord ++ tailWord_1450719).sum := by decide
  have hdescent : baseEnd_1450719 < baseStart_1450719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450736 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 1, 2, 2]
def baseStart_1450736 : Nat := 118140960795 + 1450736 * 2 ^ 59
def prefixEnd_1450736 : Nat := 4983230072969 + 3 ^ 40 * 1450736 * 2
def baseEnd_1450736 : Nat := 744924870781141222428193

theorem tailTrace_1450736 : CollatzResearch.WordTrace tailWord_1450736 prefixEnd_1450736 744924870781141222428193 := by
  unfold tailWord_1450736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456344436119356414126031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35275125914825808552168041 26456344436119356414126031)
  ·
    refine ⟨39684516654179034621189047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26456344436119356414126031 39684516654179034621189047)
    ·
      refine ⟨59526774981268551931783571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39684516654179034621189047 59526774981268551931783571)
      ·
        refine ⟨89290162471902827897675357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59526774981268551931783571 89290162471902827897675357)
        ·
          refine ⟨33483810926963560461628259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89290162471902827897675357 33483810926963560461628259)
          ·
            refine ⟨50225716390445340692442389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33483810926963560461628259 50225716390445340692442389)
            ·
              refine ⟨2354330455802125344958237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50225716390445340692442389 2354330455802125344958237)
              ·
                refine ⟨882873920925797004359339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354330455802125344958237 882873920925797004359339)
                ·
                  refine ⟨1324310881388695506539009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 882873920925797004359339 1324310881388695506539009)
                  ·
                    refine ⟨993233161041521629904257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324310881388695506539009 993233161041521629904257)
                    ·
                      refine ⟨744924870781141222428193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993233161041521629904257 744924870781141222428193)
                      ·
                        rfl

theorem cell23_1450736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 2, 2].length) (baseStart_1450736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450736 prefixEnd_1450736 := by exact prefixLift 1450736
  have htrace : WordTrace (prefixWord ++ tailWord_1450736) baseStart_1450736 baseEnd_1450736 := by
    simpa [prefixWord, tailWord_1450736, baseEnd_1450736] using wordTrace_append hprefix tailTrace_1450736
  have hstable : (prefixWord ++ tailWord_1450736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450736).length < 2 ^ (prefixWord ++ tailWord_1450736).sum := by decide
  have hdescent : baseEnd_1450736 < baseStart_1450736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450869 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1450869 : Nat := 118140960795 + 1450869 * 2 ^ 59
def prefixEnd_1450869 : Nat := 4983230072969 + 3 ^ 40 * 1450869 * 2
def baseEnd_1450869 : Nat := 744993163708189202065081

theorem tailTrace_1450869 : CollatzResearch.WordTrace tailWord_1450869 prefixEnd_1450869 744993163708189202065081 := by
  unfold tailWord_1450869
  simp only [CollatzResearch.WordTrace]
  refine ⟨52917539780756876542843661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35278359853837917695229107 52917539780756876542843661)
  ·
    refine ⟨19844077417783828703566373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52917539780756876542843661 19844077417783828703566373)
    ·
      refine ⟨3720764515834467881918695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19844077417783828703566373 3720764515834467881918695)
      ·
        refine ⟨5581146773751701822878043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720764515834467881918695 5581146773751701822878043)
        ·
          refine ⟨8371720160627552734317065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581146773751701822878043 8371720160627552734317065)
          ·
            refine ⟨6278790120470664550737799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371720160627552734317065 6278790120470664550737799)
            ·
              refine ⟨9418185180705996826106699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278790120470664550737799 9418185180705996826106699)
              ·
                refine ⟨14127277771058995239160049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418185180705996826106699 14127277771058995239160049)
                ·
                  refine ⟨10595458328294246429370037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14127277771058995239160049 10595458328294246429370037)
                  ·
                    refine ⟨993324218277585602753441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10595458328294246429370037 993324218277585602753441)
                    ·
                      refine ⟨744993163708189202065081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993324218277585602753441 744993163708189202065081)
                      ·
                        rfl

theorem cell23_1450869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1450869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450869 prefixEnd_1450869 := by exact prefixLift 1450869
  have htrace : WordTrace (prefixWord ++ tailWord_1450869) baseStart_1450869 baseEnd_1450869 := by
    simpa [prefixWord, tailWord_1450869, baseEnd_1450869] using wordTrace_append hprefix tailTrace_1450869
  have hstable : (prefixWord ++ tailWord_1450869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450869).length < 2 ^ (prefixWord ++ tailWord_1450869).sum := by decide
  have hdescent : baseEnd_1450869 < baseStart_1450869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450892 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1450892 : Nat := 118140960795 + 1450892 * 2 ^ 59
def prefixEnd_1450892 : Nat := 4983230072969 + 3 ^ 40 * 1450892 * 2
def baseEnd_1450892 : Nat := 248334991254414204025825

theorem tailTrace_1450892 : CollatzResearch.WordTrace tailWord_1450892 prefixEnd_1450892 248334991254414204025825 := by
  unfold tailWord_1450892
  simp only [CollatzResearch.WordTrace]
  refine ⟨26459189329836775735465465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35278919106449034313953953 26459189329836775735465465)
  ·
    refine ⟨19844391997377581801599099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26459189329836775735465465 19844391997377581801599099)
    ·
      refine ⟨29766587996066372702398649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19844391997377581801599099 29766587996066372702398649)
      ·
        refine ⟨22324940997049779526798987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29766587996066372702398649 22324940997049779526798987)
        ·
          refine ⟨33487411495574669290198481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22324940997049779526798987 33487411495574669290198481)
          ·
            refine ⟨25115558621681001967648861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33487411495574669290198481 25115558621681001967648861)
            ·
              refine ⟨9418334483130375737868323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25115558621681001967648861 9418334483130375737868323)
              ·
                refine ⟨14127501724695563606802485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418334483130375737868323 14127501724695563606802485)
                ·
                  refine ⟨1324453286690209088137733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14127501724695563606802485 1324453286690209088137733)
                  ·
                    refine ⟨248334991254414204025825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1324453286690209088137733 248334991254414204025825)
                    ·
                      rfl

theorem cell23_1450892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1450892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450892 prefixEnd_1450892 := by exact prefixLift 1450892
  have htrace : WordTrace (prefixWord ++ tailWord_1450892) baseStart_1450892 baseEnd_1450892 := by
    simpa [prefixWord, tailWord_1450892, baseEnd_1450892] using wordTrace_append hprefix tailTrace_1450892
  have hstable : (prefixWord ++ tailWord_1450892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450892).length < 2 ^ (prefixWord ++ tailWord_1450892).sum := by decide
  have hdescent : baseEnd_1450892 < baseStart_1450892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450905 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 8]
def baseStart_1450905 : Nat := 118140960795 + 1450905 * 2 ^ 59
def prefixEnd_1450905 : Nat := 4983230072969 + 3 ^ 40 * 1450905 * 2
def baseEnd_1450905 : Nat := 82779072112416784579435

theorem tailTrace_1450905 : CollatzResearch.WordTrace tailWord_1450905 prefixEnd_1450905 82779072112416784579435 := by
  unfold tailWord_1450905
  simp only [CollatzResearch.WordTrace]
  refine ⟨52918852808626454691154169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35279235205750969794102779 52918852808626454691154169)
  ·
    refine ⟨39689139606469841018365627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52918852808626454691154169 39689139606469841018365627)
    ·
      refine ⟨59533709409704761527548441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39689139606469841018365627 59533709409704761527548441)
      ·
        refine ⟨44650282057278571145661331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59533709409704761527548441 44650282057278571145661331)
        ·
          refine ⟨66975423085917856718491997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44650282057278571145661331 66975423085917856718491997)
          ·
            refine ⟨25115783657219196269434499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66975423085917856718491997 25115783657219196269434499)
            ·
              refine ⟨37673675485828794404151749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25115783657219196269434499 37673675485828794404151749)
              ·
                refine ⟨7063814153592898950778453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37673675485828794404151749 7063814153592898950778453)
                ·
                  refine ⟨82779072112416784579435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7063814153592898950778453 82779072112416784579435)
                  ·
                    rfl

theorem cell23_1450905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_1450905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450905 prefixEnd_1450905 := by exact prefixLift 1450905
  have htrace : WordTrace (prefixWord ++ tailWord_1450905) baseStart_1450905 baseEnd_1450905 := by
    simpa [prefixWord, tailWord_1450905, baseEnd_1450905] using wordTrace_append hprefix tailTrace_1450905
  have hstable : (prefixWord ++ tailWord_1450905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450905).length < 2 ^ (prefixWord ++ tailWord_1450905).sum := by decide
  have hdescent : baseEnd_1450905 < baseStart_1450905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450942 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1450942 : Nat := 118140960795 + 1450942 * 2 ^ 59
def prefixEnd_1450942 : Nat := 4983230072969 + 3 ^ 40 * 1450942 * 2
def baseEnd_1450942 : Nat := 745030647795967416452245

theorem tailTrace_1450942 : CollatzResearch.WordTrace tailWord_1450942 prefixEnd_1450942 745030647795967416452245 := by
  unfold tailWord_1450942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615025288686551251281385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35280134872994940006834053 6615025288686551251281385)
  ·
    refine ⟨4961268966514913438461039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6615025288686551251281385 4961268966514913438461039)
    ·
      refine ⟨7441903449772370157691559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961268966514913438461039 7441903449772370157691559)
      ·
        refine ⟨11162855174658555236537339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441903449772370157691559 11162855174658555236537339)
        ·
          refine ⟨16744282761987832854806009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11162855174658555236537339 16744282761987832854806009)
          ·
            refine ⟨12558212071490874641104507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16744282761987832854806009 12558212071490874641104507)
            ·
              refine ⟨18837318107236311961656761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12558212071490874641104507 18837318107236311961656761)
              ·
                refine ⟨14127988580427233971242571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18837318107236311961656761 14127988580427233971242571)
                ·
                  refine ⟨21191982870640850956863857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14127988580427233971242571 21191982870640850956863857)
                  ·
                    refine ⟨15893987152980638217647893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21191982870640850956863857 15893987152980638217647893)
                    ·
                      refine ⟨745030647795967416452245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15893987152980638217647893 745030647795967416452245)
                      ·
                        rfl

theorem cell23_1450942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1450942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450942 prefixEnd_1450942 := by exact prefixLift 1450942
  have htrace : WordTrace (prefixWord ++ tailWord_1450942) baseStart_1450942 baseEnd_1450942 := by
    simpa [prefixWord, tailWord_1450942, baseEnd_1450942] using wordTrace_append hprefix tailTrace_1450942
  have hstable : (prefixWord ++ tailWord_1450942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450942).length < 2 ^ (prefixWord ++ tailWord_1450942).sum := by decide
  have hdescent : baseEnd_1450942 < baseStart_1450942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450959 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 5, 2]
def baseStart_1450959 : Nat := 118140960795 + 1450959 * 2 ^ 59
def prefixEnd_1450959 : Nat := 4983230072969 + 3 ^ 40 * 1450959 * 2
def baseEnd_1450959 : Nat := 745039376967093849939667

theorem tailTrace_1450959 : CollatzResearch.WordTrace tailWord_1450959 prefixEnd_1450959 745039376967093849939667 := by
  unfold tailWord_1450959
  simp only [CollatzResearch.WordTrace]
  refine ⟨52920822350430821913619931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35280548233620547942413287 52920822350430821913619931)
  ·
    refine ⟨79381233525646232870429897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52920822350430821913619931 79381233525646232870429897)
    ·
      refine ⟨59535925144234674652822423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79381233525646232870429897 59535925144234674652822423)
      ·
        refine ⟨89303887716352011979233635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59535925144234674652822423 89303887716352011979233635)
        ·
          refine ⟨133955831574528017968850453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89303887716352011979233635 133955831574528017968850453)
          ·
            refine ⟨6279179605056000842289865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133955831574528017968850453 6279179605056000842289865)
            ·
              refine ⟨4709384703792000631717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279179605056000842289865 4709384703792000631717399)
              ·
                refine ⟨7064077055688000947576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709384703792000631717399 7064077055688000947576099)
                ·
                  refine ⟨10596115583532001421364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064077055688000947576099 10596115583532001421364149)
                  ·
                    refine ⟨993385835956125133252889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10596115583532001421364149 993385835956125133252889)
                    ·
                      refine ⟨745039376967093849939667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993385835956125133252889 745039376967093849939667)
                      ·
                        rfl

theorem cell23_1450959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5, 2].length) (baseStart_1450959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450959 prefixEnd_1450959 := by exact prefixLift 1450959
  have htrace : WordTrace (prefixWord ++ tailWord_1450959) baseStart_1450959 baseEnd_1450959 := by
    simpa [prefixWord, tailWord_1450959, baseEnd_1450959] using wordTrace_append hprefix tailTrace_1450959
  have hstable : (prefixWord ++ tailWord_1450959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450959).length < 2 ^ (prefixWord ++ tailWord_1450959).sum := by decide
  have hdescent : baseEnd_1450959 < baseStart_1450959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450969 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_1450969 : Nat := 118140960795 + 1450969 * 2 ^ 59
def prefixEnd_1450969 : Nat := 4983230072969 + 3 ^ 40 * 1450969 * 2
def baseEnd_1450969 : Nat := 248348170591212936938207

theorem tailTrace_1450969 : CollatzResearch.WordTrace tailWord_1450969 prefixEnd_1450969 248348170591212936938207 := by
  unfold tailWord_1450969
  simp only [CollatzResearch.WordTrace]
  refine ⟨52921187080394593621483961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35280791386929729080989307 52921187080394593621483961)
  ·
    refine ⟨39690890310295945216112971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52921187080394593621483961 39690890310295945216112971)
    ·
      refine ⟨59536335465443917824169457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39690890310295945216112971 59536335465443917824169457)
      ·
        refine ⟨44652251599082938368127093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59536335465443917824169457 44652251599082938368127093)
        ·
          refine ⟨4186148587414025472011915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44652251599082938368127093 4186148587414025472011915)
          ·
            refine ⟨6279222881121038208017873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186148587414025472011915 6279222881121038208017873)
            ·
              refine ⟨4709417160840778656013405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279222881121038208017873 4709417160840778656013405)
              ·
                refine ⟨1766031435315291996005027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4709417160840778656013405 1766031435315291996005027)
                ·
                  refine ⟨2649047152972937994007541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766031435315291996005027 2649047152972937994007541)
                  ·
                    refine ⟨248348170591212936938207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2649047152972937994007541 248348170591212936938207)
                    ·
                      rfl

theorem cell23_1450969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_1450969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450969 prefixEnd_1450969 := by exact prefixLift 1450969
  have htrace : WordTrace (prefixWord ++ tailWord_1450969) baseStart_1450969 baseEnd_1450969 := by
    simpa [prefixWord, tailWord_1450969, baseEnd_1450969] using wordTrace_append hprefix tailTrace_1450969
  have hstable : (prefixWord ++ tailWord_1450969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450969).length < 2 ^ (prefixWord ++ tailWord_1450969).sum := by decide
  have hdescent : baseEnd_1450969 < baseStart_1450969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450983 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1450983 : Nat := 118140960795 + 1450983 * 2 ^ 59
def prefixEnd_1450983 : Nat := 4983230072969 + 3 ^ 40 * 1450983 * 2
def baseEnd_1450983 : Nat := 745051700502801756039557

theorem tailTrace_1450983 : CollatzResearch.WordTrace tailWord_1450983 prefixEnd_1450983 745051700502801756039557 := by
  unfold tailWord_1450983
  simp only [CollatzResearch.WordTrace]
  refine ⟨52921697702343874012493603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35281131801562582674995735 52921697702343874012493603)
  ·
    refine ⟨79382546553515811018740405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52921697702343874012493603 79382546553515811018740405)
    ·
      refine ⟨7442113739392107283006913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79382546553515811018740405 7442113739392107283006913)
      ·
        refine ⟨5581585304544080462255185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7442113739392107283006913 5581585304544080462255185)
        ·
          refine ⟨4186188978408060346691389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581585304544080462255185 4186188978408060346691389)
          ·
            refine ⟨1569820866903022630009271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4186188978408060346691389 1569820866903022630009271)
            ·
              refine ⟨2354731300354533945013907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569820866903022630009271 2354731300354533945013907)
              ·
                refine ⟨3532096950531800917520861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354731300354533945013907 3532096950531800917520861)
                ·
                  refine ⟨1324536356449425344070323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3532096950531800917520861 1324536356449425344070323)
                  ·
                    refine ⟨1986804534674138016105485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324536356449425344070323 1986804534674138016105485)
                    ·
                      refine ⟨745051700502801756039557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986804534674138016105485 745051700502801756039557)
                      ·
                        rfl

theorem cell23_1450983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1450983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450983 prefixEnd_1450983 := by exact prefixLift 1450983
  have htrace : WordTrace (prefixWord ++ tailWord_1450983) baseStart_1450983 baseEnd_1450983 := by
    simpa [prefixWord, tailWord_1450983, baseEnd_1450983] using wordTrace_append hprefix tailTrace_1450983
  have hstable : (prefixWord ++ tailWord_1450983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450983).length < 2 ^ (prefixWord ++ tailWord_1450983).sum := by decide
  have hdescent : baseEnd_1450983 < baseStart_1450983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450992 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_1450992 : Nat := 118140960795 + 1450992 * 2 ^ 59
def prefixEnd_1450992 : Nat := 4983230072969 + 3 ^ 40 * 1450992 * 2
def baseEnd_1450992 : Nat := 745056321828692220827015

theorem tailTrace_1450992 : CollatzResearch.WordTrace tailWord_1450992 prefixEnd_1450992 745056321828692220827015 := by
  unfold tailWord_1450992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26461012979655634274785615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35281350639540845699714153 26461012979655634274785615)
  ·
    refine ⟨39691519469483451412178423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26461012979655634274785615 39691519469483451412178423)
    ·
      refine ⟨59537279204225177118267635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39691519469483451412178423 59537279204225177118267635)
      ·
        refine ⟨89305918806337765677401453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59537279204225177118267635 89305918806337765677401453)
        ·
          refine ⟨33489719552376662129025545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89305918806337765677401453 33489719552376662129025545)
          ·
            refine ⟨25117289664282496596769159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33489719552376662129025545 25117289664282496596769159)
            ·
              refine ⟨37675934496423744895153739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25117289664282496596769159 37675934496423744895153739)
              ·
                refine ⟨56513901744635617342730609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37675934496423744895153739 56513901744635617342730609)
                ·
                  refine ⟨42385426308476713007047957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56513901744635617342730609 42385426308476713007047957)
                  ·
                    refine ⟨1986816858209845922205373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42385426308476713007047957 1986816858209845922205373)
                    ·
                      refine ⟨745056321828692220827015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986816858209845922205373 745056321828692220827015)
                      ·
                        rfl

theorem cell23_1450992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_1450992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1450992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1450992 prefixEnd_1450992 := by exact prefixLift 1450992
  have htrace : WordTrace (prefixWord ++ tailWord_1450992) baseStart_1450992 baseEnd_1450992 := by
    simpa [prefixWord, tailWord_1450992, baseEnd_1450992] using wordTrace_append hprefix tailTrace_1450992
  have hstable : (prefixWord ++ tailWord_1450992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450992).length < 2 ^ (prefixWord ++ tailWord_1450992).sum := by decide
  have hdescent : baseEnd_1450992 < baseStart_1450992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451002 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1451002 : Nat := 118140960795 + 1451002 * 2 ^ 59
def prefixEnd_1451002 : Nat := 4983230072969 + 3 ^ 40 * 1451002 * 2
def baseEnd_1451002 : Nat := 745061456635237181701969

theorem tailTrace_1451002 : CollatzResearch.WordTrace tailWord_1451002 prefixEnd_1451002 745061456635237181701969 := by
  unfold tailWord_1451002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230597672318760064358815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35281593792850026838290173 13230597672318760064358815)
  ·
    refine ⟨19845896508478140096538223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13230597672318760064358815 19845896508478140096538223)
    ·
      refine ⟨29768844762717210144807335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19845896508478140096538223 29768844762717210144807335)
      ·
        refine ⟨44653267144075815217211003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29768844762717210144807335 44653267144075815217211003)
        ·
          refine ⟨66979900716113722825816505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44653267144075815217211003 66979900716113722825816505)
          ·
            refine ⟨50234925537085292119362379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66979900716113722825816505 50234925537085292119362379)
            ·
              refine ⟨75352388305627938179043569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50234925537085292119362379 75352388305627938179043569)
              ·
                refine ⟨56514291229220953634282677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75352388305627938179043569 56514291229220953634282677)
                ·
                  refine ⟨5298214802739464403214001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56514291229220953634282677 5298214802739464403214001)
                  ·
                    refine ⟨3973661102054598302410501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298214802739464403214001 3973661102054598302410501)
                    ·
                      refine ⟨745061456635237181701969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3973661102054598302410501 745061456635237181701969)
                      ·
                        rfl

theorem cell23_1451002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1451002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451002 prefixEnd_1451002 := by exact prefixLift 1451002
  have htrace : WordTrace (prefixWord ++ tailWord_1451002) baseStart_1451002 baseEnd_1451002 := by
    simpa [prefixWord, tailWord_1451002, baseEnd_1451002] using wordTrace_append hprefix tailTrace_1451002
  have hstable : (prefixWord ++ tailWord_1451002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451002).length < 2 ^ (prefixWord ++ tailWord_1451002).sum := by decide
  have hdescent : baseEnd_1451002 < baseStart_1451002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451019 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4]
def baseStart_1451019 : Nat := 118140960795 + 1451019 * 2 ^ 59
def prefixEnd_1451019 : Nat := 4983230072969 + 3 ^ 40 * 1451019 * 2
def baseEnd_1451019 : Nat := 745070185806363615189391

theorem tailTrace_1451019 : CollatzResearch.WordTrace tailWord_1451019 prefixEnd_1451019 745070185806363615189391 := by
  unfold tailWord_1451019
  simp only [CollatzResearch.WordTrace]
  refine ⟨52923010730213452160804111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35282007153475634773869407 52923010730213452160804111)
  ·
    refine ⟨79384516095320178241206167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52923010730213452160804111 79384516095320178241206167)
    ·
      refine ⟨119076774142980267361809251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79384516095320178241206167 119076774142980267361809251)
      ·
        refine ⟨178615161214470401042713877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119076774142980267361809251 178615161214470401042713877)
        ·
          refine ⟨8372585681928300048877213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178615161214470401042713877 8372585681928300048877213)
          ·
            refine ⟨3139719630723112518328955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8372585681928300048877213 3139719630723112518328955)
            ·
              refine ⟨4709579446084668777493433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139719630723112518328955 4709579446084668777493433)
              ·
                refine ⟨3532184584563501583120075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709579446084668777493433 3532184584563501583120075)
                ·
                  refine ⟨5298276876845252374680113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532184584563501583120075 5298276876845252374680113)
                  ·
                    refine ⟨3973707657633939281010085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298276876845252374680113 3973707657633939281010085)
                    ·
                      refine ⟨745070185806363615189391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3973707657633939281010085 745070185806363615189391)
                      ·
                        rfl

theorem cell23_1451019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 4].length) (baseStart_1451019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451019 prefixEnd_1451019 := by exact prefixLift 1451019
  have htrace : WordTrace (prefixWord ++ tailWord_1451019) baseStart_1451019 baseEnd_1451019 := by
    simpa [prefixWord, tailWord_1451019, baseEnd_1451019] using wordTrace_append hprefix tailTrace_1451019
  have hstable : (prefixWord ++ tailWord_1451019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451019).length < 2 ^ (prefixWord ++ tailWord_1451019).sum := by decide
  have hdescent : baseEnd_1451019 < baseStart_1451019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451056 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_1451056 : Nat := 118140960795 + 1451056 * 2 ^ 59
def prefixEnd_1451056 : Nat := 4983230072969 + 3 ^ 40 * 1451056 * 2
def baseEnd_1451056 : Nat := 745089184590579970426721

theorem tailTrace_1451056 : CollatzResearch.WordTrace tailWord_1451056 prefixEnd_1451056 745089184590579970426721 := by
  unfold tailWord_1451056
  simp only [CollatzResearch.WordTrace]
  refine ⟨26462180115539703739950511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35282906820719604986600681 26462180115539703739950511)
  ·
    refine ⟨39693270173309555609925767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26462180115539703739950511 39693270173309555609925767)
    ·
      refine ⟨59539905259964333414888651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39693270173309555609925767 59539905259964333414888651)
      ·
        refine ⟨89309857889946500122332977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59539905259964333414888651 89309857889946500122332977)
        ·
          refine ⟨66982393417459875091749733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89309857889946500122332977 66982393417459875091749733)
          ·
            refine ⟨12559198765773726579703075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66982393417459875091749733 12559198765773726579703075)
            ·
              refine ⟨18838798148660589869554613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559198765773726579703075 18838798148660589869554613)
              ·
                refine ⟨1766137326436930300270745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18838798148660589869554613 1766137326436930300270745)
                ·
                  refine ⟨1324602994827697725203059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766137326436930300270745 1324602994827697725203059)
                  ·
                    refine ⟨1986904492241546587804589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324602994827697725203059 1986904492241546587804589)
                    ·
                      refine ⟨745089184590579970426721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986904492241546587804589 745089184590579970426721)
                      ·
                        rfl

theorem cell23_1451056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_1451056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451056 prefixEnd_1451056 := by exact prefixLift 1451056
  have htrace : WordTrace (prefixWord ++ tailWord_1451056) baseStart_1451056 baseEnd_1451056 := by
    simpa [prefixWord, tailWord_1451056, baseEnd_1451056] using wordTrace_append hprefix tailTrace_1451056
  have hstable : (prefixWord ++ tailWord_1451056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451056).length < 2 ^ (prefixWord ++ tailWord_1451056).sum := by decide
  have hdescent : baseEnd_1451056 < baseStart_1451056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451066 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_1451066 : Nat := 118140960795 + 1451066 * 2 ^ 59
def prefixEnd_1451066 : Nat := 4983230072969 + 3 ^ 40 * 1451066 * 2
def baseEnd_1451066 : Nat := 745094319397124931301675

theorem tailTrace_1451066 : CollatzResearch.WordTrace tailWord_1451066 prefixEnd_1451066 745094319397124931301675 := by
  unfold tailWord_1451066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231181240260794796941263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35283149974028786125176701 13231181240260794796941263)
  ·
    refine ⟨19846771860391192195411895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13231181240260794796941263 19846771860391192195411895)
    ·
      refine ⟨29770157790586788293117843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19846771860391192195411895 29770157790586788293117843)
      ·
        refine ⟨44655236685880182439676765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29770157790586788293117843 44655236685880182439676765)
        ·
          refine ⟨16745713757205068414878787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44655236685880182439676765 16745713757205068414878787)
          ·
            refine ⟨25118570635807602622318181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16745713757205068414878787 25118570635807602622318181)
            ·
              refine ⟨4709731994213925491684659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25118570635807602622318181 4709731994213925491684659)
              ·
                refine ⟨7064597991320888237526989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709731994213925491684659 7064597991320888237526989)
                ·
                  refine ⟨2649224246745333089072621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7064597991320888237526989 2649224246745333089072621)
                  ·
                    refine ⟨993459092529499908402233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2649224246745333089072621 993459092529499908402233)
                    ·
                      refine ⟨745094319397124931301675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993459092529499908402233 745094319397124931301675)
                      ·
                        rfl

theorem cell23_1451066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_1451066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451066 prefixEnd_1451066 := by exact prefixLift 1451066
  have htrace : WordTrace (prefixWord ++ tailWord_1451066) baseStart_1451066 baseEnd_1451066 := by
    simpa [prefixWord, tailWord_1451066, baseEnd_1451066] using wordTrace_append hprefix tailTrace_1451066
  have hstable : (prefixWord ++ tailWord_1451066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451066).length < 2 ^ (prefixWord ++ tailWord_1451066).sum := by decide
  have hdescent : baseEnd_1451066 < baseStart_1451066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451072 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_1451072 : Nat := 118140960795 + 1451072 * 2 ^ 59
def prefixEnd_1451072 : Nat := 4983230072969 + 3 ^ 40 * 1451072 * 2
def baseEnd_1451072 : Nat := 248365800093683969275549

theorem tailTrace_1451072 : CollatzResearch.WordTrace tailWord_1451072 prefixEnd_1451072 248365800093683969275549 := by
  unfold tailWord_1451072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26462471899510721106241735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35283295866014294808322313 26462471899510721106241735)
  ·
    refine ⟨39693707849266081659362603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26462471899510721106241735 39693707849266081659362603)
    ·
      refine ⟨59540561773899122489043905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39693707849266081659362603 59540561773899122489043905)
      ·
        refine ⟨44655421330424341866782929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59540561773899122489043905 44655421330424341866782929)
        ·
          refine ⟨33491565997818256400087197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44655421330424341866782929 33491565997818256400087197)
          ·
            refine ⟨12559337249181846150032699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33491565997818256400087197 12559337249181846150032699)
            ·
              refine ⟨18839005873772769225049049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559337249181846150032699 18839005873772769225049049)
              ·
                refine ⟨14129254405329576918786787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18839005873772769225049049 14129254405329576918786787)
                ·
                  refine ⟨21193881607994365378180181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14129254405329576918786787 21193881607994365378180181)
                  ·
                    refine ⟨248365800093683969275549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21193881607994365378180181 248365800093683969275549)
                    ·
                      rfl

theorem cell23_1451072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_1451072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451072 prefixEnd_1451072 := by exact prefixLift 1451072
  have htrace : WordTrace (prefixWord ++ tailWord_1451072) baseStart_1451072 baseEnd_1451072 := by
    simpa [prefixWord, tailWord_1451072, baseEnd_1451072] using wordTrace_append hprefix tailTrace_1451072
  have hstable : (prefixWord ++ tailWord_1451072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451072).length < 2 ^ (prefixWord ++ tailWord_1451072).sum := by decide
  have hdescent : baseEnd_1451072 < baseStart_1451072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451090 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1451090 : Nat := 118140960795 + 1451090 * 2 ^ 59
def prefixEnd_1451090 : Nat := 4983230072969 + 3 ^ 40 * 1451090 * 2
def baseEnd_1451090 : Nat := 745106642932832837401565

theorem tailTrace_1451090 : CollatzResearch.WordTrace tailWord_1451090 prefixEnd_1451090 745106642932832837401565 := by
  unfold tailWord_1451090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231400078239057821659681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35283733541970820857759149 13231400078239057821659681)
  ·
    refine ⟨9923550058679293366244761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13231400078239057821659681 9923550058679293366244761)
    ·
      refine ⟨7442662544009470024683571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9923550058679293366244761 7442662544009470024683571)
      ·
        refine ⟨11163993816014205037025357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442662544009470024683571 11163993816014205037025357)
        ·
          refine ⟨4186497681005326888884509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11163993816014205037025357 4186497681005326888884509)
          ·
            refine ⟨1569936630376997583331691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4186497681005326888884509 1569936630376997583331691)
            ·
              refine ⟨2354904945565496374997537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569936630376997583331691 2354904945565496374997537)
              ·
                refine ⟨1766178709174122281248153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354904945565496374997537 1766178709174122281248153)
                ·
                  refine ⟨1324634031880591710936115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766178709174122281248153 1324634031880591710936115)
                  ·
                    refine ⟨1986951047820887566404173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324634031880591710936115 1986951047820887566404173)
                    ·
                      refine ⟨745106642932832837401565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1986951047820887566404173 745106642932832837401565)
                      ·
                        rfl

theorem cell23_1451090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1451090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451090 prefixEnd_1451090 := by exact prefixLift 1451090
  have htrace : WordTrace (prefixWord ++ tailWord_1451090) baseStart_1451090 baseEnd_1451090 := by
    simpa [prefixWord, tailWord_1451090, baseEnd_1451090] using wordTrace_append hprefix tailTrace_1451090
  have hstable : (prefixWord ++ tailWord_1451090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451090).length < 2 ^ (prefixWord ++ tailWord_1451090).sum := by decide
  have hdescent : baseEnd_1451090 < baseStart_1451090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451106 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1451106 : Nat := 118140960795 + 1451106 * 2 ^ 59
def prefixEnd_1451106 : Nat := 4983230072969 + 3 ^ 40 * 1451106 * 2
def baseEnd_1451106 : Nat := 248371619541101591600497

theorem tailTrace_1451106 : CollatzResearch.WordTrace tailWord_1451106 prefixEnd_1451106 248371619541101591600497 := by
  unfold tailWord_1451106
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231545970224566504805293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35284122587265510679480781 13231545970224566504805293)
  ·
    refine ⟨4961829738834212439301985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13231545970224566504805293 4961829738834212439301985)
    ·
      refine ⟨3721372304125659329476489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4961829738834212439301985 3721372304125659329476489)
      ·
        refine ⟨2791029228094244497107367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721372304125659329476489 2791029228094244497107367)
        ·
          refine ⟨4186543842141366745661051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791029228094244497107367 4186543842141366745661051)
          ·
            refine ⟨6279815763212050118491577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186543842141366745661051 6279815763212050118491577)
            ·
              refine ⟨4709861822409037588868683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6279815763212050118491577 4709861822409037588868683)
              ·
                refine ⟨7064792733613556383303025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709861822409037588868683 7064792733613556383303025)
                ·
                  refine ⟨5298594550210167287477269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064792733613556383303025 5298594550210167287477269)
                  ·
                    refine ⟨248371619541101591600497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5298594550210167287477269 248371619541101591600497)
                    ·
                      rfl

theorem cell23_1451106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1451106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451106 prefixEnd_1451106 := by exact prefixLift 1451106
  have htrace : WordTrace (prefixWord ++ tailWord_1451106) baseStart_1451106 baseEnd_1451106 := by
    simpa [prefixWord, tailWord_1451106, baseEnd_1451106] using wordTrace_append hprefix tailTrace_1451106
  have hstable : (prefixWord ++ tailWord_1451106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451106).length < 2 ^ (prefixWord ++ tailWord_1451106).sum := by decide
  have hdescent : baseEnd_1451106 < baseStart_1451106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451109 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1451109 : Nat := 118140960795 + 1451109 * 2 ^ 59
def prefixEnd_1451109 : Nat := 4983230072969 + 3 ^ 40 * 1451109 * 2
def baseEnd_1451109 : Nat := 745116399065268263063977

theorem tailTrace_1451109 : CollatzResearch.WordTrace tailWord_1451109 prefixEnd_1451109 745116399065268263063977 := by
  unfold tailWord_1451109
  simp only [CollatzResearch.WordTrace]
  refine ⟨52926293299887397531580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35284195533258265021053587 52926293299887397531580381)
  ·
    refine ⟨19847359987457774074342643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52926293299887397531580381 19847359987457774074342643)
    ·
      refine ⟨29771039981186661111513965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847359987457774074342643 29771039981186661111513965)
      ·
        refine ⟨11164139992944997916817737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29771039981186661111513965 11164139992944997916817737)
        ·
          refine ⟨8373104994708748437613303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164139992944997916817737 8373104994708748437613303)
          ·
            refine ⟨12559657492063122656419955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373104994708748437613303 12559657492063122656419955)
            ·
              refine ⟨18839486238094683984629933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559657492063122656419955 18839486238094683984629933)
              ·
                refine ⟨7064807339285506494236225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18839486238094683984629933 7064807339285506494236225)
                ·
                  refine ⟨5298605504464129870677169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064807339285506494236225 5298605504464129870677169)
                  ·
                    refine ⟨3973954128348097403007877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298605504464129870677169 3973954128348097403007877)
                    ·
                      refine ⟨745116399065268263063977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3973954128348097403007877 745116399065268263063977)
                      ·
                        rfl

theorem cell23_1451109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1451109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451109 prefixEnd_1451109 := by exact prefixLift 1451109
  have htrace : WordTrace (prefixWord ++ tailWord_1451109) baseStart_1451109 baseEnd_1451109 := by
    simpa [prefixWord, tailWord_1451109, baseEnd_1451109] using wordTrace_append hprefix tailTrace_1451109
  have hstable : (prefixWord ++ tailWord_1451109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451109).length < 2 ^ (prefixWord ++ tailWord_1451109).sum := by decide
  have hdescent : baseEnd_1451109 < baseStart_1451109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451113 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 4, 2]
def baseStart_1451113 : Nat := 118140960795 + 1451113 * 2 ^ 59
def prefixEnd_1451113 : Nat := 4983230072969 + 3 ^ 40 * 1451113 * 2
def baseEnd_1451113 : Nat := 745118452987886247413959

theorem tailTrace_1451113 : CollatzResearch.WordTrace tailWord_1451113 prefixEnd_1451113 745118452987886247413959 := by
  unfold tailWord_1451113
  simp only [CollatzResearch.WordTrace]
  refine ⟨52926439191872906214725993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35284292794581937476483995 52926439191872906214725993)
  ·
    refine ⟨39694829393904679661044495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52926439191872906214725993 39694829393904679661044495)
    ·
      refine ⟨59542244090857019491566743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39694829393904679661044495 59542244090857019491566743)
      ·
        refine ⟨89313366136285529237350115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59542244090857019491566743 89313366136285529237350115)
        ·
          refine ⟨133970049204428293856025173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89313366136285529237350115 133970049204428293856025173)
          ·
            refine ⟨1569961514114394068625295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 133970049204428293856025173 1569961514114394068625295)
            ·
              refine ⟨2354942271171591102937943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569961514114394068625295 2354942271171591102937943)
              ·
                refine ⟨3532413406757386654406915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2354942271171591102937943 3532413406757386654406915)
                ·
                  refine ⟨5298620110136079981610373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532413406757386654406915 5298620110136079981610373)
                  ·
                    refine ⟨993491270650514996551945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5298620110136079981610373 993491270650514996551945)
                    ·
                      refine ⟨745118452987886247413959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993491270650514996551945 745118452987886247413959)
                      ·
                        rfl

theorem cell23_1451113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4, 2].length) (baseStart_1451113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451113 prefixEnd_1451113 := by exact prefixLift 1451113
  have htrace : WordTrace (prefixWord ++ tailWord_1451113) baseStart_1451113 baseEnd_1451113 := by
    simpa [prefixWord, tailWord_1451113, baseEnd_1451113] using wordTrace_append hprefix tailTrace_1451113
  have hstable : (prefixWord ++ tailWord_1451113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451113).length < 2 ^ (prefixWord ++ tailWord_1451113).sum := by decide
  have hdescent : baseEnd_1451113 < baseStart_1451113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451136 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 5]
def baseStart_1451136 : Nat := 118140960795 + 1451136 * 2 ^ 59
def prefixEnd_1451136 : Nat := 4983230072969 + 3 ^ 40 * 1451136 * 2
def baseEnd_1451136 : Nat := 82792251449215517491817

theorem tailTrace_1451136 : CollatzResearch.WordTrace tailWord_1451136 prefixEnd_1451136 82792251449215517491817 := by
  unfold tailWord_1451136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463639035394790571406631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35284852047193054095208841 26463639035394790571406631)
  ·
    refine ⟨39695458553092185857109947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26463639035394790571406631 39695458553092185857109947)
    ·
      refine ⟨59543187829638278785664921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39695458553092185857109947 59543187829638278785664921)
      ·
        refine ⟨44657390872228709089248691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59543187829638278785664921 44657390872228709089248691)
        ·
          refine ⟨66986086308343063633873037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44657390872228709089248691 66986086308343063633873037)
          ·
            refine ⟨25119782365628648862702389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66986086308343063633873037 25119782365628648862702389)
            ·
              refine ⟨2354979596777685830878349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25119782365628648862702389 2354979596777685830878349)
              ·
                refine ⟨883117348791632186579381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354979596777685830878349 883117348791632186579381)
                ·
                  refine ⟨82792251449215517491817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883117348791632186579381 82792251449215517491817)
                  ·
                    rfl

theorem cell23_1451136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 5].length) (baseStart_1451136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451136 prefixEnd_1451136 := by exact prefixLift 1451136
  have htrace : WordTrace (prefixWord ++ tailWord_1451136) baseStart_1451136 baseEnd_1451136 := by
    simpa [prefixWord, tailWord_1451136, baseEnd_1451136] using wordTrace_append hprefix tailTrace_1451136
  have hstable : (prefixWord ++ tailWord_1451136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451136).length < 2 ^ (prefixWord ++ tailWord_1451136).sum := by decide
  have hdescent : baseEnd_1451136 < baseStart_1451136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451159 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1451159 : Nat := 118140960795 + 1451159 * 2 ^ 59
def prefixEnd_1451159 : Nat := 4983230072969 + 3 ^ 40 * 1451159 * 2
def baseEnd_1451159 : Nat := 745142073097993067438747

theorem tailTrace_1451159 : CollatzResearch.WordTrace tailWord_1451159 prefixEnd_1451159 745142073097993067438747 := by
  unfold tailWord_1451159
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928116949706256070900531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35285411299804170713933687 52928116949706256070900531)
  ·
    refine ⟨79392175424559384106350797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52928116949706256070900531 79392175424559384106350797)
    ·
      refine ⟨29772065784209769039881549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79392175424559384106350797 29772065784209769039881549)
      ·
        refine ⟨11164524669078663389955581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29772065784209769039881549 11164524669078663389955581)
        ·
          refine ⟨4186696750904498771233343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11164524669078663389955581 4186696750904498771233343)
          ·
            refine ⟨6280045126356748156850015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186696750904498771233343 6280045126356748156850015)
            ·
              refine ⟨9420067689535122235275023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280045126356748156850015 9420067689535122235275023)
              ·
                refine ⟨14130101534302683352912535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420067689535122235275023 14130101534302683352912535)
                ·
                  refine ⟨21195152301454025029368803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130101534302683352912535 21195152301454025029368803)
                  ·
                    refine ⟨31792728452181037544053205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21195152301454025029368803 31792728452181037544053205)
                    ·
                      refine ⟨745142073097993067438747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31792728452181037544053205 745142073097993067438747)
                      ·
                        rfl

theorem cell23_1451159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1451159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451159 prefixEnd_1451159 := by exact prefixLift 1451159
  have htrace : WordTrace (prefixWord ++ tailWord_1451159) baseStart_1451159 baseEnd_1451159 := by
    simpa [prefixWord, tailWord_1451159, baseEnd_1451159] using wordTrace_append hprefix tailTrace_1451159
  have hstable : (prefixWord ++ tailWord_1451159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451159).length < 2 ^ (prefixWord ++ tailWord_1451159).sum := by decide
  have hdescent : baseEnd_1451159 < baseStart_1451159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451186 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1451186 : Nat := 118140960795 + 1451186 * 2 ^ 59
def prefixEnd_1451186 : Nat := 4983230072969 + 3 ^ 40 * 1451186 * 2
def baseEnd_1451186 : Nat := 745155937075664461801123

theorem tailTrace_1451186 : CollatzResearch.WordTrace tailWord_1451186 prefixEnd_1451186 745155937075664461801123 := by
  unfold tailWord_1451186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232275430152109920533353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35286067813738959788088941 13232275430152109920533353)
  ·
    refine ⟨9924206572614082440400015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13232275430152109920533353 9924206572614082440400015)
    ·
      refine ⟨14886309858921123660600023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9924206572614082440400015 14886309858921123660600023)
      ·
        refine ⟨22329464788381685490900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14886309858921123660600023 22329464788381685490900035)
        ·
          refine ⟨33494197182572528236350053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22329464788381685490900035 33494197182572528236350053)
          ·
            refine ⟨6280161971732349044315635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33494197182572528236350053 6280161971732349044315635)
            ·
              refine ⟨9420242957598523566473453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280161971732349044315635 9420242957598523566473453)
              ·
                refine ⟨3532591109099446337427545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9420242957598523566473453 3532591109099446337427545)
                ·
                  refine ⟨2649443331824584753070659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3532591109099446337427545 2649443331824584753070659)
                  ·
                    refine ⟨3974164997736877129605989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2649443331824584753070659 3974164997736877129605989)
                    ·
                      refine ⟨745155937075664461801123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3974164997736877129605989 745155937075664461801123)
                      ·
                        rfl

theorem cell23_1451186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1451186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451186 prefixEnd_1451186 := by exact prefixLift 1451186
  have htrace : WordTrace (prefixWord ++ tailWord_1451186) baseStart_1451186 baseEnd_1451186 := by
    simpa [prefixWord, tailWord_1451186, baseEnd_1451186] using wordTrace_append hprefix tailTrace_1451186
  have hstable : (prefixWord ++ tailWord_1451186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451186).length < 2 ^ (prefixWord ++ tailWord_1451186).sum := by decide
  have hdescent : baseEnd_1451186 < baseStart_1451186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451249 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_1451249 : Nat := 118140960795 + 1451249 * 2 ^ 59
def prefixEnd_1451249 : Nat := 4983230072969 + 3 ^ 40 * 1451249 * 2
def baseEnd_1451249 : Nat := 745188286356897715313333

theorem tailTrace_1451249 : CollatzResearch.WordTrace tailWord_1451249 prefixEnd_1451249 745188286356897715313333 := by
  unfold tailWord_1451249
  simp only [CollatzResearch.WordTrace]
  refine ⟨52931399519380201441676801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35287599679586800961117867 52931399519380201441676801)
  ·
    refine ⟨39698549639535151081257601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52931399519380201441676801 39698549639535151081257601)
    ·
      refine ⟨29773912229651363310943201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39698549639535151081257601 29773912229651363310943201)
      ·
        refine ⟨22330434172238522483207401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29773912229651363310943201 22330434172238522483207401)
        ·
          refine ⟨16747825629178891862405551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22330434172238522483207401 16747825629178891862405551)
          ·
            refine ⟨25121738443768337793608327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16747825629178891862405551 25121738443768337793608327)
            ·
              refine ⟨37682607665652506690412491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25121738443768337793608327 37682607665652506690412491)
              ·
                refine ⟨56523911498478760035618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37682607665652506690412491 56523911498478760035618737)
                ·
                  refine ⟨42392933623859070026714053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56523911498478760035618737 42392933623859070026714053)
                  ·
                    refine ⟨7948675054473575630008885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42392933623859070026714053 7948675054473575630008885)
                    ·
                      refine ⟨745188286356897715313333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7948675054473575630008885 745188286356897715313333)
                      ·
                        rfl

theorem cell23_1451249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_1451249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451249 prefixEnd_1451249 := by exact prefixLift 1451249
  have htrace : WordTrace (prefixWord ++ tailWord_1451249) baseStart_1451249 baseEnd_1451249 := by
    simpa [prefixWord, tailWord_1451249, baseEnd_1451249] using wordTrace_append hprefix tailTrace_1451249
  have hstable : (prefixWord ++ tailWord_1451249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451249).length < 2 ^ (prefixWord ++ tailWord_1451249).sum := by decide
  have hdescent : baseEnd_1451249 < baseStart_1451249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451260 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 6]
def baseStart_1451260 : Nat := 118140960795 + 1451260 * 2 ^ 59
def prefixEnd_1451260 : Nat := 4983230072969 + 3 ^ 40 * 1451260 * 2
def baseEnd_1451260 : Nat := 82799326071566352475087

theorem tailTrace_1451260 : CollatzResearch.WordTrace tailWord_1451260 prefixEnd_1451260 82799326071566352475087 := by
  unfold tailWord_1451260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26465900361170175160163617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35287867148226900213551489 26465900361170175160163617)
  ·
    refine ⟨19849425270877631370122713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26465900361170175160163617 19849425270877631370122713)
    ·
      refine ⟨14887068953158223527592035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19849425270877631370122713 14887068953158223527592035)
      ·
        refine ⟨22330603429737335291388053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14887068953158223527592035 22330603429737335291388053)
        ·
          refine ⟨1046747035768937591783815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22330603429737335291388053 1046747035768937591783815)
          ·
            refine ⟨1570120553653406387675723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046747035768937591783815 1570120553653406387675723)
            ·
              refine ⟨2355180830480109581513585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570120553653406387675723 2355180830480109581513585)
              ·
                refine ⟨1766385622860082186135189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355180830480109581513585 1766385622860082186135189)
                ·
                  refine ⟨82799326071566352475087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1766385622860082186135189 82799326071566352475087)
                  ·
                    rfl

theorem cell23_1451260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_1451260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451260 prefixEnd_1451260 := by exact prefixLift 1451260
  have htrace : WordTrace (prefixWord ++ tailWord_1451260) baseStart_1451260 baseEnd_1451260 := by
    simpa [prefixWord, tailWord_1451260, baseEnd_1451260] using wordTrace_append hprefix tailTrace_1451260
  have hstable : (prefixWord ++ tailWord_1451260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451260).length < 2 ^ (prefixWord ++ tailWord_1451260).sum := by decide
  have hdescent : baseEnd_1451260 < baseStart_1451260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451304 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1451304 : Nat := 118140960795 + 1451304 * 2 ^ 59
def prefixEnd_1451304 : Nat := 4983230072969 + 3 ^ 40 * 1451304 * 2
def baseEnd_1451304 : Nat := 745216527792895000125581

theorem tailTrace_1451304 : CollatzResearch.WordTrace tailWord_1451304 prefixEnd_1451304 745216527792895000125581 := by
  unfold tailWord_1451304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466702767090472917464483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35288937022787297223285977 26466702767090472917464483)
  ·
    refine ⟨39700054150635709376196725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26466702767090472917464483 39700054150635709376196725)
    ·
      refine ⟨3721880076622097754018443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39700054150635709376196725 3721880076622097754018443)
      ·
        refine ⟨5582820114933146631027665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721880076622097754018443 5582820114933146631027665)
        ·
          refine ⟨4187115086199859973270749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582820114933146631027665 4187115086199859973270749)
          ·
            refine ⟨1570168157324947489976531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4187115086199859973270749 1570168157324947489976531)
            ·
              refine ⟨2355252235987421234964797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570168157324947489976531 2355252235987421234964797)
              ·
                refine ⟨883219588495282963111799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355252235987421234964797 883219588495282963111799)
                ·
                  refine ⟨1324829382742924444667699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883219588495282963111799 1324829382742924444667699)
                  ·
                    refine ⟨1987244074114386667001549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324829382742924444667699 1987244074114386667001549)
                    ·
                      refine ⟨745216527792895000125581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987244074114386667001549 745216527792895000125581)
                      ·
                        rfl

theorem cell23_1451304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1451304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451304 prefixEnd_1451304 := by exact prefixLift 1451304
  have htrace : WordTrace (prefixWord ++ tailWord_1451304) baseStart_1451304 baseEnd_1451304 := by
    simpa [prefixWord, tailWord_1451304, baseEnd_1451304] using wordTrace_append hprefix tailTrace_1451304
  have hstable : (prefixWord ++ tailWord_1451304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451304).length < 2 ^ (prefixWord ++ tailWord_1451304).sum := by decide
  have hdescent : baseEnd_1451304 < baseStart_1451304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451313 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1451313 : Nat := 118140960795 + 1451313 * 2 ^ 59
def prefixEnd_1451313 : Nat := 4983230072969 + 3 ^ 40 * 1451313 * 2
def baseEnd_1451313 : Nat := 745221149118785464913039

theorem tailTrace_1451313 : CollatzResearch.WordTrace tailWord_1451313 prefixEnd_1451313 745221149118785464913039 := by
  unfold tailWord_1451313
  simp only [CollatzResearch.WordTrace]
  refine ⟨52933733791148340372006593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35289155860765560248004395 52933733791148340372006593)
  ·
    refine ⟨39700300343361255279004945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52933733791148340372006593 39700300343361255279004945)
    ·
      refine ⟨29775225257520941459253709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39700300343361255279004945 29775225257520941459253709)
      ·
        refine ⟨11165709471570353047220141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29775225257520941459253709 11165709471570353047220141)
        ·
          refine ⟨4187141051838882392707553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11165709471570353047220141 4187141051838882392707553)
          ·
            refine ⟨3140355788879161794530665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187141051838882392707553 3140355788879161794530665)
            ·
              refine ⟨2355266841659371345897999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140355788879161794530665 2355266841659371345897999)
              ·
                refine ⟨3532900262489057018846999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355266841659371345897999 3532900262489057018846999)
                ·
                  refine ⟨5299350393733585528270499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532900262489057018846999 5299350393733585528270499)
                  ·
                    refine ⟨7949025590600378292405749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299350393733585528270499 7949025590600378292405749)
                    ·
                      refine ⟨745221149118785464913039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7949025590600378292405749 745221149118785464913039)
                      ·
                        rfl

theorem cell23_1451313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1451313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451313 prefixEnd_1451313 := by exact prefixLift 1451313
  have htrace : WordTrace (prefixWord ++ tailWord_1451313) baseStart_1451313 baseEnd_1451313 := by
    simpa [prefixWord, tailWord_1451313, baseEnd_1451313] using wordTrace_append hprefix tailTrace_1451313
  have hstable : (prefixWord ++ tailWord_1451313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451313).length < 2 ^ (prefixWord ++ tailWord_1451313).sum := by decide
  have hdescent : baseEnd_1451313 < baseStart_1451313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451327 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 3, 2, 2]
def baseStart_1451327 : Nat := 118140960795 + 1451327 * 2 ^ 59
def prefixEnd_1451327 : Nat := 4983230072969 + 3 ^ 40 * 1451327 * 2
def baseEnd_1451327 : Nat := 745228337847948410137975

theorem tailTrace_1451327 : CollatzResearch.WordTrace tailWord_1451327 prefixEnd_1451327 745228337847948410137975 := by
  unfold tailWord_1451327
  simp only [CollatzResearch.WordTrace]
  refine ⟨52934244413097620763016235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35289496275398413842010823 52934244413097620763016235)
  ·
    refine ⟨79401366619646431144524353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52934244413097620763016235 79401366619646431144524353)
    ·
      refine ⟨59551024964734823358393265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79401366619646431144524353 59551024964734823358393265)
      ·
        refine ⟨44663268723551117518794949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59551024964734823358393265 44663268723551117518794949)
        ·
          refine ⟨8374362885665834534774053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44663268723551117518794949 8374362885665834534774053)
          ·
            refine ⟨1570193041062343975270135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8374362885665834534774053 1570193041062343975270135)
            ·
              refine ⟨2355289561593515962905203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570193041062343975270135 2355289561593515962905203)
              ·
                refine ⟨3532934342390273944357805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355289561593515962905203 3532934342390273944357805)
                ·
                  refine ⟨1324850378396352729134177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3532934342390273944357805 1324850378396352729134177)
                  ·
                    refine ⟨993637783797264546850633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1324850378396352729134177 993637783797264546850633)
                    ·
                      refine ⟨745228337847948410137975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993637783797264546850633 745228337847948410137975)
                      ·
                        rfl

theorem cell23_1451327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_1451327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451327 prefixEnd_1451327 := by exact prefixLift 1451327
  have htrace : WordTrace (prefixWord ++ tailWord_1451327) baseStart_1451327 baseEnd_1451327 := by
    simpa [prefixWord, tailWord_1451327, baseEnd_1451327] using wordTrace_append hprefix tailTrace_1451327
  have hstable : (prefixWord ++ tailWord_1451327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451327).length < 2 ^ (prefixWord ++ tailWord_1451327).sum := by decide
  have hdescent : baseEnd_1451327 < baseStart_1451327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451376 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_1451376 : Nat := 118140960795 + 1451376 * 2 ^ 59
def prefixEnd_1451376 : Nat := 4983230072969 + 3 ^ 40 * 1451376 * 2
def baseEnd_1451376 : Nat := 248417832800006239475083

theorem tailTrace_1451376 : CollatzResearch.WordTrace tailWord_1451376 prefixEnd_1451376 248417832800006239475083 := by
  unfold tailWord_1451376
  simp only [CollatzResearch.WordTrace]
  refine ⟨26468015794960051065774991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35290687726613401421033321 26468015794960051065774991)
  ·
    refine ⟨39702023692440076598662487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26468015794960051065774991 39702023692440076598662487)
    ·
      refine ⟨59553035538660114897993731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39702023692440076598662487 59553035538660114897993731)
      ·
        refine ⟨89329553307990172346990597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59553035538660114897993731 89329553307990172346990597)
        ·
          refine ⟨16749291245248157315060737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89329553307990172346990597 16749291245248157315060737)
          ·
            refine ⟨12561968433936117986295553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16749291245248157315060737 12561968433936117986295553)
            ·
              refine ⟨9421476325452088489721665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12561968433936117986295553 9421476325452088489721665)
              ·
                refine ⟨7066107244089066367291249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421476325452088489721665 7066107244089066367291249)
                ·
                  refine ⟨5299580433066799775468437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7066107244089066367291249 5299580433066799775468437)
                  ·
                    refine ⟨248417832800006239475083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5299580433066799775468437 248417832800006239475083)
                    ·
                      rfl

theorem cell23_1451376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_1451376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451376 prefixEnd_1451376 := by exact prefixLift 1451376
  have htrace : WordTrace (prefixWord ++ tailWord_1451376) baseStart_1451376 baseEnd_1451376 := by
    simpa [prefixWord, tailWord_1451376, baseEnd_1451376] using wordTrace_append hprefix tailTrace_1451376
  have hstable : (prefixWord ++ tailWord_1451376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451376).length < 2 ^ (prefixWord ++ tailWord_1451376).sum := by decide
  have hdescent : baseEnd_1451376 < baseStart_1451376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451383 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_1451383 : Nat := 118140960795 + 1451383 * 2 ^ 59
def prefixEnd_1451383 : Nat := 4983230072969 + 3 ^ 40 * 1451383 * 2
def baseEnd_1451383 : Nat := 745257092764600191037717

theorem tailTrace_1451383 : CollatzResearch.WordTrace tailWord_1451383 prefixEnd_1451383 745257092764600191037717 := by
  unfold tailWord_1451383
  simp only [CollatzResearch.WordTrace]
  refine ⟨52936286900894742327054803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35290857933929828218036535 52936286900894742327054803)
  ·
    refine ⟨79404430351342113490582205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52936286900894742327054803 79404430351342113490582205)
    ·
      refine ⟨29776661381753292558968327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79404430351342113490582205 29776661381753292558968327)
      ·
        refine ⟨44664992072629938838452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29776661381753292558968327 44664992072629938838452491)
        ·
          refine ⟨66997488108944908257678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44664992072629938838452491 66997488108944908257678737)
          ·
            refine ⟨50248116081708681193259053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66997488108944908257678737 50248116081708681193259053)
            ·
              refine ⟨18843043530640755447472145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50248116081708681193259053 18843043530640755447472145)
              ·
                refine ⟨14132282647980566585604109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18843043530640755447472145 14132282647980566585604109)
                ·
                  refine ⟨5299605992992712469601541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14132282647980566585604109 5299605992992712469601541)
                  ·
                    refine ⟨993676123686133588050289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299605992992712469601541 993676123686133588050289)
                    ·
                      refine ⟨745257092764600191037717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993676123686133588050289 745257092764600191037717)
                      ·
                        rfl

theorem cell23_1451383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_1451383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451383 prefixEnd_1451383 := by exact prefixLift 1451383
  have htrace : WordTrace (prefixWord ++ tailWord_1451383) baseStart_1451383 baseEnd_1451383 := by
    simpa [prefixWord, tailWord_1451383, baseEnd_1451383] using wordTrace_append hprefix tailTrace_1451383
  have hstable : (prefixWord ++ tailWord_1451383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451383).length < 2 ^ (prefixWord ++ tailWord_1451383).sum := by decide
  have hdescent : baseEnd_1451383 < baseStart_1451383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451394 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1451394 : Nat := 118140960795 + 1451394 * 2 ^ 59
def prefixEnd_1451394 : Nat := 4983230072969 + 3 ^ 40 * 1451394 * 2
def baseEnd_1451394 : Nat := 745262741051799648000167

theorem tailTrace_1451394 : CollatzResearch.WordTrace tailWord_1451394 prefixEnd_1451394 745262741051799648000167 := by
  unfold tailWord_1451394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234172025963722801426309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35291125402569927470470157 13234172025963722801426309)
  ·
    refine ⟨2481407254868198025267433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13234172025963722801426309 2481407254868198025267433)
    ·
      refine ⟨1861055441151148518950575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2481407254868198025267433 1861055441151148518950575)
      ·
        refine ⟨2791583161726722778425863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861055441151148518950575 2791583161726722778425863)
        ·
          refine ⟨4187374742590084167638795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791583161726722778425863 4187374742590084167638795)
          ·
            refine ⟨6281062113885126251458193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187374742590084167638795 6281062113885126251458193)
            ·
              refine ⟨4710796585413844688593645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281062113885126251458193 4710796585413844688593645)
              ·
                refine ⟨1766548719530191758222617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4710796585413844688593645 1766548719530191758222617)
                ·
                  refine ⟨1324911539647643818666963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766548719530191758222617 1324911539647643818666963)
                  ·
                    refine ⟨1987367309471465728000445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1324911539647643818666963 1987367309471465728000445)
                    ·
                      refine ⟨745262741051799648000167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987367309471465728000445 745262741051799648000167)
                      ·
                        rfl

theorem cell23_1451394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1451394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451394 prefixEnd_1451394 := by exact prefixLift 1451394
  have htrace : WordTrace (prefixWord ++ tailWord_1451394) baseStart_1451394 baseEnd_1451394 := by
    simpa [prefixWord, tailWord_1451394, baseEnd_1451394] using wordTrace_append hprefix tailTrace_1451394
  have hstable : (prefixWord ++ tailWord_1451394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451394).length < 2 ^ (prefixWord ++ tailWord_1451394).sum := by decide
  have hdescent : baseEnd_1451394 < baseStart_1451394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451400 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1451400 : Nat := 118140960795 + 1451400 * 2 ^ 59
def prefixEnd_1451400 : Nat := 4983230072969 + 3 ^ 40 * 1451400 * 2
def baseEnd_1451400 : Nat := 745265821935726624525139

theorem tailTrace_1451400 : CollatzResearch.WordTrace tailWord_1451400 prefixEnd_1451400 745265821935726624525139 := by
  unfold tailWord_1451400
  simp only [CollatzResearch.WordTrace]
  refine ⟨26468453470916577115211827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35291271294555436153615769 26468453470916577115211827)
  ·
    refine ⟨39702680206374865672817741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26468453470916577115211827 39702680206374865672817741)
    ·
      refine ⟨14888505077390574627306653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39702680206374865672817741 14888505077390574627306653)
      ·
        refine ⟨5583189404021465485239995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14888505077390574627306653 5583189404021465485239995)
        ·
          refine ⟨8374784106032198227859993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583189404021465485239995 8374784106032198227859993)
          ·
            refine ⟨6281088079524148670894995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374784106032198227859993 6281088079524148670894995)
            ·
              refine ⟨9421632119286223006342493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281088079524148670894995 9421632119286223006342493)
              ·
                refine ⟨3533112044732333627378435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421632119286223006342493 3533112044732333627378435)
                ·
                  refine ⟨5299668067098500441067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533112044732333627378435 5299668067098500441067653)
                  ·
                    refine ⟨993687762580968832700185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299668067098500441067653 993687762580968832700185)
                    ·
                      refine ⟨745265821935726624525139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993687762580968832700185 745265821935726624525139)
                      ·
                        rfl

theorem cell23_1451400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1451400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451400 prefixEnd_1451400 := by exact prefixLift 1451400
  have htrace : WordTrace (prefixWord ++ tailWord_1451400) baseStart_1451400 baseEnd_1451400 := by
    simpa [prefixWord, tailWord_1451400, baseEnd_1451400] using wordTrace_append hprefix tailTrace_1451400
  have hstable : (prefixWord ++ tailWord_1451400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451400).length < 2 ^ (prefixWord ++ tailWord_1451400).sum := by decide
  have hdescent : baseEnd_1451400 < baseStart_1451400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451443 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 7, 2]
def baseStart_1451443 : Nat := 118140960795 + 1451443 * 2 ^ 59
def prefixEnd_1451443 : Nat := 4983230072969 + 3 ^ 40 * 1451443 * 2
def baseEnd_1451443 : Nat := 745287901603869956287441

theorem tailTrace_1451443 : CollatzResearch.WordTrace tailWord_1451443 prefixEnd_1451443 745287901603869956287441 := by
  unfold tailWord_1451443
  simp only [CollatzResearch.WordTrace]
  refine ⟨52938475280677372574238983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35292316853784915049492655 52938475280677372574238983)
  ·
    refine ⟨79407712921016058861358475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52938475280677372574238983 79407712921016058861358475)
    ·
      refine ⟨119111569381524088292037713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79407712921016058861358475 119111569381524088292037713)
      ·
        refine ⟨89333677036143066219028285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119111569381524088292037713 89333677036143066219028285)
        ·
          refine ⟨33500128888553649832135607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89333677036143066219028285 33500128888553649832135607)
          ·
            refine ⟨50250193332830474748203411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33500128888553649832135607 50250193332830474748203411)
            ·
              refine ⟨75375289999245712122305117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50250193332830474748203411 75375289999245712122305117)
              ·
                refine ⟨28265733749717142045864419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75375289999245712122305117 28265733749717142045864419)
                ·
                  refine ⟨42398600624575713068796629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28265733749717142045864419 42398600624575713068796629)
                  ·
                    refine ⟨993717202138493275049921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42398600624575713068796629 993717202138493275049921)
                    ·
                      refine ⟨745287901603869956287441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993717202138493275049921 745287901603869956287441)
                      ·
                        rfl

theorem cell23_1451443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7, 2].length) (baseStart_1451443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451443 prefixEnd_1451443 := by exact prefixLift 1451443
  have htrace : WordTrace (prefixWord ++ tailWord_1451443) baseStart_1451443 baseEnd_1451443 := by
    simpa [prefixWord, tailWord_1451443, baseEnd_1451443] using wordTrace_append hprefix tailTrace_1451443
  have hstable : (prefixWord ++ tailWord_1451443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451443).length < 2 ^ (prefixWord ++ tailWord_1451443).sum := by decide
  have hdescent : baseEnd_1451443 < baseStart_1451443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451527 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1451527 : Nat := 118140960795 + 1451527 * 2 ^ 59
def prefixEnd_1451527 : Nat := 4983230072969 + 3 ^ 40 * 1451527 * 2
def baseEnd_1451527 : Nat := 745331033978847627637055

theorem tailTrace_1451527 : CollatzResearch.WordTrace tailWord_1451527 prefixEnd_1451527 745331033978847627637055 := by
  unfold tailWord_1451527
  simp only [CollatzResearch.WordTrace]
  refine ⟨52941539012373054920296835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35294359341582036613531223 52941539012373054920296835)
  ·
    refine ⟨79412308518559582380445253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52941539012373054920296835 79412308518559582380445253)
    ·
      refine ⟨14889807847229921696333485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79412308518559582380445253 14889807847229921696333485)
      ·
        refine ⟨5583677942711220636125057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14889807847229921696333485 5583677942711220636125057)
        ·
          refine ⟨4187758457033415477093793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5583677942711220636125057 4187758457033415477093793)
          ·
            refine ⟨3140818842775061607820345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187758457033415477093793 3140818842775061607820345)
            ·
              refine ⟨2355614132081296205865259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140818842775061607820345 2355614132081296205865259)
              ·
                refine ⟨3533421198121944308797889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355614132081296205865259 3533421198121944308797889)
                ·
                  refine ⟨2650065898591458231598417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3533421198121944308797889 2650065898591458231598417)
                  ·
                    refine ⟨1987549423943593673698813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650065898591458231598417 1987549423943593673698813)
                    ·
                      refine ⟨745331033978847627637055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987549423943593673698813 745331033978847627637055)
                      ·
                        rfl

theorem cell23_1451527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1451527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451527 prefixEnd_1451527 := by exact prefixLift 1451527
  have htrace : WordTrace (prefixWord ++ tailWord_1451527) baseStart_1451527 baseEnd_1451527 := by
    simpa [prefixWord, tailWord_1451527, baseEnd_1451527] using wordTrace_append hprefix tailTrace_1451527
  have hstable : (prefixWord ++ tailWord_1451527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451527).length < 2 ^ (prefixWord ++ tailWord_1451527).sum := by decide
  have hdescent : baseEnd_1451527 < baseStart_1451527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451591 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_1451591 : Nat := 118140960795 + 1451591 * 2 ^ 59
def prefixEnd_1451591 : Nat := 4983230072969 + 3 ^ 40 * 1451591 * 2
def baseEnd_1451591 : Nat := 745363896740735377236761

theorem tailTrace_1451591 : CollatzResearch.WordTrace tailWord_1451591 prefixEnd_1451591 745363896740735377236761 := by
  unfold tailWord_1451591
  simp only [CollatzResearch.WordTrace]
  refine ⟨52943873284141193850626627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35295915522760795900417751 52943873284141193850626627)
  ·
    refine ⟨79415809926211790775939941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52943873284141193850626627 79415809926211790775939941)
    ·
      refine ⟨14890464361164710770488739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79415809926211790775939941 14890464361164710770488739)
      ·
        refine ⟨22335696541747066155733109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890464361164710770488739 22335696541747066155733109)
        ·
          refine ⟨2093971550788787452099979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22335696541747066155733109 2093971550788787452099979)
          ·
            refine ⟨3140957326183181178149969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093971550788787452099979 3140957326183181178149969)
            ·
              refine ⟨2355717994637385883612477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140957326183181178149969 2355717994637385883612477)
              ·
                refine ⟨883394247989019706354679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355717994637385883612477 883394247989019706354679)
                ·
                  refine ⟨1325091371983529559532019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883394247989019706354679 1325091371983529559532019)
                  ·
                    refine ⟨1987637057975294339298029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325091371983529559532019 1987637057975294339298029)
                    ·
                      refine ⟨745363896740735377236761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987637057975294339298029 745363896740735377236761)
                      ·
                        rfl

theorem cell23_1451591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_1451591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451591 prefixEnd_1451591 := by exact prefixLift 1451591
  have htrace : WordTrace (prefixWord ++ tailWord_1451591) baseStart_1451591 baseEnd_1451591 := by
    simpa [prefixWord, tailWord_1451591, baseEnd_1451591] using wordTrace_append hprefix tailTrace_1451591
  have hstable : (prefixWord ++ tailWord_1451591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451591).length < 2 ^ (prefixWord ++ tailWord_1451591).sum := by decide
  have hdescent : baseEnd_1451591 < baseStart_1451591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451607 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 2, 4]
def baseStart_1451607 : Nat := 118140960795 + 1451607 * 2 ^ 59
def prefixEnd_1451607 : Nat := 4983230072969 + 3 ^ 40 * 1451607 * 2
def baseEnd_1451607 : Nat := 248457370810402438212229

theorem tailTrace_1451607 : CollatzResearch.WordTrace tailWord_1451607 prefixEnd_1451607 248457370810402438212229 := by
  unfold tailWord_1451607
  simp only [CollatzResearch.WordTrace]
  refine ⟨52944456852083228583209075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35296304568055485722139383 52944456852083228583209075)
  ·
    refine ⟨79416685278124842874813613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52944456852083228583209075 79416685278124842874813613)
    ·
      refine ⟨29781256979296816078055105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79416685278124842874813613 29781256979296816078055105)
      ·
        refine ⟨22335942734472612058541329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29781256979296816078055105 22335942734472612058541329)
        ·
          refine ⟨16751957050854459043905997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22335942734472612058541329 16751957050854459043905997)
          ·
            refine ⟨6281983894070422141464749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16751957050854459043905997 6281983894070422141464749)
            ·
              refine ⟨2355743960276408303049281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6281983894070422141464749 2355743960276408303049281)
              ·
                refine ⟨1766807970207306227286961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355743960276408303049281 1766807970207306227286961)
                ·
                  refine ⟨1325105977655479670465221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766807970207306227286961 1325105977655479670465221)
                  ·
                    refine ⟨248457370810402438212229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325105977655479670465221 248457370810402438212229)
                    ·
                      rfl

theorem cell23_1451607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_1451607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451607 prefixEnd_1451607 := by exact prefixLift 1451607
  have htrace : WordTrace (prefixWord ++ tailWord_1451607) baseStart_1451607 baseEnd_1451607 := by
    simpa [prefixWord, tailWord_1451607, baseEnd_1451607] using wordTrace_append hprefix tailTrace_1451607
  have hstable : (prefixWord ++ tailWord_1451607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451607).length < 2 ^ (prefixWord ++ tailWord_1451607).sum := by decide
  have hdescent : baseEnd_1451607 < baseStart_1451607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451633 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 7]
def baseStart_1451633 : Nat := 118140960795 + 1451633 * 2 ^ 59
def prefixEnd_1451633 : Nat := 4983230072969 + 3 ^ 40 * 1451633 * 2
def baseEnd_1451633 : Nat := 248461820976074737637189

theorem tailTrace_1451633 : CollatzResearch.WordTrace tailWord_1451633 prefixEnd_1451633 248461820976074737637189 := by
  unfold tailWord_1451633
  simp only [CollatzResearch.WordTrace]
  refine ⟨52945405149989035023655553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35296936766659356682437035 52945405149989035023655553)
  ·
    refine ⟨39709053862491776267741665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52945405149989035023655553 39709053862491776267741665)
    ·
      refine ⟨29781790396868832200806249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39709053862491776267741665 29781790396868832200806249)
      ·
        refine ⟨22336342797651624150604687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29781790396868832200806249 22336342797651624150604687)
        ·
          refine ⟨33504514196477436225907031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336342797651624150604687 33504514196477436225907031)
          ·
            refine ⟨50256771294716154338860547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33504514196477436225907031 50256771294716154338860547)
            ·
              refine ⟨75385156942074231508290821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50256771294716154338860547 75385156942074231508290821)
              ·
                refine ⟨14134716926638918407804529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75385156942074231508290821 14134716926638918407804529)
                ·
                  refine ⟨10601037694979188805853397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134716926638918407804529 10601037694979188805853397)
                  ·
                    refine ⟨248461820976074737637189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10601037694979188805853397 248461820976074737637189)
                    ·
                      rfl

theorem cell23_1451633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_1451633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451633 prefixEnd_1451633 := by exact prefixLift 1451633
  have htrace : WordTrace (prefixWord ++ tailWord_1451633) baseStart_1451633 baseEnd_1451633 := by
    simpa [prefixWord, tailWord_1451633, baseEnd_1451633] using wordTrace_append hprefix tailTrace_1451633
  have hstable : (prefixWord ++ tailWord_1451633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451633).length < 2 ^ (prefixWord ++ tailWord_1451633).sum := by decide
  have hdescent : baseEnd_1451633 < baseStart_1451633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451634 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1451634 : Nat := 118140960795 + 1451634 * 2 ^ 59
def prefixEnd_1451634 : Nat := 4983230072969 + 3 ^ 40 * 1451634 * 2
def baseEnd_1451634 : Nat := 745385976408878708999063

theorem tailTrace_1451634 : CollatzResearch.WordTrace tailWord_1451634 prefixEnd_1451634 745385976408878708999063 := by
  unfold tailWord_1451634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236360405746353048610489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35296961081990274796294637 13236360405746353048610489)
  ·
    refine ⟨9927270304309764786457867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13236360405746353048610489 9927270304309764786457867)
    ·
      refine ⟨14890905456464647179686801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9927270304309764786457867 14890905456464647179686801)
      ·
        refine ⟨11168179092348485384765101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14890905456464647179686801 11168179092348485384765101)
        ·
          refine ⟨4188067159630682019286913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11168179092348485384765101 4188067159630682019286913)
          ·
            refine ⟨3141050369723011514465185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4188067159630682019286913 3141050369723011514465185)
            ·
              refine ⟨2355787777292258635848889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141050369723011514465185 2355787777292258635848889)
              ·
                refine ⟨1766840832969193976886667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355787777292258635848889 1766840832969193976886667)
                ·
                  refine ⟨2650261249453790965330001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1766840832969193976886667 2650261249453790965330001)
                  ·
                    refine ⟨1987695937090343223997501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650261249453790965330001 1987695937090343223997501)
                    ·
                      refine ⟨745385976408878708999063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987695937090343223997501 745385976408878708999063)
                      ·
                        rfl

theorem cell23_1451634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1451634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451634 prefixEnd_1451634 := by exact prefixLift 1451634
  have htrace : WordTrace (prefixWord ++ tailWord_1451634) baseStart_1451634 baseEnd_1451634 := by
    simpa [prefixWord, tailWord_1451634, baseEnd_1451634] using wordTrace_append hprefix tailTrace_1451634
  have hstable : (prefixWord ++ tailWord_1451634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451634).length < 2 ^ (prefixWord ++ tailWord_1451634).sum := by decide
  have hdescent : baseEnd_1451634 < baseStart_1451634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451637 : List Nat := [1, 3, 4, 2, 1, 1, 4, 7]
def baseStart_1451637 : Nat := 118140960795 + 1451637 * 2 ^ 59
def prefixEnd_1451637 : Nat := 4983230072969 + 3 ^ 40 * 1451637 * 2
def baseEnd_1451637 : Nat := 27606945068549711009687

theorem tailTrace_1451637 : CollatzResearch.WordTrace tailWord_1451637 prefixEnd_1451637 27606945068549711009687 := by
  unfold tailWord_1451637
  simp only [CollatzResearch.WordTrace]
  refine ⟨52945551041974543706801165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35297034027983029137867443 52945551041974543706801165)
  ·
    refine ⟨19854581640740453890050437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52945551041974543706801165 19854581640740453890050437)
    ·
      refine ⟨3722734057638835104384457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19854581640740453890050437 3722734057638835104384457)
      ·
        refine ⟨2792050543229126328288343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3722734057638835104384457 2792050543229126328288343)
        ·
          refine ⟨4188075814843689492432515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792050543229126328288343 4188075814843689492432515)
          ·
            refine ⟨6282113722265534238648773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188075814843689492432515 6282113722265534238648773)
            ·
              refine ⟨1177896322924787669746645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6282113722265534238648773 1177896322924787669746645)
              ·
                refine ⟨27606945068549711009687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1177896322924787669746645 27606945068549711009687)
                ·
                  rfl

theorem cell23_1451637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 7].length) (baseStart_1451637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451637 prefixEnd_1451637 := by exact prefixLift 1451637
  have htrace : WordTrace (prefixWord ++ tailWord_1451637) baseStart_1451637 baseEnd_1451637 := by
    simpa [prefixWord, tailWord_1451637, baseEnd_1451637] using wordTrace_append hprefix tailTrace_1451637
  have hstable : (prefixWord ++ tailWord_1451637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451637).length < 2 ^ (prefixWord ++ tailWord_1451637).sum := by decide
  have hdescent : baseEnd_1451637 < baseStart_1451637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451643 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5]
def baseStart_1451643 : Nat := 118140960795 + 1451643 * 2 ^ 59
def prefixEnd_1451643 : Nat := 4983230072969 + 3 ^ 40 * 1451643 * 2
def baseEnd_1451643 : Nat := 745390597734769173786521

theorem tailTrace_1451643 : CollatzResearch.WordTrace tailWord_1451643 prefixEnd_1451643 745390597734769173786521 := by
  unfold tailWord_1451643
  simp only [CollatzResearch.WordTrace]
  refine ⟨52945769879952806731519583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35297179919968537821013055 52945769879952806731519583)
  ·
    refine ⟨79418654819929210097279375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52945769879952806731519583 79418654819929210097279375)
    ·
      refine ⟨119127982229893815145919063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79418654819929210097279375 119127982229893815145919063)
      ·
        refine ⟨178691973344840722718878595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119127982229893815145919063 178691973344840722718878595)
        ·
          refine ⟨268037960017261084078317893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178691973344840722718878595 268037960017261084078317893)
          ·
            refine ⟨50257117503236453264684605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268037960017261084078317893 50257117503236453264684605)
            ·
              refine ⟨18846419063713669974256727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50257117503236453264684605 18846419063713669974256727)
              ·
                refine ⟨28269628595570504961385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18846419063713669974256727 28269628595570504961385091)
                ·
                  refine ⟨42404442893355757442077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28269628595570504961385091 42404442893355757442077637)
                  ·
                    refine ⟨7950833042504204520389557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42404442893355757442077637 7950833042504204520389557)
                    ·
                      refine ⟨745390597734769173786521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7950833042504204520389557 745390597734769173786521)
                      ·
                        rfl

theorem cell23_1451643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_1451643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451643 prefixEnd_1451643 := by exact prefixLift 1451643
  have htrace : WordTrace (prefixWord ++ tailWord_1451643) baseStart_1451643 baseEnd_1451643 := by
    simpa [prefixWord, tailWord_1451643, baseEnd_1451643] using wordTrace_append hprefix tailTrace_1451643
  have hstable : (prefixWord ++ tailWord_1451643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451643).length < 2 ^ (prefixWord ++ tailWord_1451643).sum := by decide
  have hdescent : baseEnd_1451643 < baseStart_1451643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451681 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1451681 : Nat := 118140960795 + 1451681 * 2 ^ 59
def prefixEnd_1451681 : Nat := 4983230072969 + 3 ^ 40 * 1451681 * 2
def baseEnd_1451681 : Nat := 745410109999640025111347

theorem tailTrace_1451681 : CollatzResearch.WordTrace tailWord_1451681 prefixEnd_1451681 745410109999640025111347 := by
  unfold tailWord_1451681
  simp only [CollatzResearch.WordTrace]
  refine ⟨52947155853815139221402897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35298103902543426147601931 52947155853815139221402897)
  ·
    refine ⟨39710366890361354416052173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52947155853815139221402897 39710366890361354416052173)
    ·
      refine ⟨14891387583885507906019565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39710366890361354416052173 14891387583885507906019565)
      ·
        refine ⟨5584270343957065464757337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14891387583885507906019565 5584270343957065464757337)
        ·
          refine ⟨4188202757967799098568003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5584270343957065464757337 4188202757967799098568003)
          ·
            refine ⟨6282304136951698647852005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188202757967799098568003 6282304136951698647852005)
            ·
              refine ⟨1177932025678443496472251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6282304136951698647852005 1177932025678443496472251)
              ·
                refine ⟨1766898038517665244708377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177932025678443496472251 1766898038517665244708377)
                ·
                  refine ⟨1325173528888248933531283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766898038517665244708377 1325173528888248933531283)
                  ·
                    refine ⟨1987760293332373400296925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325173528888248933531283 1987760293332373400296925)
                    ·
                      refine ⟨745410109999640025111347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987760293332373400296925 745410109999640025111347)
                      ·
                        rfl

theorem cell23_1451681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1451681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451681 prefixEnd_1451681 := by exact prefixLift 1451681
  have htrace : WordTrace (prefixWord ++ tailWord_1451681) baseStart_1451681 baseEnd_1451681 := by
    simpa [prefixWord, tailWord_1451681, baseEnd_1451681] using wordTrace_append hprefix tailTrace_1451681
  have hstable : (prefixWord ++ tailWord_1451681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451681).length < 2 ^ (prefixWord ++ tailWord_1451681).sum := by decide
  have hdescent : baseEnd_1451681 < baseStart_1451681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451737 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1451737 : Nat := 118140960795 + 1451737 * 2 ^ 59
def prefixEnd_1451737 : Nat := 4983230072969 + 3 ^ 40 * 1451737 * 2
def baseEnd_1451737 : Nat := 745438864916291806011089

theorem tailTrace_1451737 : CollatzResearch.WordTrace tailWord_1451737 prefixEnd_1451737 745438864916291806011089 := by
  unfold tailWord_1451737
  simp only [CollatzResearch.WordTrace]
  refine ⟨52949198341612260785441465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35299465561074840523627643 52949198341612260785441465)
  ·
    refine ⟨39711898756209195589081099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52949198341612260785441465 39711898756209195589081099)
    ·
      refine ⟨59567848134313793383621649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39711898756209195589081099 59567848134313793383621649)
      ·
        refine ⟨44675886100735345037716237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59567848134313793383621649 44675886100735345037716237)
        ·
          refine ⟨16753457287775754389143589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44675886100735345037716237 16753457287775754389143589)
          ·
            refine ⟨3141273241457953947964423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16753457287775754389143589 3141273241457953947964423)
            ·
              refine ⟨4711909862186930921946635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141273241457953947964423 4711909862186930921946635)
              ·
                refine ⟨7067864793280396382919953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711909862186930921946635 7067864793280396382919953)
                ·
                  refine ⟨5300898594960297287189965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067864793280396382919953 5300898594960297287189965)
                  ·
                    refine ⟨1987836973110111482696237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5300898594960297287189965 1987836973110111482696237)
                    ·
                      refine ⟨745438864916291806011089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987836973110111482696237 745438864916291806011089)
                      ·
                        rfl

theorem cell23_1451737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1451737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451737 prefixEnd_1451737 := by exact prefixLift 1451737
  have htrace : WordTrace (prefixWord ++ tailWord_1451737) baseStart_1451737 baseEnd_1451737 := by
    simpa [prefixWord, tailWord_1451737, baseEnd_1451737] using wordTrace_append hprefix tailTrace_1451737
  have hstable : (prefixWord ++ tailWord_1451737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451737).length < 2 ^ (prefixWord ++ tailWord_1451737).sum := by decide
  have hdescent : baseEnd_1451737 < baseStart_1451737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451757 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1451757 : Nat := 118140960795 + 1451757 * 2 ^ 59
def prefixEnd_1451757 : Nat := 4983230072969 + 3 ^ 40 * 1451757 * 2
def baseEnd_1451757 : Nat := 248483044843127242586999

theorem tailTrace_1451757 : CollatzResearch.WordTrace tailWord_1451757 prefixEnd_1451757 248483044843127242586999 := by
  unfold tailWord_1451757
  simp only [CollatzResearch.WordTrace]
  refine ⟨52949927801539804201169525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35299951867693202800779683 52949927801539804201169525)
  ·
    refine ⟨4964055731394356643859643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52949927801539804201169525 4964055731394356643859643)
    ·
      refine ⟨7446083597091534965789465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964055731394356643859643 7446083597091534965789465)
      ·
        refine ⟨5584562697818651224342099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7446083597091534965789465 5584562697818651224342099)
        ·
          refine ⟨8376844046727976836513149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584562697818651224342099 8376844046727976836513149)
          ·
            refine ⟨3141316517522991313692431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8376844046727976836513149 3141316517522991313692431)
            ·
              refine ⟨4711974776284486970538647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141316517522991313692431 4711974776284486970538647)
              ·
                refine ⟨7067962164426730455807971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711974776284486970538647 7067962164426730455807971)
                ·
                  refine ⟨10601943246640095683711957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067962164426730455807971 10601943246640095683711957)
                  ·
                    refine ⟨248483044843127242586999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10601943246640095683711957 248483044843127242586999)
                    ·
                      rfl

theorem cell23_1451757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1451757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451757 prefixEnd_1451757 := by exact prefixLift 1451757
  have htrace : WordTrace (prefixWord ++ tailWord_1451757) baseStart_1451757 baseEnd_1451757 := by
    simpa [prefixWord, tailWord_1451757, baseEnd_1451757] using wordTrace_append hprefix tailTrace_1451757
  have hstable : (prefixWord ++ tailWord_1451757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451757).length < 2 ^ (prefixWord ++ tailWord_1451757).sum := by decide
  have hdescent : baseEnd_1451757 < baseStart_1451757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451777 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1451777 : Nat := 118140960795 + 1451777 * 2 ^ 59
def prefixEnd_1451777 : Nat := 4983230072969 + 3 ^ 40 * 1451777 * 2
def baseEnd_1451777 : Nat := 745459404142471649510905

theorem tailTrace_1451777 : CollatzResearch.WordTrace tailWord_1451777 prefixEnd_1451777 745459404142471649510905 := by
  unfold tailWord_1451777
  simp only [CollatzResearch.WordTrace]
  refine ⟨52950657261467347616897585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35300438174311565077931723 52950657261467347616897585)
  ·
    refine ⟨39712992946100510712673189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52950657261467347616897585 39712992946100510712673189)
    ·
      refine ⟨7446186177393845758626223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39712992946100510712673189 7446186177393845758626223)
      ·
        refine ⟨11169279266090768637939335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446186177393845758626223 11169279266090768637939335)
        ·
          refine ⟨16753918899136152956909003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169279266090768637939335 16753918899136152956909003)
          ·
            refine ⟨25130878348704229435363505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16753918899136152956909003 25130878348704229435363505)
            ·
              refine ⟨18848158761528172076522629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25130878348704229435363505 18848158761528172076522629)
              ·
                refine ⟨3534029767786532264347993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18848158761528172076522629 3534029767786532264347993)
                ·
                  refine ⟨2650522325839899198260995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3534029767786532264347993 2650522325839899198260995)
                  ·
                    refine ⟨3975783488759848797391493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650522325839899198260995 3975783488759848797391493)
                    ·
                      refine ⟨745459404142471649510905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3975783488759848797391493 745459404142471649510905)
                      ·
                        rfl

theorem cell23_1451777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1451777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451777 prefixEnd_1451777 := by exact prefixLift 1451777
  have htrace : WordTrace (prefixWord ++ tailWord_1451777) baseStart_1451777 baseEnd_1451777 := by
    simpa [prefixWord, tailWord_1451777, baseEnd_1451777] using wordTrace_append hprefix tailTrace_1451777
  have hstable : (prefixWord ++ tailWord_1451777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451777).length < 2 ^ (prefixWord ++ tailWord_1451777).sum := by decide
  have hdescent : baseEnd_1451777 < baseStart_1451777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451787 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 3, 4]
def baseStart_1451787 : Nat := 118140960795 + 1451787 * 2 ^ 59
def prefixEnd_1451787 : Nat := 4983230072969 + 3 ^ 40 * 1451787 * 2
def baseEnd_1451787 : Nat := 248488179649672203461953

theorem tailTrace_1451787 : CollatzResearch.WordTrace tailWord_1451787 prefixEnd_1451787 248488179649672203461953 := by
  unfold tailWord_1451787
  simp only [CollatzResearch.WordTrace]
  refine ⟨52951021991431119324761615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35300681327620746216507743 52951021991431119324761615)
  ·
    refine ⟨79426532987146678987142423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52951021991431119324761615 79426532987146678987142423)
    ·
      refine ⟨119139799480720018480713635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79426532987146678987142423 119139799480720018480713635)
      ·
        refine ⟨178709699221080027721070453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119139799480720018480713635 178709699221080027721070453)
        ·
          refine ⟨16754034301976252598850355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178709699221080027721070453 16754034301976252598850355)
          ·
            refine ⟨25131051452964378898275533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16754034301976252598850355 25131051452964378898275533)
            ·
              refine ⟨9424144294861642086853325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25131051452964378898275533 9424144294861642086853325)
              ·
                refine ⟨3534054110573115782569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9424144294861642086853325 3534054110573115782569997)
                ·
                  refine ⟨1325270291464918418463749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3534054110573115782569997 1325270291464918418463749)
                  ·
                    refine ⟨248488179649672203461953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325270291464918418463749 248488179649672203461953)
                    ·
                      rfl

theorem cell23_1451787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 4].length) (baseStart_1451787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451787 prefixEnd_1451787 := by exact prefixLift 1451787
  have htrace : WordTrace (prefixWord ++ tailWord_1451787) baseStart_1451787 baseEnd_1451787 := by
    simpa [prefixWord, tailWord_1451787, baseEnd_1451787] using wordTrace_append hprefix tailTrace_1451787
  have hstable : (prefixWord ++ tailWord_1451787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451787).length < 2 ^ (prefixWord ++ tailWord_1451787).sum := by decide
  have hdescent : baseEnd_1451787 < baseStart_1451787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451789 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1451789 : Nat := 118140960795 + 1451789 * 2 ^ 59
def prefixEnd_1451789 : Nat := 4983230072969 + 3 ^ 40 * 1451789 * 2
def baseEnd_1451789 : Nat := 745465565910325602560851

theorem tailTrace_1451789 : CollatzResearch.WordTrace tailWord_1451789 prefixEnd_1451789 745465565910325602560851 := by
  unfold tailWord_1451789
  simp only [CollatzResearch.WordTrace]
  refine ⟨52951094937423873666334421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35300729958282582444222947 52951094937423873666334421)
  ·
    refine ⟨1241041287595872039054713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 52951094937423873666334421 1241041287595872039054713)
    ·
      refine ⟨930780965696904029291035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1241041287595872039054713 930780965696904029291035)
      ·
        refine ⟨1396171448545356043936553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930780965696904029291035 1396171448545356043936553)
        ·
          refine ⟨1047128586409017032952415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396171448545356043936553 1047128586409017032952415)
          ·
            refine ⟨1570692879613525549428623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047128586409017032952415 1570692879613525549428623)
            ·
              refine ⟨2356039319420288324142935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570692879613525549428623 2356039319420288324142935)
              ·
                refine ⟨3534058979130432486214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356039319420288324142935 3534058979130432486214403)
                ·
                  refine ⟨5301088468695648729321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534058979130432486214403 5301088468695648729321605)
                  ·
                    refine ⟨993954087880434136747801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301088468695648729321605 993954087880434136747801)
                    ·
                      refine ⟨745465565910325602560851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 993954087880434136747801 745465565910325602560851)
                      ·
                        rfl

theorem cell23_1451789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1451789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451789 prefixEnd_1451789 := by exact prefixLift 1451789
  have htrace : WordTrace (prefixWord ++ tailWord_1451789) baseStart_1451789 baseEnd_1451789 := by
    simpa [prefixWord, tailWord_1451789, baseEnd_1451789] using wordTrace_append hprefix tailTrace_1451789
  have hstable : (prefixWord ++ tailWord_1451789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451789).length < 2 ^ (prefixWord ++ tailWord_1451789).sum := by decide
  have hdescent : baseEnd_1451789 < baseStart_1451789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451794 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1451794 : Nat := 118140960795 + 1451794 * 2 ^ 59
def prefixEnd_1451794 : Nat := 4983230072969 + 3 ^ 40 * 1451794 * 2
def baseEnd_1451794 : Nat := 745468133313598082998327

theorem tailTrace_1451794 : CollatzResearch.WordTrace tailWord_1451794 prefixEnd_1451794 745468133313598082998327 := by
  unfold tailWord_1451794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237819325601439880066609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35300851534937173013510957 13237819325601439880066609)
  ·
    refine ⟨9928364494201079910049957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13237819325601439880066609 9928364494201079910049957)
    ·
      refine ⟨1861568342662702483134367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9928364494201079910049957 1861568342662702483134367)
      ·
        refine ⟨2792352513994053724701551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861568342662702483134367 2792352513994053724701551)
        ·
          refine ⟨4188528770991080587052327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792352513994053724701551 4188528770991080587052327)
          ·
            refine ⟨6282793156486620880578491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188528770991080587052327 6282793156486620880578491)
            ·
              refine ⟨9424189734729931320867737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282793156486620880578491 9424189734729931320867737)
              ·
                refine ⟨7068142301047448490650803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424189734729931320867737 7068142301047448490650803)
                ·
                  refine ⟨10602213451571172735976205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068142301047448490650803 10602213451571172735976205)
                  ·
                    refine ⟨3975830044339189775991077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10602213451571172735976205 3975830044339189775991077)
                    ·
                      refine ⟨745468133313598082998327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3975830044339189775991077 745468133313598082998327)
                      ·
                        rfl

theorem cell23_1451794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1451794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451794 prefixEnd_1451794 := by exact prefixLift 1451794
  have htrace : WordTrace (prefixWord ++ tailWord_1451794) baseStart_1451794 baseEnd_1451794 := by
    simpa [prefixWord, tailWord_1451794, baseEnd_1451794] using wordTrace_append hprefix tailTrace_1451794
  have hstable : (prefixWord ++ tailWord_1451794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451794).length < 2 ^ (prefixWord ++ tailWord_1451794).sum := by decide
  have hdescent : baseEnd_1451794 < baseStart_1451794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451797 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_1451797 : Nat := 118140960795 + 1451797 * 2 ^ 59
def prefixEnd_1451797 : Nat := 4983230072969 + 3 ^ 40 * 1451797 * 2
def baseEnd_1451797 : Nat := 745469673755561571260813

theorem tailTrace_1451797 : CollatzResearch.WordTrace tailWord_1451797 prefixEnd_1451797 745469673755561571260813 := by
  unfold tailWord_1451797
  simp only [CollatzResearch.WordTrace]
  refine ⟨52951386721394891032625645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35300924480929927355083763 52951386721394891032625645)
  ·
    refine ⟨19856770020523084137234617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52951386721394891032625645 19856770020523084137234617)
    ·
      refine ⟨14892577515392313102925963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19856770020523084137234617 14892577515392313102925963)
      ·
        refine ⟨22338866273088469654388945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892577515392313102925963 22338866273088469654388945)
        ·
          refine ⟨16754149704816352240791709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22338866273088469654388945 16754149704816352240791709)
          ·
            refine ⟨6282806139306132090296891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16754149704816352240791709 6282806139306132090296891)
            ·
              refine ⟨9424209208959198135445337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282806139306132090296891 9424209208959198135445337)
              ·
                refine ⟨7068156906719398601584003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424209208959198135445337 7068156906719398601584003)
                ·
                  refine ⟨10602235360079097902376005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068156906719398601584003 10602235360079097902376005)
                  ·
                    refine ⟨1987919130014830856695501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10602235360079097902376005 1987919130014830856695501)
                    ·
                      refine ⟨745469673755561571260813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1987919130014830856695501 745469673755561571260813)
                      ·
                        rfl

theorem cell23_1451797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_1451797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451797 prefixEnd_1451797 := by exact prefixLift 1451797
  have htrace : WordTrace (prefixWord ++ tailWord_1451797) baseStart_1451797 baseEnd_1451797 := by
    simpa [prefixWord, tailWord_1451797, baseEnd_1451797] using wordTrace_append hprefix tailTrace_1451797
  have hstable : (prefixWord ++ tailWord_1451797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451797).length < 2 ^ (prefixWord ++ tailWord_1451797).sum := by decide
  have hdescent : baseEnd_1451797 < baseStart_1451797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451840 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1451840 : Nat := 118140960795 + 1451840 * 2 ^ 59
def prefixEnd_1451840 : Nat := 4983230072969 + 3 ^ 40 * 1451840 * 2
def baseEnd_1451840 : Nat := 745491753423704903023115

theorem tailTrace_1451840 : CollatzResearch.WordTrace tailWord_1451840 prefixEnd_1451840 745491753423704903023115 := by
  unfold tailWord_1451840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476477530119554688220487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35301970040159406250960649 26476477530119554688220487)
  ·
    refine ⟨39714716295179332032330731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26476477530119554688220487 39714716295179332032330731)
    ·
      refine ⟨59572074442768998048496097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39714716295179332032330731 59572074442768998048496097)
      ·
        refine ⟨44679055832076748536372073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59572074442768998048496097 44679055832076748536372073)
        ·
          refine ⟨33509291874057561402279055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44679055832076748536372073 33509291874057561402279055)
          ·
            refine ⟨50263937811086342103418583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33509291874057561402279055 50263937811086342103418583)
            ·
              refine ⟨75395906716629513155127875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50263937811086342103418583 75395906716629513155127875)
              ·
                refine ⟨113093860074944269732691813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75395906716629513155127875 113093860074944269732691813)
                ·
                  refine ⟨21205098764052050574879715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113093860074944269732691813 21205098764052050574879715)
                  ·
                    refine ⟨31807648146078075862319573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21205098764052050574879715 31807648146078075862319573)
                    ·
                      refine ⟨745491753423704903023115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31807648146078075862319573 745491753423704903023115)
                      ·
                        rfl

theorem cell23_1451840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1451840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451840 prefixEnd_1451840 := by exact prefixLift 1451840
  have htrace : WordTrace (prefixWord ++ tailWord_1451840) baseStart_1451840 baseEnd_1451840 := by
    simpa [prefixWord, tailWord_1451840, baseEnd_1451840] using wordTrace_append hprefix tailTrace_1451840
  have hstable : (prefixWord ++ tailWord_1451840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451840).length < 2 ^ (prefixWord ++ tailWord_1451840).sum := by decide
  have hdescent : baseEnd_1451840 < baseStart_1451840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451871 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 2, 3, 2]
def baseStart_1451871 : Nat := 118140960795 + 1451871 * 2 ^ 59
def prefixEnd_1451871 : Nat := 4983230072969 + 3 ^ 40 * 1451871 * 2
def baseEnd_1451871 : Nat := 745507671323994281735473

theorem tailTrace_1451871 : CollatzResearch.WordTrace tailWord_1451871 prefixEnd_1451871 745507671323994281735473 := by
  unfold tailWord_1451871
  simp only [CollatzResearch.WordTrace]
  refine ⟨52954085723126801670819467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35302723815417867780546311 52954085723126801670819467)
  ·
    refine ⟨79431128584690202506229201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52954085723126801670819467 79431128584690202506229201)
    ·
      refine ⟨59573346438517651879671901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79431128584690202506229201 59573346438517651879671901)
      ·
        refine ⟨22340004914444119454876963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59573346438517651879671901 22340004914444119454876963)
        ·
          refine ⟨33510007371666179182315445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22340004914444119454876963 33510007371666179182315445)
          ·
            refine ⟨3141563191093704298342073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33510007371666179182315445 3141563191093704298342073)
            ·
              refine ⟨2356172393320278223756555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141563191093704298342073 2356172393320278223756555)
              ·
                refine ⟨3534258589980417335634833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356172393320278223756555 3534258589980417335634833)
                ·
                  refine ⟨2650693942485313001726125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3534258589980417335634833 2650693942485313001726125)
                  ·
                    refine ⟨994010228431992375647297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2650693942485313001726125 994010228431992375647297)
                    ·
                      refine ⟨745507671323994281735473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994010228431992375647297 745507671323994281735473)
                      ·
                        rfl

theorem cell23_1451871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_1451871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451871 prefixEnd_1451871 := by exact prefixLift 1451871
  have htrace : WordTrace (prefixWord ++ tailWord_1451871) baseStart_1451871 baseEnd_1451871 := by
    simpa [prefixWord, tailWord_1451871, baseEnd_1451871] using wordTrace_append hprefix tailTrace_1451871
  have hstable : (prefixWord ++ tailWord_1451871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451871).length < 2 ^ (prefixWord ++ tailWord_1451871).sum := by decide
  have hdescent : baseEnd_1451871 < baseStart_1451871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451897 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1451897 : Nat := 118140960795 + 1451897 * 2 ^ 59
def prefixEnd_1451897 : Nat := 4983230072969 + 3 ^ 40 * 1451897 * 2
def baseEnd_1451897 : Nat := 745521021821011180010353

theorem tailTrace_1451897 : CollatzResearch.WordTrace tailWord_1451897 prefixEnd_1451897 745521021821011180010353 := by
  unfold tailWord_1451897
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955034021032608111265945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35303356014021738740843963 52955034021032608111265945)
  ·
    refine ⟨39716275515774456083449459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52955034021032608111265945 39716275515774456083449459)
    ·
      refine ⟨59574413273661684125174189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39716275515774456083449459 59574413273661684125174189)
      ·
        refine ⟨22340404977623131546940321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59574413273661684125174189 22340404977623131546940321)
        ·
          refine ⟨16755303733217348660205241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22340404977623131546940321 16755303733217348660205241)
          ·
            refine ⟨12566477799913011495153931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16755303733217348660205241 12566477799913011495153931)
            ·
              refine ⟨18849716699869517242730897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12566477799913011495153931 18849716699869517242730897)
              ·
                refine ⟨14137287524902137932048173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18849716699869517242730897 14137287524902137932048173)
                ·
                  refine ⟨5301482821838301724518065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14137287524902137932048173 5301482821838301724518065)
                  ·
                    refine ⟨3976112116378726293388549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301482821838301724518065 3976112116378726293388549)
                    ·
                      refine ⟨745521021821011180010353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3976112116378726293388549 745521021821011180010353)
                      ·
                        rfl

theorem cell23_1451897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1451897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451897 prefixEnd_1451897 := by exact prefixLift 1451897
  have htrace : WordTrace (prefixWord ++ tailWord_1451897) baseStart_1451897 baseEnd_1451897 := by
    simpa [prefixWord, tailWord_1451897, baseEnd_1451897] using wordTrace_append hprefix tailTrace_1451897
  have hstable : (prefixWord ++ tailWord_1451897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451897).length < 2 ^ (prefixWord ++ tailWord_1451897).sum := by decide
  have hdescent : baseEnd_1451897 < baseStart_1451897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451901 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_1451901 : Nat := 118140960795 + 1451901 * 2 ^ 59
def prefixEnd_1451901 : Nat := 4983230072969 + 3 ^ 40 * 1451901 * 2
def baseEnd_1451901 : Nat := 745523075743629164360335

theorem tailTrace_1451901 : CollatzResearch.WordTrace tailWord_1451901 prefixEnd_1451901 745523075743629164360335 := by
  unfold tailWord_1451901
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955179913018116794411557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35303453275345411196274371 52955179913018116794411557)
  ·
    refine ⟨9929096233690896898952167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52955179913018116794411557 9929096233690896898952167)
    ·
      refine ⟨14893644350536345348428251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9929096233690896898952167 14893644350536345348428251)
      ·
        refine ⟨22340466525804518022642377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14893644350536345348428251 22340466525804518022642377)
        ·
          refine ⟨16755349894353388516981783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22340466525804518022642377 16755349894353388516981783)
          ·
            refine ⟨25133024841530082775472675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755349894353388516981783 25133024841530082775472675)
            ·
              refine ⟨37699537262295124163209013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25133024841530082775472675 37699537262295124163209013)
              ·
                refine ⟨3534331618340167890300845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37699537262295124163209013 3534331618340167890300845)
                ·
                  refine ⟨1325374356877562958862817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3534331618340167890300845 1325374356877562958862817)
                  ·
                    refine ⟨994030767658172219147113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1325374356877562958862817 994030767658172219147113)
                    ·
                      refine ⟨745523075743629164360335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994030767658172219147113 745523075743629164360335)
                      ·
                        rfl

theorem cell23_1451901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_1451901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451901 prefixEnd_1451901 := by exact prefixLift 1451901
  have htrace : WordTrace (prefixWord ++ tailWord_1451901) baseStart_1451901 baseEnd_1451901 := by
    simpa [prefixWord, tailWord_1451901, baseEnd_1451901] using wordTrace_append hprefix tailTrace_1451901
  have hstable : (prefixWord ++ tailWord_1451901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451901).length < 2 ^ (prefixWord ++ tailWord_1451901).sum := by decide
  have hdescent : baseEnd_1451901 < baseStart_1451901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451907 : List Nat := [1, 1, 1, 3, 4, 2, 3, 8]
def baseStart_1451907 : Nat := 118140960795 + 1451907 * 2 ^ 59
def prefixEnd_1451907 : Nat := 4983230072969 + 3 ^ 40 * 1451907 * 2
def baseEnd_1451907 : Nat := 27612079875094671884641

theorem tailTrace_1451907 : CollatzResearch.WordTrace tailWord_1451907 prefixEnd_1451907 27612079875094671884641 := by
  unfold tailWord_1451907
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955398750996379819129975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35303599167330919879419983 52955398750996379819129975)
  ·
    refine ⟨79433098126494569728694963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52955398750996379819129975 79433098126494569728694963)
    ·
      refine ⟨119149647189741854593042445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79433098126494569728694963 119149647189741854593042445)
      ·
        refine ⟨44681117696153195472390917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119149647189741854593042445 44681117696153195472390917)
        ·
          refine ⟨8377709568028724151073297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44681117696153195472390917 8377709568028724151073297)
          ·
            refine ⟨6283282176021543113304973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8377709568028724151073297 6283282176021543113304973)
            ·
              refine ⟨2356230816008078667489365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6283282176021543113304973 2356230816008078667489365)
              ·
                refine ⟨27612079875094671884641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2356230816008078667489365 27612079875094671884641)
                ·
                  rfl

theorem cell23_1451907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 8].length) (baseStart_1451907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451907 prefixEnd_1451907 := by exact prefixLift 1451907
  have htrace : WordTrace (prefixWord ++ tailWord_1451907) baseStart_1451907 baseEnd_1451907 := by
    simpa [prefixWord, tailWord_1451907, baseEnd_1451907] using wordTrace_append hprefix tailTrace_1451907
  have hstable : (prefixWord ++ tailWord_1451907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451907).length < 2 ^ (prefixWord ++ tailWord_1451907).sum := by decide
  have hdescent : baseEnd_1451907 < baseStart_1451907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451935 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1451935 : Nat := 118140960795 + 1451935 * 2 ^ 59
def prefixEnd_1451935 : Nat := 4983230072969 + 3 ^ 40 * 1451935 * 2
def baseEnd_1451935 : Nat := 745540534085882031335179

theorem tailTrace_1451935 : CollatzResearch.WordTrace tailWord_1451935 prefixEnd_1451935 745540534085882031335179 := by
  unfold tailWord_1451935
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956419994894940601149259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35304279996596627067432839 52956419994894940601149259)
  ·
    refine ⟨79434629992342410901723889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52956419994894940601149259 79434629992342410901723889)
    ·
      refine ⟨59575972494256808176292917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79434629992342410901723889 59575972494256808176292917)
      ·
        refine ⟨5585247421336575766527461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59575972494256808176292917 5585247421336575766527461)
        ·
          refine ⟨1047233891500607956223899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5585247421336575766527461 1047233891500607956223899)
          ·
            refine ⟨1570850837250911934335849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047233891500607956223899 1570850837250911934335849)
            ·
              refine ⟨1178138127938183950751887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570850837250911934335849 1178138127938183950751887)
              ·
                refine ⟨1767207191907275926127831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178138127938183950751887 1767207191907275926127831)
                ·
                  refine ⟨2650810787860913889191747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767207191907275926127831 2650810787860913889191747)
                  ·
                    refine ⟨3976216181791370833787621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2650810787860913889191747 3976216181791370833787621)
                    ·
                      refine ⟨745540534085882031335179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3976216181791370833787621 745540534085882031335179)
                      ·
                        rfl

theorem cell23_1451935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1451935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451935 prefixEnd_1451935 := by exact prefixLift 1451935
  have htrace : WordTrace (prefixWord ++ tailWord_1451935) baseStart_1451935 baseEnd_1451935 := by
    simpa [prefixWord, tailWord_1451935, baseEnd_1451935] using wordTrace_append hprefix tailTrace_1451935
  have hstable : (prefixWord ++ tailWord_1451935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451935).length < 2 ^ (prefixWord ++ tailWord_1451935).sum := by decide
  have hdescent : baseEnd_1451935 < baseStart_1451935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451938 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1451938 : Nat := 118140960795 + 1451938 * 2 ^ 59
def prefixEnd_1451938 : Nat := 4983230072969 + 3 ^ 40 * 1451938 * 2
def baseEnd_1451938 : Nat := 745542074527845519597665

theorem tailTrace_1451938 : CollatzResearch.WordTrace tailWord_1451938 prefixEnd_1451938 745542074527845519597665 := by
  unfold tailWord_1451938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239132353471018028377117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35304352942589381409005645 13239132353471018028377117)
  ·
    refine ⟨4964674632551631760641419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13239132353471018028377117 4964674632551631760641419)
    ·
      refine ⟨7447011948827447640962129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964674632551631760641419 7447011948827447640962129)
      ·
        refine ⟨5585258961620585730721597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447011948827447640962129 5585258961620585730721597)
        ·
          refine ⟨2094472110607719649020599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5585258961620585730721597 2094472110607719649020599)
          ·
            refine ⟨3141708165911579473530899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094472110607719649020599 3141708165911579473530899)
            ·
              refine ⟨4712562248867369210296349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141708165911579473530899 4712562248867369210296349)
              ·
                refine ⟨1767210843325263453861131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4712562248867369210296349 1767210843325263453861131)
                ·
                  refine ⟨2650816264987895180791697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767210843325263453861131 2650816264987895180791697)
                  ·
                    refine ⟨1988112198740921385593773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2650816264987895180791697 1988112198740921385593773)
                    ·
                      refine ⟨745542074527845519597665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988112198740921385593773 745542074527845519597665)
                      ·
                        rfl

theorem cell23_1451938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1451938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451938 prefixEnd_1451938 := by exact prefixLift 1451938
  have htrace : WordTrace (prefixWord ++ tailWord_1451938) baseStart_1451938 baseEnd_1451938 := by
    simpa [prefixWord, tailWord_1451938, baseEnd_1451938] using wordTrace_append hprefix tailTrace_1451938
  have hstable : (prefixWord ++ tailWord_1451938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451938).length < 2 ^ (prefixWord ++ tailWord_1451938).sum := by decide
  have hdescent : baseEnd_1451938 < baseStart_1451938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451967 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 6]
def baseStart_1451967 : Nat := 118140960795 + 1451967 * 2 ^ 59
def prefixEnd_1451967 : Nat := 4983230072969 + 3 ^ 40 * 1451967 * 2
def baseEnd_1451967 : Nat := 248518988488941968711677

theorem tailTrace_1451967 : CollatzResearch.WordTrace tailWord_1451967 prefixEnd_1451967 248518988488941968711677 := by
  unfold tailWord_1451967
  simp only [CollatzResearch.WordTrace]
  refine ⟨52957587130779010066314155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35305058087186006710876103 52957587130779010066314155)
  ·
    refine ⟨79436380696168515099471233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52957587130779010066314155 79436380696168515099471233)
    ·
      refine ⟨59577285522126386324603425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79436380696168515099471233 59577285522126386324603425)
      ·
        refine ⟨44682964141594789743452569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59577285522126386324603425 44682964141594789743452569)
        ·
          refine ⟨33512223106196092307589427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44682964141594789743452569 33512223106196092307589427)
          ·
            refine ⟨50268334659294138461384141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33512223106196092307589427 50268334659294138461384141)
            ·
              refine ⟨18850625497235301923019053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50268334659294138461384141 18850625497235301923019053)
              ·
                refine ⟨7068984561463238221132145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18850625497235301923019053 7068984561463238221132145)
                ·
                  refine ⟨5301738421097428665849109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068984561463238221132145 5301738421097428665849109)
                  ·
                    refine ⟨248518988488941968711677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5301738421097428665849109 248518988488941968711677)
                    ·
                      rfl

theorem cell23_1451967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_1451967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451967 prefixEnd_1451967 := by exact prefixLift 1451967
  have htrace : WordTrace (prefixWord ++ tailWord_1451967) baseStart_1451967 baseEnd_1451967 := by
    simpa [prefixWord, tailWord_1451967, baseEnd_1451967] using wordTrace_append hprefix tailTrace_1451967
  have hstable : (prefixWord ++ tailWord_1451967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451967).length < 2 ^ (prefixWord ++ tailWord_1451967).sum := by decide
  have hdescent : baseEnd_1451967 < baseStart_1451967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451968 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3]
def baseStart_1451968 : Nat := 118140960795 + 1451968 * 2 ^ 59
def prefixEnd_1451968 : Nat := 4983230072969 + 3 ^ 40 * 1451968 * 2
def baseEnd_1451968 : Nat := 745557478947480402222527

theorem tailTrace_1451968 : CollatzResearch.WordTrace tailWord_1451968 prefixEnd_1451968 745557478947480402222527 := by
  unfold tailWord_1451968
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478811801887693618550279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35305082402516924824733705 26478811801887693618550279)
  ·
    refine ⟨39718217702831540427825419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478811801887693618550279 39718217702831540427825419)
    ·
      refine ⟨59577326554247310641738129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39718217702831540427825419 59577326554247310641738129)
      ·
        refine ⟨44682994915685482981303597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59577326554247310641738129 44682994915685482981303597)
        ·
          refine ⟨16756123093382056117988849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44682994915685482981303597 16756123093382056117988849)
          ·
            refine ⟨12567092320036542088491637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16756123093382056117988849 12567092320036542088491637)
            ·
              refine ⟨1178164905003425820796091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12567092320036542088491637 1178164905003425820796091)
              ·
                refine ⟨1767247357505138731194137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178164905003425820796091 1767247357505138731194137)
                ·
                  refine ⟨1325435518128854048395603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1767247357505138731194137 1325435518128854048395603)
                  ·
                    refine ⟨1988153277193281072593405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325435518128854048395603 1988153277193281072593405)
                    ·
                      refine ⟨745557478947480402222527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988153277193281072593405 745557478947480402222527)
                      ·
                        rfl

theorem cell23_1451968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_1451968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451968 prefixEnd_1451968 := by exact prefixLift 1451968
  have htrace : WordTrace (prefixWord ++ tailWord_1451968) baseStart_1451968 baseEnd_1451968 := by
    simpa [prefixWord, tailWord_1451968, baseEnd_1451968] using wordTrace_append hprefix tailTrace_1451968
  have hstable : (prefixWord ++ tailWord_1451968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451968).length < 2 ^ (prefixWord ++ tailWord_1451968).sum := by decide
  have hdescent : baseEnd_1451968 < baseStart_1451968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_1451977 : Nat := 118140960795 + 1451977 * 2 ^ 59
def prefixEnd_1451977 : Nat := 4983230072969 + 3 ^ 40 * 1451977 * 2
def baseEnd_1451977 : Nat := 745562100273370867009985

theorem tailTrace_1451977 : CollatzResearch.WordTrace tailWord_1451977 prefixEnd_1451977 745562100273370867009985 := by
  unfold tailWord_1451977
  simp only [CollatzResearch.WordTrace]
  refine ⟨52957951860742781774178185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35305301240495187849452123 52957951860742781774178185)
  ·
    refine ⟨39718463895557086330633639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52957951860742781774178185 39718463895557086330633639)
    ·
      refine ⟨59577695843335629495950459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39718463895557086330633639 59577695843335629495950459)
      ·
        refine ⟨89366543765003444243925689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59577695843335629495950459 89366543765003444243925689)
        ·
          refine ⟨67024907823752583182944267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89366543765003444243925689 67024907823752583182944267)
          ·
            refine ⟨100537361735628874774416401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67024907823752583182944267 100537361735628874774416401)
            ·
              refine ⟨75403021301721656080812301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100537361735628874774416401 75403021301721656080812301)
              ·
                refine ⟨28276132988145621030304613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75403021301721656080812301 28276132988145621030304613)
                ·
                  refine ⟨5301774935277303943182115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28276132988145621030304613 5301774935277303943182115)
                  ·
                    refine ⟨7952662402915955914773173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301774935277303943182115 7952662402915955914773173)
                    ·
                      refine ⟨745562100273370867009985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7952662402915955914773173 745562100273370867009985)
                      ·
                        rfl

theorem cell23_1451977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_1451977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451977 prefixEnd_1451977 := by exact prefixLift 1451977
  have htrace : WordTrace (prefixWord ++ tailWord_1451977) baseStart_1451977 baseEnd_1451977 := by
    simpa [prefixWord, tailWord_1451977, baseEnd_1451977] using wordTrace_append hprefix tailTrace_1451977
  have hstable : (prefixWord ++ tailWord_1451977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451977).length < 2 ^ (prefixWord ++ tailWord_1451977).sum := by decide
  have hdescent : baseEnd_1451977 < baseStart_1451977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451991 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_1451991 : Nat := 118140960795 + 1451991 * 2 ^ 59
def prefixEnd_1451991 : Nat := 4983230072969 + 3 ^ 40 * 1451991 * 2
def baseEnd_1451991 : Nat := 745569289002533812234921

theorem tailTrace_1451991 : CollatzResearch.WordTrace tailWord_1451991 prefixEnd_1451991 745569289002533812234921 := by
  unfold tailWord_1451991
  simp only [CollatzResearch.WordTrace]
  refine ⟨52958462482692062165187827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35305641655128041443458551 52958462482692062165187827)
  ·
    refine ⟨79437693724038093247781741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52958462482692062165187827 79437693724038093247781741)
    ·
      refine ⟨29789135146514284967918153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79437693724038093247781741 29789135146514284967918153)
      ·
        refine ⟨22341851359885713725938615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29789135146514284967918153 22341851359885713725938615)
        ·
          refine ⟨33512777039828570588907923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341851359885713725938615 33512777039828570588907923)
          ·
            refine ⟨50269165559742855883361885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33512777039828570588907923 50269165559742855883361885)
            ·
              refine ⟨18850937084903570956260707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50269165559742855883361885 18850937084903570956260707)
              ·
                refine ⟨28276405627355356434391061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18850937084903570956260707 28276405627355356434391061)
                ·
                  refine ⟨1325456513782282332862081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28276405627355356434391061 1325456513782282332862081)
                  ·
                    refine ⟨994092385336711749646561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1325456513782282332862081 994092385336711749646561)
                    ·
                      refine ⟨745569289002533812234921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994092385336711749646561 745569289002533812234921)
                      ·
                        rfl

theorem cell23_1451991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_1451991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1451991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1451991 prefixEnd_1451991 := by exact prefixLift 1451991
  have htrace : WordTrace (prefixWord ++ tailWord_1451991) baseStart_1451991 baseEnd_1451991 := by
    simpa [prefixWord, tailWord_1451991, baseEnd_1451991] using wordTrace_append hprefix tailTrace_1451991
  have hstable : (prefixWord ++ tailWord_1451991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451991).length < 2 ^ (prefixWord ++ tailWord_1451991).sum := by decide
  have hdescent : baseEnd_1451991 < baseStart_1451991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452008 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1452008 : Nat := 118140960795 + 1452008 * 2 ^ 59
def prefixEnd_1452008 : Nat := 4983230072969 + 3 ^ 40 * 1452008 * 2
def baseEnd_1452008 : Nat := 745578018173660245722343

theorem tailTrace_1452008 : CollatzResearch.WordTrace tailWord_1452008 prefixEnd_1452008 745578018173660245722343 := by
  unfold tailWord_1452008
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479541261815237034278339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35306055015753649379037785 26479541261815237034278339)
  ·
    refine ⟨39719311892722855551417509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26479541261815237034278339 39719311892722855551417509)
    ·
      refine ⟨7447370979885535415890783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39719311892722855551417509 7447370979885535415890783)
      ·
        refine ⟨11171056469828303123836175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447370979885535415890783 11171056469828303123836175)
        ·
          refine ⟨16756584704742454685754263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171056469828303123836175 16756584704742454685754263)
          ·
            refine ⟨25134877057113682028631395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16756584704742454685754263 25134877057113682028631395)
            ·
              refine ⟨37702315585670523042947093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25134877057113682028631395 37702315585670523042947093)
              ·
                refine ⟨1767296043078305767638145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37702315585670523042947093 1767296043078305767638145)
                ·
                  refine ⟨1325472032308729325728609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1767296043078305767638145 1325472032308729325728609)
                  ·
                    refine ⟨994104024231546994296457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1325472032308729325728609 994104024231546994296457)
                    ·
                      refine ⟨745578018173660245722343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994104024231546994296457 745578018173660245722343)
                      ·
                        rfl

theorem cell23_1452008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1452008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452008 prefixEnd_1452008 := by exact prefixLift 1452008
  have htrace : WordTrace (prefixWord ++ tailWord_1452008) baseStart_1452008 baseEnd_1452008 := by
    simpa [prefixWord, tailWord_1452008, baseEnd_1452008] using wordTrace_append hprefix tailTrace_1452008
  have hstable : (prefixWord ++ tailWord_1452008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452008).length < 2 ^ (prefixWord ++ tailWord_1452008).sum := by decide
  have hdescent : baseEnd_1452008 < baseStart_1452008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452024 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1452024 : Nat := 118140960795 + 1452024 * 2 ^ 59
def prefixEnd_1452024 : Nat := 4983230072969 + 3 ^ 40 * 1452024 * 2
def baseEnd_1452024 : Nat := 745586233864132183122269

theorem tailTrace_1452024 : CollatzResearch.WordTrace tailWord_1452024 prefixEnd_1452024 745586233864132183122269 := by
  unfold tailWord_1452024
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479833045786254400569563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35306444061048339200759417 26479833045786254400569563)
  ·
    refine ⟨39719749568679381600854345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26479833045786254400569563 39719749568679381600854345)
    ·
      refine ⟨29789812176509536200640759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39719749568679381600854345 29789812176509536200640759)
      ·
        refine ⟨44684718264764304300961139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789812176509536200640759 44684718264764304300961139)
        ·
          refine ⟨67027077397146456451441709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44684718264764304300961139 67027077397146456451441709)
          ·
            refine ⟨25135154023929921169290641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67027077397146456451441709 25135154023929921169290641)
            ·
              refine ⟨18851365517947440876967981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25135154023929921169290641 18851365517947440876967981)
              ·
                refine ⟨7069262069230290328862993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18851365517947440876967981 7069262069230290328862993)
                ·
                  refine ⟨5301946551922717746647245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7069262069230290328862993 5301946551922717746647245)
                  ·
                    refine ⟨1988229956971019154992717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5301946551922717746647245 1988229956971019154992717)
                    ·
                      refine ⟨745586233864132183122269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988229956971019154992717 745586233864132183122269)
                      ·
                        rfl

theorem cell23_1452024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1452024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452024 prefixEnd_1452024 := by exact prefixLift 1452024
  have htrace : WordTrace (prefixWord ++ tailWord_1452024) baseStart_1452024 baseEnd_1452024 := by
    simpa [prefixWord, tailWord_1452024, baseEnd_1452024] using wordTrace_append hprefix tailTrace_1452024
  have hstable : (prefixWord ++ tailWord_1452024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452024).length < 2 ^ (prefixWord ++ tailWord_1452024).sum := by decide
  have hdescent : baseEnd_1452024 < baseStart_1452024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452025 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 2, 2, 2]
def baseStart_1452025 : Nat := 118140960795 + 1452025 * 2 ^ 59
def prefixEnd_1452025 : Nat := 4983230072969 + 3 ^ 40 * 1452025 * 2
def baseEnd_1452025 : Nat := 745586747344786679209765

theorem tailTrace_1452025 : CollatzResearch.WordTrace tailWord_1452025 prefixEnd_1452025 745586747344786679209765 := by
  unfold tailWord_1452025
  simp only [CollatzResearch.WordTrace]
  refine ⟨52959702564568885971925529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35306468376379257314617019 52959702564568885971925529)
  ·
    refine ⟨39719776923426664478944147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52959702564568885971925529 39719776923426664478944147)
    ·
      refine ⟨59579665385139996718416221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39719776923426664478944147 59579665385139996718416221)
      ·
        refine ⟨22342374519427498769406083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59579665385139996718416221 22342374519427498769406083)
        ·
          refine ⟨33513561779141248154109125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22342374519427498769406083 33513561779141248154109125)
          ·
            refine ⟨6283792833588984028895461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33513561779141248154109125 6283792833588984028895461)
            ·
              refine ⟨1178211156297934505417899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6283792833588984028895461 1178211156297934505417899)
              ·
                refine ⟨1767316734446901758126849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178211156297934505417899 1767316734446901758126849)
                ·
                  refine ⟨1325487550835176318595137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1767316734446901758126849 1325487550835176318595137)
                  ·
                    refine ⟨994115663126382238946353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1325487550835176318595137 994115663126382238946353)
                    ·
                      refine ⟨745586747344786679209765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994115663126382238946353 745586747344786679209765)
                      ·
                        rfl

theorem cell23_1452025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_1452025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452025 prefixEnd_1452025 := by exact prefixLift 1452025
  have htrace : WordTrace (prefixWord ++ tailWord_1452025) baseStart_1452025 baseEnd_1452025 := by
    simpa [prefixWord, tailWord_1452025, baseEnd_1452025] using wordTrace_append hprefix tailTrace_1452025
  have hstable : (prefixWord ++ tailWord_1452025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452025).length < 2 ^ (prefixWord ++ tailWord_1452025).sum := by decide
  have hdescent : baseEnd_1452025 < baseStart_1452025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452027 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 7]
def baseStart_1452027 : Nat := 118140960795 + 1452027 * 2 ^ 59
def prefixEnd_1452027 : Nat := 4983230072969 + 3 ^ 40 * 1452027 * 2
def baseEnd_1452027 : Nat := 248529258102031890461585

theorem tailTrace_1452027 : CollatzResearch.WordTrace tailWord_1452027 prefixEnd_1452027 248529258102031890461585 := by
  unfold tailWord_1452027
  simp only [CollatzResearch.WordTrace]
  refine ⟨52959775510561640313498335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35306517007041093542332223 52959775510561640313498335)
  ·
    refine ⟨79439663265842460470247503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52959775510561640313498335 79439663265842460470247503)
    ·
      refine ⟨119159494898763690705371255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79439663265842460470247503 119159494898763690705371255)
      ·
        refine ⟨178739242348145536058056883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119159494898763690705371255 178739242348145536058056883)
        ·
          refine ⟨268108863522218304087085325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178739242348145536058056883 268108863522218304087085325)
          ·
            refine ⟨100540823820831864032656997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268108863522218304087085325 100540823820831864032656997)
            ·
              refine ⟨18851404466405974506123187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100540823820831864032656997 18851404466405974506123187)
              ·
                refine ⟨28277106699608961759184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18851404466405974506123187 28277106699608961759184781)
                ·
                  refine ⟨10603915012353360659694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28277106699608961759184781 10603915012353360659694293)
                  ·
                    refine ⟨248529258102031890461585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10603915012353360659694293 248529258102031890461585)
                    ·
                      rfl

theorem cell23_1452027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 7].length) (baseStart_1452027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452027 prefixEnd_1452027 := by exact prefixLift 1452027
  have htrace : WordTrace (prefixWord ++ tailWord_1452027) baseStart_1452027 baseEnd_1452027 := by
    simpa [prefixWord, tailWord_1452027, baseEnd_1452027] using wordTrace_append hprefix tailTrace_1452027
  have hstable : (prefixWord ++ tailWord_1452027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452027).length < 2 ^ (prefixWord ++ tailWord_1452027).sum := by decide
  have hdescent : baseEnd_1452027 < baseStart_1452027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452061 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1452061 : Nat := 118140960795 + 1452061 * 2 ^ 59
def prefixEnd_1452061 : Nat := 4983230072969 + 3 ^ 40 * 1452061 * 2
def baseEnd_1452061 : Nat := 248535077549449512786533

theorem tailTrace_1452061 : CollatzResearch.WordTrace tailWord_1452061 prefixEnd_1452061 248535077549449512786533 := by
  unfold tailWord_1452061
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961015592438464120236037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35307343728292309413490691 52961015592438464120236037)
  ·
    refine ⟨9930190423582212022544257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52961015592438464120236037 9930190423582212022544257)
    ·
      refine ⟨7447642817686659016908193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930190423582212022544257 7447642817686659016908193)
      ·
        refine ⟨5585732113264994262681145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447642817686659016908193 5585732113264994262681145)
        ·
          refine ⟨4189299084948745697010859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5585732113264994262681145 4189299084948745697010859)
          ·
            refine ⟨6283948627423118545516289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189299084948745697010859 6283948627423118545516289)
            ·
              refine ⟨4712961470567338909137217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283948627423118545516289 4712961470567338909137217)
              ·
                refine ⟨3534721102925504181852913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712961470567338909137217 3534721102925504181852913)
                ·
                  refine ⟨2651040827194128136389685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3534721102925504181852913 2651040827194128136389685)
                  ·
                    refine ⟨248535077549449512786533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2651040827194128136389685 248535077549449512786533)
                    ·
                      rfl

theorem cell23_1452061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1452061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452061 prefixEnd_1452061 := by exact prefixLift 1452061
  have htrace : WordTrace (prefixWord ++ tailWord_1452061) baseStart_1452061 baseEnd_1452061 := by
    simpa [prefixWord, tailWord_1452061, baseEnd_1452061] using wordTrace_append hprefix tailTrace_1452061
  have hstable : (prefixWord ++ tailWord_1452061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452061).length < 2 ^ (prefixWord ++ tailWord_1452061).sum := by decide
  have hdescent : baseEnd_1452061 < baseStart_1452061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452065 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 5]
def baseStart_1452065 : Nat := 118140960795 + 1452065 * 2 ^ 59
def prefixEnd_1452065 : Nat := 4983230072969 + 3 ^ 40 * 1452065 * 2
def baseEnd_1452065 : Nat := 82845254063440724745509

theorem tailTrace_1452065 : CollatzResearch.WordTrace tailWord_1452065 prefixEnd_1452065 82845254063440724745509 := by
  unfold tailWord_1452065
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961161484423972803381649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35307440989615981868921099 52961161484423972803381649)
  ·
    refine ⟨39720871113317979602536237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52961161484423972803381649 39720871113317979602536237)
    ·
      refine ⟨14895326667494242350951089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39720871113317979602536237 14895326667494242350951089)
      ·
        refine ⟨11171495000620681763213317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14895326667494242350951089 11171495000620681763213317)
        ·
          refine ⟨2094655312616377830602497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11171495000620681763213317 2094655312616377830602497)
          ·
            refine ⟨1570991484462283372951873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094655312616377830602497 1570991484462283372951873)
            ·
              refine ⟨1178243613346712529713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570991484462283372951873 1178243613346712529713905)
              ·
                refine ⟨883682710010034397285429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178243613346712529713905 883682710010034397285429)
                ·
                  refine ⟨82845254063440724745509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883682710010034397285429 82845254063440724745509)
                  ·
                    rfl

theorem cell23_1452065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 5].length) (baseStart_1452065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452065 prefixEnd_1452065 := by exact prefixLift 1452065
  have htrace : WordTrace (prefixWord ++ tailWord_1452065) baseStart_1452065 baseEnd_1452065 := by
    simpa [prefixWord, tailWord_1452065, baseEnd_1452065] using wordTrace_append hprefix tailTrace_1452065
  have hstable : (prefixWord ++ tailWord_1452065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452065).length < 2 ^ (prefixWord ++ tailWord_1452065).sum := by decide
  have hdescent : baseEnd_1452065 < baseStart_1452065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452081 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_1452081 : Nat := 118140960795 + 1452081 * 2 ^ 59
def prefixEnd_1452081 : Nat := 4983230072969 + 3 ^ 40 * 1452081 * 2
def baseEnd_1452081 : Nat := 745615502261438460109507

theorem tailTrace_1452081 : CollatzResearch.WordTrace tailWord_1452081 prefixEnd_1452081 745615502261438460109507 := by
  unfold tailWord_1452081
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961745052366007535964097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35307830034910671690642731 52961745052366007535964097)
  ·
    refine ⟨39721308789274505651973073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52961745052366007535964097 39721308789274505651973073)
    ·
      refine ⟨29790981591955879238979805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39721308789274505651973073 29790981591955879238979805)
      ·
        refine ⟨11171618096983454714617427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29790981591955879238979805 11171618096983454714617427)
        ·
          refine ⟨16757427145475182071926141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171618096983454714617427 16757427145475182071926141)
          ·
            refine ⟨6284035179553193276972303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16757427145475182071926141 6284035179553193276972303)
            ·
              refine ⟨9426052769329789915458455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284035179553193276972303 9426052769329789915458455)
              ·
                refine ⟨14139079153994684873187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426052769329789915458455 14139079153994684873187683)
                ·
                  refine ⟨21208618730992027309781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14139079153994684873187683 21208618730992027309781525)
                  ·
                    refine ⟨994154003015251280146009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21208618730992027309781525 994154003015251280146009)
                    ·
                      refine ⟨745615502261438460109507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994154003015251280146009 745615502261438460109507)
                      ·
                        rfl

theorem cell23_1452081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_1452081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452081 prefixEnd_1452081 := by exact prefixLift 1452081
  have htrace : WordTrace (prefixWord ++ tailWord_1452081) baseStart_1452081 baseEnd_1452081 := by
    simpa [prefixWord, tailWord_1452081, baseEnd_1452081] using wordTrace_append hprefix tailTrace_1452081
  have hstable : (prefixWord ++ tailWord_1452081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452081).length < 2 ^ (prefixWord ++ tailWord_1452081).sum := by decide
  have hdescent : baseEnd_1452081 < baseStart_1452081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452108 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_1452108 : Nat := 118140960795 + 1452108 * 2 ^ 59
def prefixEnd_1452108 : Nat := 4983230072969 + 3 ^ 40 * 1452108 * 2
def baseEnd_1452108 : Nat := 248543122079703284823961

theorem tailTrace_1452108 : CollatzResearch.WordTrace tailWord_1452108 prefixEnd_1452108 248543122079703284823961 := by
  unfold tailWord_1452108
  simp only [CollatzResearch.WordTrace]
  refine ⟨26481364911634095573598489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35308486548845460764797985 26481364911634095573598489)
  ·
    refine ⟨19861023683725571680198867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26481364911634095573598489 19861023683725571680198867)
    ·
      refine ⟨29791535525588357520298301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861023683725571680198867 29791535525588357520298301)
      ·
        refine ⟨11171825822095634070111863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29791535525588357520298301 11171825822095634070111863)
        ·
          refine ⟨16757738733143451105167795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171825822095634070111863 16757738733143451105167795)
          ·
            refine ⟨25136608099715176657751693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16757738733143451105167795 25136608099715176657751693)
            ·
              refine ⟨9426228037393191246656885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25136608099715176657751693 9426228037393191246656885)
              ·
                refine ⟨883708878505611679374083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9426228037393191246656885 883708878505611679374083)
                ·
                  refine ⟨1325563317758417519061125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883708878505611679374083 1325563317758417519061125)
                  ·
                    refine ⟨248543122079703284823961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325563317758417519061125 248543122079703284823961)
                    ·
                      rfl

theorem cell23_1452108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_1452108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452108 prefixEnd_1452108 := by exact prefixLift 1452108
  have htrace : WordTrace (prefixWord ++ tailWord_1452108) baseStart_1452108 baseEnd_1452108 := by
    simpa [prefixWord, tailWord_1452108, baseEnd_1452108] using wordTrace_append hprefix tailTrace_1452108
  have hstable : (prefixWord ++ tailWord_1452108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452108).length < 2 ^ (prefixWord ++ tailWord_1452108).sum := by decide
  have hdescent : baseEnd_1452108 < baseStart_1452108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452125 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1452125 : Nat := 118140960795 + 1452125 * 2 ^ 59
def prefixEnd_1452125 : Nat := 4983230072969 + 3 ^ 40 * 1452125 * 2
def baseEnd_1452125 : Nat := 248546031803412095986435

theorem tailTrace_1452125 : CollatzResearch.WordTrace tailWord_1452125 prefixEnd_1452125 248546031803412095986435 := by
  unfold tailWord_1452125
  simp only [CollatzResearch.WordTrace]
  refine ⟨52963349864206603050565829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35308899909471068700377219 52963349864206603050565829)
  ·
    refine ⟨9930628099538738071981093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52963349864206603050565829 9930628099538738071981093)
    ·
      refine ⟨1861992768663513388496455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9930628099538738071981093 1861992768663513388496455)
      ·
        refine ⟨2792989152995270082744683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861992768663513388496455 2792989152995270082744683)
        ·
          refine ⟨4189483729492905124117025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2792989152995270082744683 4189483729492905124117025)
          ·
            refine ⟨3142112797119678843087769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4189483729492905124117025 3142112797119678843087769)
            ·
              refine ⟨2356584597839759132315827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142112797119678843087769 2356584597839759132315827)
              ·
                refine ⟨3534876896759638698473741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356584597839759132315827 3534876896759638698473741)
                ·
                  refine ⟨1325578836284864511927653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3534876896759638698473741 1325578836284864511927653)
                  ·
                    refine ⟨248546031803412095986435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325578836284864511927653 248546031803412095986435)
                    ·
                      rfl

theorem cell23_1452125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1452125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452125 prefixEnd_1452125 := by exact prefixLift 1452125
  have htrace : WordTrace (prefixWord ++ tailWord_1452125) baseStart_1452125 baseEnd_1452125 := by
    simpa [prefixWord, tailWord_1452125, baseEnd_1452125] using wordTrace_append hprefix tailTrace_1452125
  have hstable : (prefixWord ++ tailWord_1452125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452125).length < 2 ^ (prefixWord ++ tailWord_1452125).sum := by decide
  have hdescent : baseEnd_1452125 < baseStart_1452125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452151 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 1, 5]
def baseStart_1452151 : Nat := 118140960795 + 1452151 * 2 ^ 59
def prefixEnd_1452151 : Nat := 4983230072969 + 3 ^ 40 * 1452151 * 2
def baseEnd_1452151 : Nat := 248550481969084395411395

theorem tailTrace_1452151 : CollatzResearch.WordTrace tailWord_1452151 prefixEnd_1452151 248550481969084395411395 := by
  unfold tailWord_1452151
  simp only [CollatzResearch.WordTrace]
  refine ⟨52964298162112409491012307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35309532108074939660674871 52964298162112409491012307)
  ·
    refine ⟨79446447243168614236518461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52964298162112409491012307 79446447243168614236518461)
    ·
      refine ⟨29792417716188230338694423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79446447243168614236518461 29792417716188230338694423)
      ·
        refine ⟨44688626574282345508041635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29792417716188230338694423 44688626574282345508041635)
        ·
          refine ⟨67032939861423518262062453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44688626574282345508041635 67032939861423518262062453)
          ·
            refine ⟨6284338112008454837068355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67032939861423518262062453 6284338112008454837068355)
            ·
              refine ⟨9426507168012682255602533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284338112008454837068355 9426507168012682255602533)
              ·
                refine ⟨1767470094002377922925475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9426507168012682255602533 1767470094002377922925475)
                ·
                  refine ⟨2651205141003566884388213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767470094002377922925475 2651205141003566884388213)
                  ·
                    refine ⟨248550481969084395411395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2651205141003566884388213 248550481969084395411395)
                    ·
                      rfl

theorem cell23_1452151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_1452151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452151 prefixEnd_1452151 := by exact prefixLift 1452151
  have htrace : WordTrace (prefixWord ++ tailWord_1452151) baseStart_1452151 baseEnd_1452151 := by
    simpa [prefixWord, tailWord_1452151, baseEnd_1452151] using wordTrace_append hprefix tailTrace_1452151
  have hstable : (prefixWord ++ tailWord_1452151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452151).length < 2 ^ (prefixWord ++ tailWord_1452151).sum := by decide
  have hdescent : baseEnd_1452151 < baseStart_1452151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452154 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1452154 : Nat := 118140960795 + 1452154 * 2 ^ 59
def prefixEnd_1452154 : Nat := 4983230072969 + 3 ^ 40 * 1452154 * 2
def baseEnd_1452154 : Nat := 745652986349216674496671

theorem tailTrace_1452154 : CollatzResearch.WordTrace tailWord_1452154 prefixEnd_1452154 745652986349216674496671 := by
  unfold tailWord_1452154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241101895275385250842879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35309605054067694002247677 13241101895275385250842879)
  ·
    refine ⟨19861652842913077876264319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241101895275385250842879 19861652842913077876264319)
    ·
      refine ⟨29792479264369616814396479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861652842913077876264319 29792479264369616814396479)
      ·
        refine ⟨44688718896554425221594719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29792479264369616814396479 44688718896554425221594719)
        ·
          refine ⟨67033078344831637832392079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44688718896554425221594719 67033078344831637832392079)
          ·
            refine ⟨100549617517247456748588119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67033078344831637832392079 100549617517247456748588119)
            ·
              refine ⟨150824426275871185122882179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100549617517247456748588119 150824426275871185122882179)
              ·
                refine ⟨226236639413806777684323269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150824426275871185122882179 226236639413806777684323269)
                ·
                  refine ⟨42419369890088770815810613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226236639413806777684323269 42419369890088770815810613)
                  ·
                    refine ⟨3976815927195822263982245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42419369890088770815810613 3976815927195822263982245)
                    ·
                      refine ⟨745652986349216674496671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3976815927195822263982245 745652986349216674496671)
                      ·
                        rfl

theorem cell23_1452154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1452154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452154 prefixEnd_1452154 := by exact prefixLift 1452154
  have htrace : WordTrace (prefixWord ++ tailWord_1452154) baseStart_1452154 baseEnd_1452154 := by
    simpa [prefixWord, tailWord_1452154, baseEnd_1452154] using wordTrace_append hprefix tailTrace_1452154
  have hstable : (prefixWord ++ tailWord_1452154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452154).length < 2 ^ (prefixWord ++ tailWord_1452154).sum := by decide
  have hdescent : baseEnd_1452154 < baseStart_1452154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452168 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_1452168 : Nat := 118140960795 + 1452168 * 2 ^ 59
def prefixEnd_1452168 : Nat := 4983230072969 + 3 ^ 40 * 1452168 * 2
def baseEnd_1452168 : Nat := 248553391692793206573869

theorem tailTrace_1452168 : CollatzResearch.WordTrace tailWord_1452168 prefixEnd_1452168 248553391692793206573869 := by
  unfold tailWord_1452168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26482459101525410697190579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35309945468700547596254105 26482459101525410697190579)
  ·
    refine ⟨39723688652288116045785869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26482459101525410697190579 39723688652288116045785869)
    ·
      refine ⟨14896383244608043517169701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39723688652288116045785869 14896383244608043517169701)
      ·
        refine ⟨2793071858364008159469319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14896383244608043517169701 2793071858364008159469319)
        ·
          refine ⟨4189607787546012239203979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793071858364008159469319 4189607787546012239203979)
          ·
            refine ⟨6284411681319018358805969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189607787546012239203979 6284411681319018358805969)
            ·
              refine ⟨4713308760989263769104477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6284411681319018358805969 4713308760989263769104477)
              ·
                refine ⟨1767490785370973913414179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4713308760989263769104477 1767490785370973913414179)
                ·
                  refine ⟨2651236178056460870121269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767490785370973913414179 2651236178056460870121269)
                  ·
                    refine ⟨248553391692793206573869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2651236178056460870121269 248553391692793206573869)
                    ·
                      rfl

theorem cell23_1452168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_1452168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452168 prefixEnd_1452168 := by exact prefixLift 1452168
  have htrace : WordTrace (prefixWord ++ tailWord_1452168) baseStart_1452168 baseEnd_1452168 := by
    simpa [prefixWord, tailWord_1452168, baseEnd_1452168] using wordTrace_append hprefix tailTrace_1452168
  have hstable : (prefixWord ++ tailWord_1452168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452168).length < 2 ^ (prefixWord ++ tailWord_1452168).sum := by decide
  have hdescent : baseEnd_1452168 < baseStart_1452168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452181 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1452181 : Nat := 118140960795 + 1452181 * 2 ^ 59
def prefixEnd_1452181 : Nat := 4983230072969 + 3 ^ 40 * 1452181 * 2
def baseEnd_1452181 : Nat := 248555616775629356286349

theorem tailTrace_1452181 : CollatzResearch.WordTrace tailWord_1452181 prefixEnd_1452181 248555616775629356286349 := by
  unfold tailWord_1452181
  simp only [CollatzResearch.WordTrace]
  refine ⟨52965392352003724614604397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35310261568002483076402931 52965392352003724614604397)
  ·
    refine ⟨19862022132001396730476649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52965392352003724614604397 19862022132001396730476649)
    ·
      refine ⟨14896516599001047547857487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19862022132001396730476649 14896516599001047547857487)
      ·
        refine ⟨22344774898501571321786231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14896516599001047547857487 22344774898501571321786231)
        ·
          refine ⟨33517162347752356982679347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22344774898501571321786231 33517162347752356982679347)
          ·
            refine ⟨50275743521628535474019021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33517162347752356982679347 50275743521628535474019021)
            ·
              refine ⟨18853403820610700802757133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50275743521628535474019021 18853403820610700802757133)
              ·
                refine ⟨7070026432729012801033925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18853403820610700802757133 7070026432729012801033925)
                ·
                  refine ⟨1325629956136689900193861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7070026432729012801033925 1325629956136689900193861)
                  ·
                    refine ⟨248555616775629356286349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325629956136689900193861 248555616775629356286349)
                    ·
                      rfl

theorem cell23_1452181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1452181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452181 prefixEnd_1452181 := by exact prefixLift 1452181
  have htrace : WordTrace (prefixWord ++ tailWord_1452181) baseStart_1452181 baseEnd_1452181 := by
    simpa [prefixWord, tailWord_1452181, baseEnd_1452181] using wordTrace_append hprefix tailTrace_1452181
  have hstable : (prefixWord ++ tailWord_1452181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452181).length < 2 ^ (prefixWord ++ tailWord_1452181).sum := by decide
  have hdescent : baseEnd_1452181 < baseStart_1452181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452202 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1452202 : Nat := 118140960795 + 1452202 * 2 ^ 59
def prefixEnd_1452202 : Nat := 4983230072969 + 3 ^ 40 * 1452202 * 2
def baseEnd_1452202 : Nat := 248559211140210828898817

theorem tailTrace_1452202 : CollatzResearch.WordTrace tailWord_1452202 prefixEnd_1452202 248559211140210828898817 := by
  unfold tailWord_1452202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241539571231911300279715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35310772189951763467412573 13241539571231911300279715)
  ·
    refine ⟨19862309356847866950419573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241539571231911300279715 19862309356847866950419573)
    ·
      refine ⟨1862091502204487526601835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19862309356847866950419573 1862091502204487526601835)
      ·
        refine ⟨2793137253306731289902753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862091502204487526601835 2793137253306731289902753)
        ·
          refine ⟨2094852939980048467427065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2793137253306731289902753 2094852939980048467427065)
          ·
            refine ⟨1571139704985036350570299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094852939980048467427065 1571139704985036350570299)
            ·
              refine ⟨2356709557477554525855449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571139704985036350570299 2356709557477554525855449)
              ·
                refine ⟨1767532168108165894391587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356709557477554525855449 1767532168108165894391587)
                ·
                  refine ⟨2651298252162248841587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767532168108165894391587 2651298252162248841587381)
                  ·
                    refine ⟨248559211140210828898817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2651298252162248841587381 248559211140210828898817)
                    ·
                      rfl

theorem cell23_1452202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1452202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452202 prefixEnd_1452202 := by exact prefixLift 1452202
  have htrace : WordTrace (prefixWord ++ tailWord_1452202) baseStart_1452202 baseEnd_1452202 := by
    simpa [prefixWord, tailWord_1452202, baseEnd_1452202] using wordTrace_append hprefix tailTrace_1452202
  have hstable : (prefixWord ++ tailWord_1452202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452202).length < 2 ^ (prefixWord ++ tailWord_1452202).sum := by decide
  have hdescent : baseEnd_1452202 < baseStart_1452202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452205 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1452205 : Nat := 118140960795 + 1452205 * 2 ^ 59
def prefixEnd_1452205 : Nat := 4983230072969 + 3 ^ 40 * 1452205 * 2
def baseEnd_1452205 : Nat := 745679173862595974958937

theorem tailTrace_1452205 : CollatzResearch.WordTrace tailWord_1452205 prefixEnd_1452205 745679173862595974958937 := by
  unfold tailWord_1452205
  simp only [CollatzResearch.WordTrace]
  refine ⟨52966267703916776713478069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35310845135944517808985379 52966267703916776713478069)
  ·
    refine ⟨4965587597242197816888569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52966267703916776713478069 4965587597242197816888569)
    ·
      refine ⟨3724190697931648362666427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4965587597242197816888569 3724190697931648362666427)
      ·
        refine ⟨5586286046897472543999641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724190697931648362666427 5586286046897472543999641)
        ·
          refine ⟨4189714535173104407999731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5586286046897472543999641 4189714535173104407999731)
          ·
            refine ⟨6284571802759656611999597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189714535173104407999731 6284571802759656611999597)
            ·
              refine ⟨2356714426034871229499849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6284571802759656611999597 2356714426034871229499849)
              ·
                refine ⟨1767535819526153422124887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356714426034871229499849 1767535819526153422124887)
                ·
                  refine ⟨2651303729289230133187331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767535819526153422124887 2651303729289230133187331)
                  ·
                    refine ⟨3976955593933845199780997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2651303729289230133187331 3976955593933845199780997)
                    ·
                      refine ⟨745679173862595974958937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3976955593933845199780997 745679173862595974958937)
                      ·
                        rfl

theorem cell23_1452205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1452205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452205 prefixEnd_1452205 := by exact prefixLift 1452205
  have htrace : WordTrace (prefixWord ++ tailWord_1452205) baseStart_1452205 baseEnd_1452205 := by
    simpa [prefixWord, tailWord_1452205, baseEnd_1452205] using wordTrace_append hprefix tailTrace_1452205
  have hstable : (prefixWord ++ tailWord_1452205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452205).length < 2 ^ (prefixWord ++ tailWord_1452205).sum := by decide
  have hdescent : baseEnd_1452205 < baseStart_1452205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452222 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_1452222 : Nat := 118140960795 + 1452222 * 2 ^ 59
def prefixEnd_1452222 : Nat := 4983230072969 + 3 ^ 40 * 1452222 * 2
def baseEnd_1452222 : Nat := 745687903033722408446359

theorem tailTrace_1452222 : CollatzResearch.WordTrace tailWord_1452222 prefixEnd_1452222 745687903033722408446359 := by
  unfold tailWord_1452222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620860968106898577105865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35311258496570125744564613 6620860968106898577105865)
  ·
    refine ⟨4965645726080173932829399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6620860968106898577105865 4965645726080173932829399)
    ·
      refine ⟨7448468589120260899244099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965645726080173932829399 7448468589120260899244099)
      ·
        refine ⟨11172702883680391348866149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448468589120260899244099 11172702883680391348866149)
        ·
          refine ⟨2094881790690073377912403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11172702883680391348866149 2094881790690073377912403)
          ·
            refine ⟨3142322686035110066868605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094881790690073377912403 3142322686035110066868605)
            ·
              refine ⟨1178371007263166275075727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3142322686035110066868605 1178371007263166275075727)
              ·
                refine ⟨1767556510894749412613591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178371007263166275075727 1767556510894749412613591)
                ·
                  refine ⟨2651334766342124118920387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767556510894749412613591 2651334766342124118920387)
                  ·
                    refine ⟨3977002149513186178380581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2651334766342124118920387 3977002149513186178380581)
                    ·
                      refine ⟨745687903033722408446359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3977002149513186178380581 745687903033722408446359)
                      ·
                        rfl

theorem cell23_1452222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_1452222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452222 prefixEnd_1452222 := by exact prefixLift 1452222
  have htrace : WordTrace (prefixWord ++ tailWord_1452222) baseStart_1452222 baseEnd_1452222 := by
    simpa [prefixWord, tailWord_1452222, baseEnd_1452222] using wordTrace_append hprefix tailTrace_1452222
  have hstable : (prefixWord ++ tailWord_1452222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452222).length < 2 ^ (prefixWord ++ tailWord_1452222).sum := by decide
  have hdescent : baseEnd_1452222 < baseStart_1452222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452245 : List Nat := [1, 3, 2, 4, 3, 1, 1, 8]
def baseStart_1452245 : Nat := 118140960795 + 1452245 * 2 ^ 59
def prefixEnd_1452245 : Nat := 4983230072969 + 3 ^ 40 * 1452245 * 2
def baseEnd_1452245 : Nat := 27618507892176882165139

theorem tailTrace_1452245 : CollatzResearch.WordTrace tailWord_1452245 prefixEnd_1452245 27618507892176882165139 := by
  unfold tailWord_1452245
  simp only [CollatzResearch.WordTrace]
  refine ⟨52967726623771863544934189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35311817749181242363289459 52967726623771863544934189)
  ·
    refine ⟨19862897483914448829350321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52967726623771863544934189 19862897483914448829350321)
    ·
      refine ⟨14897173112935836622012741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19862897483914448829350321 14897173112935836622012741)
      ·
        refine ⟨2793219958675469366627389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14897173112935836622012741 2793219958675469366627389)
        ·
          refine ⟨1047457484503301012485271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2793219958675469366627389 1047457484503301012485271)
          ·
            refine ⟨1571186226754951518727907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047457484503301012485271 1571186226754951518727907)
            ·
              refine ⟨2356779340132427278091861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571186226754951518727907 2356779340132427278091861)
              ·
                refine ⟨27618507892176882165139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2356779340132427278091861 27618507892176882165139)
                ·
                  rfl

theorem cell23_1452245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 8].length) (baseStart_1452245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452245 prefixEnd_1452245 := by exact prefixLift 1452245
  have htrace : WordTrace (prefixWord ++ tailWord_1452245) baseStart_1452245 baseEnd_1452245 := by
    simpa [prefixWord, tailWord_1452245, baseEnd_1452245] using wordTrace_append hprefix tailTrace_1452245
  have hstable : (prefixWord ++ tailWord_1452245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452245).length < 2 ^ (prefixWord ++ tailWord_1452245).sum := by decide
  have hdescent : baseEnd_1452245 < baseStart_1452245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452252 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1452252 : Nat := 118140960795 + 1452252 * 2 ^ 59
def prefixEnd_1452252 : Nat := 4983230072969 + 3 ^ 40 * 1452252 * 2
def baseEnd_1452252 : Nat := 745703307453357291071221

theorem tailTrace_1452252 : CollatzResearch.WordTrace tailWord_1452252 prefixEnd_1452252 745703307453357291071221 := by
  unfold tailWord_1452252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26483990967373251870219505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35311987956497669160292673 26483990967373251870219505)
  ·
    refine ⟨19862993225529938902664629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26483990967373251870219505 19862993225529938902664629)
    ·
      refine ⟨1862155614893431772124809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19862993225529938902664629 1862155614893431772124809)
      ·
        refine ⟨1396616711170073829093607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1862155614893431772124809 1396616711170073829093607)
        ·
          refine ⟨2094925066755110743640411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396616711170073829093607 2094925066755110743640411)
          ·
            refine ⟨3142387600132666115460617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094925066755110743640411 3142387600132666115460617)
            ·
              refine ⟨2356790700099499586595463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142387600132666115460617 2356790700099499586595463)
              ·
                refine ⟨3535186050149249379893195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356790700099499586595463 3535186050149249379893195)
                ·
                  refine ⟨5302779075223874069839793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535186050149249379893195 5302779075223874069839793)
                  ·
                    refine ⟨3977084306417905552379845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302779075223874069839793 3977084306417905552379845)
                    ·
                      refine ⟨745703307453357291071221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3977084306417905552379845 745703307453357291071221)
                      ·
                        rfl

theorem cell23_1452252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1452252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452252 prefixEnd_1452252 := by exact prefixLift 1452252
  have htrace : WordTrace (prefixWord ++ tailWord_1452252) baseStart_1452252 baseEnd_1452252 := by
    simpa [prefixWord, tailWord_1452252, baseEnd_1452252] using wordTrace_append hprefix tailTrace_1452252
  have hstable : (prefixWord ++ tailWord_1452252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452252).length < 2 ^ (prefixWord ++ tailWord_1452252).sum := by decide
  have hdescent : baseEnd_1452252 < baseStart_1452252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452281 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1452281 : Nat := 118140960795 + 1452281 * 2 ^ 59
def prefixEnd_1452281 : Nat := 4983230072969 + 3 ^ 40 * 1452281 * 2
def baseEnd_1452281 : Nat := 745718198392337677608587

theorem tailTrace_1452281 : CollatzResearch.WordTrace tailWord_1452281 prefixEnd_1452281 745718198392337677608587 := by
  unfold tailWord_1452281
  simp only [CollatzResearch.WordTrace]
  refine ⟨52969039651641441693244697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312693101094294462163131 52969039651641441693244697)
  ·
    refine ⟨39726779738731081269933523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52969039651641441693244697 39726779738731081269933523)
    ·
      refine ⟨59590169608096621904900285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39726779738731081269933523 59590169608096621904900285)
      ·
        refine ⟨22346313603036233214337607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59590169608096621904900285 22346313603036233214337607)
        ·
          refine ⟨33519470404554349821506411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22346313603036233214337607 33519470404554349821506411)
          ·
            refine ⟨50279205606831524732259617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33519470404554349821506411 50279205606831524732259617)
            ·
              refine ⟨37709404205123643549194713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50279205606831524732259617 37709404205123643549194713)
              ·
                refine ⟨28282053153842732661896035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37709404205123643549194713 28282053153842732661896035)
                ·
                  refine ⟨42423079730764098992844053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28282053153842732661896035 42423079730764098992844053)
                  ·
                    refine ⟨1988581862379567140289565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42423079730764098992844053 1988581862379567140289565)
                    ·
                      refine ⟨745718198392337677608587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988581862379567140289565 745718198392337677608587)
                      ·
                        rfl

theorem cell23_1452281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1452281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452281 prefixEnd_1452281 := by exact prefixLift 1452281
  have htrace : WordTrace (prefixWord ++ tailWord_1452281) baseStart_1452281 baseEnd_1452281 := by
    simpa [prefixWord, tailWord_1452281, baseEnd_1452281] using wordTrace_append hprefix tailTrace_1452281
  have hstable : (prefixWord ++ tailWord_1452281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452281).length < 2 ^ (prefixWord ++ tailWord_1452281).sum := by decide
  have hdescent : baseEnd_1452281 < baseStart_1452281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452282 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_1452282 : Nat := 118140960795 + 1452282 * 2 ^ 59
def prefixEnd_1452282 : Nat := 4983230072969 + 3 ^ 40 * 1452282 * 2
def baseEnd_1452282 : Nat := 745718711872992173696083

theorem tailTrace_1452282 : CollatzResearch.WordTrace tailWord_1452282 prefixEnd_1452282 745718711872992173696083 := by
  unfold tailWord_1452282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242269031159454716007775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35312717416425212576020733 13242269031159454716007775)
  ·
    refine ⟨19863403546739182074011663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13242269031159454716007775 19863403546739182074011663)
    ·
      refine ⟨29795105320108773111017495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19863403546739182074011663 29795105320108773111017495)
      ·
        refine ⟨44692657980163159666526243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29795105320108773111017495 44692657980163159666526243)
        ·
          refine ⟨67038986970244739499789365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44692657980163159666526243 67038986970244739499789365)
          ·
            refine ⟨6284905028460444328105253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67038986970244739499789365 6284905028460444328105253)
            ·
              refine ⟨1178419692836333311519735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6284905028460444328105253 1178419692836333311519735)
              ·
                refine ⟨1767629539254499967279603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178419692836333311519735 1767629539254499967279603)
                ·
                  refine ⟨2651444308881749950919405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767629539254499967279603 2651444308881749950919405)
                  ·
                    refine ⟨994291615830656231594777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651444308881749950919405 994291615830656231594777)
                    ·
                      refine ⟨745718711872992173696083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994291615830656231594777 745718711872992173696083)
                      ·
                        rfl

theorem cell23_1452282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_1452282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452282 prefixEnd_1452282 := by exact prefixLift 1452282
  have htrace : WordTrace (prefixWord ++ tailWord_1452282) baseStart_1452282 baseEnd_1452282 := by
    simpa [prefixWord, tailWord_1452282, baseEnd_1452282] using wordTrace_append hprefix tailTrace_1452282
  have hstable : (prefixWord ++ tailWord_1452282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452282).length < 2 ^ (prefixWord ++ tailWord_1452282).sum := by decide
  have hdescent : baseEnd_1452282 < baseStart_1452282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452291 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1452291 : Nat := 118140960795 + 1452291 * 2 ^ 59
def prefixEnd_1452291 : Nat := 4983230072969 + 3 ^ 40 * 1452291 * 2
def baseEnd_1452291 : Nat := 745723333198882638483541

theorem tailTrace_1452291 : CollatzResearch.WordTrace tailWord_1452291 prefixEnd_1452291 745723333198882638483541 := by
  unfold tailWord_1452291
  simp only [CollatzResearch.WordTrace]
  refine ⟨52969404381605213401108727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35312936254403475600739151 52969404381605213401108727)
  ·
    refine ⟨79454106572407820101663091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52969404381605213401108727 79454106572407820101663091)
    ·
      refine ⟨119181159858611730152494637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79454106572407820101663091 119181159858611730152494637)
      ·
        refine ⟨44692934946979398807185489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119181159858611730152494637 44692934946979398807185489)
        ·
          refine ⟨33519701210234549105389117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44692934946979398807185489 33519701210234549105389117)
          ·
            refine ⟨12569887953837955914520919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33519701210234549105389117 12569887953837955914520919)
            ·
              refine ⟨18854831930756933871781379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12569887953837955914520919 18854831930756933871781379)
              ·
                refine ⟨28282247896135400807672069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18854831930756933871781379 28282247896135400807672069)
                ·
                  refine ⟨5302921480525387651438513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28282247896135400807672069 5302921480525387651438513)
                  ·
                    refine ⟨3977191110394040738578885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302921480525387651438513 3977191110394040738578885)
                    ·
                      refine ⟨745723333198882638483541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3977191110394040738578885 745723333198882638483541)
                      ·
                        rfl

theorem cell23_1452291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1452291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452291 prefixEnd_1452291 := by exact prefixLift 1452291
  have htrace : WordTrace (prefixWord ++ tailWord_1452291) baseStart_1452291 baseEnd_1452291 := by
    simpa [prefixWord, tailWord_1452291, baseEnd_1452291] using wordTrace_append hprefix tailTrace_1452291
  have hstable : (prefixWord ++ tailWord_1452291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452291).length < 2 ^ (prefixWord ++ tailWord_1452291).sum := by decide
  have hdescent : baseEnd_1452291 < baseStart_1452291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452348 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1452348 : Nat := 118140960795 + 1452348 * 2 ^ 59
def prefixEnd_1452348 : Nat := 4983230072969 + 3 ^ 40 * 1452348 * 2
def baseEnd_1452348 : Nat := 248584200532062971823593

theorem tailTrace_1452348 : CollatzResearch.WordTrace tailWord_1452348 prefixEnd_1452348 248584200532062971823593 := by
  unfold tailWord_1452348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26485741671199356067966849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35314322228265808090622465 26485741671199356067966849)
  ·
    refine ⟨19864306253399517050975137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26485741671199356067966849 19864306253399517050975137)
    ·
      refine ⟨14898229690049637788231353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19864306253399517050975137 14898229690049637788231353)
      ·
        refine ⟨11173672267537228341173515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14898229690049637788231353 11173672267537228341173515)
        ·
          refine ⟨16760508401305842511760273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11173672267537228341173515 16760508401305842511760273)
          ·
            refine ⟨12570381300979381883820205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16760508401305842511760273 12570381300979381883820205)
            ·
              refine ⟨4713892987867268206432577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12570381300979381883820205 4713892987867268206432577)
              ·
                refine ⟨3535419740900451154824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713892987867268206432577 3535419740900451154824433)
                ·
                  refine ⟨2651564805675338366118325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3535419740900451154824433 2651564805675338366118325)
                  ·
                    refine ⟨248584200532062971823593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2651564805675338366118325 248584200532062971823593)
                    ·
                      rfl

theorem cell23_1452348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1452348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452348 prefixEnd_1452348 := by exact prefixLift 1452348
  have htrace : WordTrace (prefixWord ++ tailWord_1452348) baseStart_1452348 baseEnd_1452348 := by
    simpa [prefixWord, tailWord_1452348, baseEnd_1452348] using wordTrace_append hprefix tailTrace_1452348
  have hstable : (prefixWord ++ tailWord_1452348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452348).length < 2 ^ (prefixWord ++ tailWord_1452348).sum := by decide
  have hdescent : baseEnd_1452348 < baseStart_1452348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452378 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_1452378 : Nat := 118140960795 + 1452378 * 2 ^ 59
def prefixEnd_1452378 : Nat := 4983230072969 + 3 ^ 40 * 1452378 * 2
def baseEnd_1452378 : Nat := 248589335338607932698547

theorem tailTrace_1452378 : CollatzResearch.WordTrace tailWord_1452378 prefixEnd_1452378 248589335338607932698547 := by
  unfold tailWord_1452378
  simp only [CollatzResearch.WordTrace]
  refine ⟨13243144383072506814881447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35315051688193351506350525 13243144383072506814881447)
  ·
    refine ⟨19864716574608760222322171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13243144383072506814881447 19864716574608760222322171)
    ·
      refine ⟨29797074861913140333483257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19864716574608760222322171 29797074861913140333483257)
      ·
        refine ⟨22347806146434855250112443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29797074861913140333483257 22347806146434855250112443)
        ·
          refine ⟨33521709219652282875168665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22347806146434855250112443 33521709219652282875168665)
          ·
            refine ⟨25141281914739212156376499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33521709219652282875168665 25141281914739212156376499)
            ·
              refine ⟨37711922872108818234564749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25141281914739212156376499 37711922872108818234564749)
              ·
                refine ⟨14141971077040806837961781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37711922872108818234564749 14141971077040806837961781)
                ·
                  refine ⟨1325809788472575641058917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14141971077040806837961781 1325809788472575641058917)
                  ·
                    refine ⟨248589335338607932698547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325809788472575641058917 248589335338607932698547)
                    ·
                      rfl

theorem cell23_1452378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_1452378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452378 prefixEnd_1452378 := by exact prefixLift 1452378
  have htrace : WordTrace (prefixWord ++ tailWord_1452378) baseStart_1452378 baseEnd_1452378 := by
    simpa [prefixWord, tailWord_1452378, baseEnd_1452378] using wordTrace_append hprefix tailTrace_1452378
  have hstable : (prefixWord ++ tailWord_1452378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452378).length < 2 ^ (prefixWord ++ tailWord_1452378).sum := by decide
  have hdescent : baseEnd_1452378 < baseStart_1452378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452446 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1452446 : Nat := 118140960795 + 1452446 * 2 ^ 59
def prefixEnd_1452446 : Nat := 4983230072969 + 3 ^ 40 * 1452446 * 2
def baseEnd_1452446 : Nat := 248600974233443177348443

theorem tailTrace_1452446 : CollatzResearch.WordTrace tailWord_1452446 prefixEnd_1452446 248600974233443177348443 := by
  unfold tailWord_1452446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621882212005459359125149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35316705130695783248667461 6621882212005459359125149)
  ·
    refine ⟨2483205829502047259671931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6621882212005459359125149 2483205829502047259671931)
    ·
      refine ⟨3724808744253070889507897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483205829502047259671931 3724808744253070889507897)
      ·
        refine ⟨2793606558189803167130923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3724808744253070889507897 2793606558189803167130923)
        ·
          refine ⟨4190409837284704750696385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793606558189803167130923 4190409837284704750696385)
          ·
            refine ⟨3142807377963528563022289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4190409837284704750696385 3142807377963528563022289)
            ·
              refine ⟨2357105533472646422266717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142807377963528563022289 2357105533472646422266717)
              ·
                refine ⟨883914575052242408350019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2357105533472646422266717 883914575052242408350019)
                ·
                  refine ⟨1325871862578363612525029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883914575052242408350019 1325871862578363612525029)
                  ·
                    refine ⟨248600974233443177348443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325871862578363612525029 248600974233443177348443)
                    ·
                      rfl

theorem cell23_1452446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1452446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452446 prefixEnd_1452446 := by exact prefixLift 1452446
  have htrace : WordTrace (prefixWord ++ tailWord_1452446) baseStart_1452446 baseEnd_1452446 := by
    simpa [prefixWord, tailWord_1452446, baseEnd_1452446] using wordTrace_append hprefix tailTrace_1452446
  have hstable : (prefixWord ++ tailWord_1452446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452446).length < 2 ^ (prefixWord ++ tailWord_1452446).sum := by decide
  have hdescent : baseEnd_1452446 < baseStart_1452446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452469 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1452469 : Nat := 118140960795 + 1452469 * 2 ^ 59
def prefixEnd_1452469 : Nat := 4983230072969 + 3 ^ 40 * 1452469 * 2
def baseEnd_1452469 : Nat := 745814732755382942057723

theorem tailTrace_1452469 : CollatzResearch.WordTrace tailWord_1452469 prefixEnd_1452469 745814732755382942057723 := by
  unfold tailWord_1452469
  simp only [CollatzResearch.WordTrace]
  refine ⟨52975896574960349801088461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35317264383306899867392307 52975896574960349801088461)
  ·
    refine ⟨19865961215610131175408173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52975896574960349801088461 19865961215610131175408173)
    ·
      refine ⟨7449735455853799190778065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19865961215610131175408173 7449735455853799190778065)
      ·
        refine ⟨5587301591890349393083549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7449735455853799190778065 5587301591890349393083549)
        ·
          refine ⟨2095238096958881022406331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5587301591890349393083549 2095238096958881022406331)
          ·
            refine ⟨3142857145438321533609497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095238096958881022406331 3142857145438321533609497)
            ·
              refine ⟨2357142859078741150207123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142857145438321533609497 2357142859078741150207123)
              ·
                refine ⟨3535714288618111725310685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357142859078741150207123 3535714288618111725310685)
                ·
                  refine ⟨1325892858231791896991507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535714288618111725310685 1325892858231791896991507)
                  ·
                    refine ⟨1988839287347687845487261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325892858231791896991507 1988839287347687845487261)
                    ·
                      refine ⟨745814732755382942057723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988839287347687845487261 745814732755382942057723)
                      ·
                        rfl

theorem cell23_1452469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1452469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452469 prefixEnd_1452469 := by exact prefixLift 1452469
  have htrace : WordTrace (prefixWord ++ tailWord_1452469) baseStart_1452469 baseEnd_1452469 := by
    simpa [prefixWord, tailWord_1452469, baseEnd_1452469] using wordTrace_append hprefix tailTrace_1452469
  have hstable : (prefixWord ++ tailWord_1452469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452469).length < 2 ^ (prefixWord ++ tailWord_1452469).sum := by decide
  have hdescent : baseEnd_1452469 < baseStart_1452469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452502 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1452502 : Nat := 118140960795 + 1452502 * 2 ^ 59
def prefixEnd_1452502 : Nat := 4983230072969 + 3 ^ 40 * 1452502 * 2
def baseEnd_1452502 : Nat := 248610559205660437648357

theorem tailTrace_1452502 : CollatzResearch.WordTrace tailWord_1452502 prefixEnd_1452502 248610559205660437648357 := by
  unfold tailWord_1452502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311068761490049777314985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35318066789227197624693173 3311068761490049777314985)
  ·
    refine ⟨2483301571117537332986239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3311068761490049777314985 2483301571117537332986239)
    ·
      refine ⟨3724952356676305999479359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483301571117537332986239 3724952356676305999479359)
      ·
        refine ⟨5587428535014458999219039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724952356676305999479359 5587428535014458999219039)
        ·
          refine ⟨8381142802521688498828559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587428535014458999219039 8381142802521688498828559)
          ·
            refine ⟨12571714203782532748242839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381142802521688498828559 12571714203782532748242839)
            ·
              refine ⟨18857571305673799122364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12571714203782532748242839 18857571305673799122364259)
              ·
                refine ⟨28286356958510698683546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18857571305673799122364259 28286356958510698683546389)
                ·
                  refine ⟨1325922982430189000791237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28286356958510698683546389 1325922982430189000791237)
                  ·
                    refine ⟨248610559205660437648357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325922982430189000791237 248610559205660437648357)
                    ·
                      rfl

theorem cell23_1452502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1452502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452502 prefixEnd_1452502 := by exact prefixLift 1452502
  have htrace : WordTrace (prefixWord ++ tailWord_1452502) baseStart_1452502 baseEnd_1452502 := by
    simpa [prefixWord, tailWord_1452502, baseEnd_1452502] using wordTrace_append hprefix tailTrace_1452502
  have hstable : (prefixWord ++ tailWord_1452502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452502).length < 2 ^ (prefixWord ++ tailWord_1452502).sum := by decide
  have hdescent : baseEnd_1452502 < baseStart_1452502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452515 : List Nat := [1, 1, 1, 6, 3, 2, 9]
def baseStart_1452515 : Nat := 118140960795 + 1452515 * 2 ^ 59
def prefixEnd_1452515 : Nat := 4983230072969 + 3 ^ 40 * 1452515 * 2
def baseEnd_1452515 : Nat := 9207880899573947680031

theorem tailTrace_1452515 : CollatzResearch.WordTrace tailWord_1452515 prefixEnd_1452515 9207880899573947680031 := by
  unfold tailWord_1452515
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977574332793699657262999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35318382888529133104841999 52977574332793699657262999)
  ·
    refine ⟨79466361499190549485894499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52977574332793699657262999 79466361499190549485894499)
    ·
      refine ⟨119199542248785824228841749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79466361499190549485894499 119199542248785824228841749)
      ·
        refine ⟨5587478542911835510726957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119199542248785824228841749 5587478542911835510726957)
        ·
          refine ⟨2095304453591938316522609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5587478542911835510726957 2095304453591938316522609)
          ·
            refine ⟨1571478340193953737391957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095304453591938316522609 1571478340193953737391957)
            ·
              refine ⟨9207880899573947680031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1571478340193953737391957 9207880899573947680031)
              ·
                rfl

theorem cell23_1452515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 9].length) (baseStart_1452515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452515 prefixEnd_1452515 := by exact prefixLift 1452515
  have htrace : WordTrace (prefixWord ++ tailWord_1452515) baseStart_1452515 baseEnd_1452515 := by
    simpa [prefixWord, tailWord_1452515, baseEnd_1452515] using wordTrace_append hprefix tailTrace_1452515
  have hstable : (prefixWord ++ tailWord_1452515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452515).length < 2 ^ (prefixWord ++ tailWord_1452515).sum := by decide
  have hdescent : baseEnd_1452515 < baseStart_1452515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452526 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_1452526 : Nat := 118140960795 + 1452526 * 2 ^ 59
def prefixEnd_1452526 : Nat := 4983230072969 + 3 ^ 40 * 1452526 * 2
def baseEnd_1452526 : Nat := 745844001152689219044961

theorem tailTrace_1452526 : CollatzResearch.WordTrace tailWord_1452526 prefixEnd_1452526 745844001152689219044961 := by
  unfold tailWord_1452526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622246941969231066989179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35318650357169232357275621 6622246941969231066989179)
  ·
    refine ⟨9933370412953846600483769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622246941969231066989179 9933370412953846600483769)
    ·
      refine ⟨7450027809715384950362827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9933370412953846600483769 7450027809715384950362827)
      ·
        refine ⟨11175041714573077425544241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7450027809715384950362827 11175041714573077425544241)
        ·
          refine ⟨8381281285929808069158181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175041714573077425544241 8381281285929808069158181)
          ·
            refine ⟨1571490241111839012967159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8381281285929808069158181 1571490241111839012967159)
            ·
              refine ⟨2357235361667758519450739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571490241111839012967159 2357235361667758519450739)
              ·
                refine ⟨3535853042501637779176109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357235361667758519450739 3535853042501637779176109)
                ·
                  refine ⟨1325944890938114167191041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535853042501637779176109 1325944890938114167191041)
                  ·
                    refine ⟨994458668203585625393281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1325944890938114167191041 994458668203585625393281)
                    ·
                      refine ⟨745844001152689219044961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994458668203585625393281 745844001152689219044961)
                      ·
                        rfl

theorem cell23_1452526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_1452526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452526 prefixEnd_1452526 := by exact prefixLift 1452526
  have htrace : WordTrace (prefixWord ++ tailWord_1452526) baseStart_1452526 baseEnd_1452526 := by
    simpa [prefixWord, tailWord_1452526, baseEnd_1452526] using wordTrace_append hprefix tailTrace_1452526
  have hstable : (prefixWord ++ tailWord_1452526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452526).length < 2 ^ (prefixWord ++ tailWord_1452526).sum := by decide
  have hdescent : baseEnd_1452526 < baseStart_1452526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452528 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_1452528 : Nat := 118140960795 + 1452528 * 2 ^ 59
def prefixEnd_1452528 : Nat := 4983230072969 + 3 ^ 40 * 1452528 * 2
def baseEnd_1452528 : Nat := 248615009371332737073317

theorem tailTrace_1452528 : CollatzResearch.WordTrace tailWord_1452528 prefixEnd_1452528 248615009371332737073317 := by
  unfold tailWord_1452528
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489024240873301438743119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35318698987831068584990825 26489024240873301438743119)
  ·
    refine ⟨39733536361309952158114679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489024240873301438743119 39733536361309952158114679)
    ·
      refine ⟨59600304541964928237172019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39733536361309952158114679 59600304541964928237172019)
      ·
        refine ⟨89400456812947392355758029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59600304541964928237172019 89400456812947392355758029)
        ·
          refine ⟨33525171304855272133409261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89400456812947392355758029 33525171304855272133409261)
          ·
            refine ⟨12571939239320727050028473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33525171304855272133409261 12571939239320727050028473)
            ·
              refine ⟨9428954429490545287521355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12571939239320727050028473 9428954429490545287521355)
              ·
                refine ⟨14143431644235817931282033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9428954429490545287521355 14143431644235817931282033)
                ·
                  refine ⟨10607573733176863448461525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14143431644235817931282033 10607573733176863448461525)
                  ·
                    refine ⟨248615009371332737073317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10607573733176863448461525 248615009371332737073317)
                    ·
                      rfl

theorem cell23_1452528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_1452528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452528 prefixEnd_1452528 := by exact prefixLift 1452528
  have htrace : WordTrace (prefixWord ++ tailWord_1452528) baseStart_1452528 baseEnd_1452528 := by
    simpa [prefixWord, tailWord_1452528, baseEnd_1452528] using wordTrace_append hprefix tailTrace_1452528
  have hstable : (prefixWord ++ tailWord_1452528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452528).length < 2 ^ (prefixWord ++ tailWord_1452528).sum := by decide
  have hdescent : baseEnd_1452528 < baseStart_1452528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452538 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_1452538 : Nat := 118140960795 + 1452538 * 2 ^ 59
def prefixEnd_1452538 : Nat := 4983230072969 + 3 ^ 40 * 1452538 * 2
def baseEnd_1452538 : Nat := 745850162920543172094905

theorem tailTrace_1452538 : CollatzResearch.WordTrace tailWord_1452538 prefixEnd_1452538 745850162920543172094905 := by
  unfold tailWord_1452538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244603302927593646337567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35318942141140249723566845 13244603302927593646337567)
  ·
    refine ⟨19866904954391390469506351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244603302927593646337567 19866904954391390469506351)
    ·
      refine ⟨29800357431587085704259527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19866904954391390469506351 29800357431587085704259527)
      ·
        refine ⟨44700536147380628556389291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29800357431587085704259527 44700536147380628556389291)
        ·
          refine ⟨67050804221070942834583937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44700536147380628556389291 67050804221070942834583937)
          ·
            refine ⟨50288103165803207125937953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67050804221070942834583937 50288103165803207125937953)
            ·
              refine ⟨37716077374352405344453465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50288103165803207125937953 37716077374352405344453465)
              ·
                refine ⟨28287058030764304008340099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37716077374352405344453465 28287058030764304008340099)
                ·
                  refine ⟨42430587046146456012510149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28287058030764304008340099 42430587046146456012510149)
                  ·
                    refine ⟨7955735071152460502345653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42430587046146456012510149 7955735071152460502345653)
                    ·
                      refine ⟨745850162920543172094905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7955735071152460502345653 745850162920543172094905)
                      ·
                        rfl

theorem cell23_1452538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_1452538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452538 prefixEnd_1452538 := by exact prefixLift 1452538
  have htrace : WordTrace (prefixWord ++ tailWord_1452538) baseStart_1452538 baseEnd_1452538 := by
    simpa [prefixWord, tailWord_1452538, baseEnd_1452538] using wordTrace_append hprefix tailTrace_1452538
  have hstable : (prefixWord ++ tailWord_1452538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452538).length < 2 ^ (prefixWord ++ tailWord_1452538).sum := by decide
  have hdescent : baseEnd_1452538 < baseStart_1452538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452576 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1452576 : Nat := 118140960795 + 1452576 * 2 ^ 59
def prefixEnd_1452576 : Nat := 4983230072969 + 3 ^ 40 * 1452576 * 2
def baseEnd_1452576 : Nat := 745869675185414023419731

theorem tailTrace_1452576 : CollatzResearch.WordTrace tailWord_1452576 prefixEnd_1452576 745869675185414023419731 := by
  unfold tailWord_1452576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489899592786353537616791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35319866123715138050155721 26489899592786353537616791)
  ·
    refine ⟨39734849389179530306425187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489899592786353537616791 39734849389179530306425187)
    ·
      refine ⟨59602274083769295459637781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39734849389179530306425187 59602274083769295459637781)
      ·
        refine ⟨2793856597676685724670521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59602274083769295459637781 2793856597676685724670521)
        ·
          refine ⟨2095392448257514293502891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2793856597676685724670521 2095392448257514293502891)
          ·
            refine ⟨3143088672386271440254337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095392448257514293502891 3143088672386271440254337)
            ·
              refine ⟨2357316504289703580190753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143088672386271440254337 2357316504289703580190753)
              ·
                refine ⟨1767987378217277685143065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357316504289703580190753 1767987378217277685143065)
                ·
                  refine ⟨1325990533662958263857299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1767987378217277685143065 1325990533662958263857299)
                  ·
                    refine ⟨1988985800494437395785949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1325990533662958263857299 1988985800494437395785949)
                    ·
                      refine ⟨745869675185414023419731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1988985800494437395785949 745869675185414023419731)
                      ·
                        rfl

theorem cell23_1452576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1452576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452576 prefixEnd_1452576 := by exact prefixLift 1452576
  have htrace : WordTrace (prefixWord ++ tailWord_1452576) baseStart_1452576 baseEnd_1452576 := by
    simpa [prefixWord, tailWord_1452576, baseEnd_1452576] using wordTrace_append hprefix tailTrace_1452576
  have hstable : (prefixWord ++ tailWord_1452576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452576).length < 2 ^ (prefixWord ++ tailWord_1452576).sum := by decide
  have hdescent : baseEnd_1452576 < baseStart_1452576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452588 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 11]
def baseStart_1452588 : Nat := 118140960795 + 1452588 * 2 ^ 59
def prefixEnd_1452588 : Nat := 4983230072969 + 3 ^ 40 * 1452588 * 2
def baseEnd_1452588 : Nat := 82875092994807552941075

theorem tailTrace_1452588 : CollatzResearch.WordTrace tailWord_1452588 prefixEnd_1452588 82875092994807552941075 := by
  unfold tailWord_1452588
  simp only [CollatzResearch.WordTrace]
  refine ⟨26490118430764616562335209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35320157907686155416446945 26490118430764616562335209)
  ·
    refine ⟨19867588823073462421751407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26490118430764616562335209 19867588823073462421751407)
    ·
      refine ⟨29801383234610193632627111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19867588823073462421751407 29801383234610193632627111)
      ·
        refine ⟨44702074851915290448940667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801383234610193632627111 44702074851915290448940667)
        ·
          refine ⟨67053112277872935673411001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44702074851915290448940667 67053112277872935673411001)
          ·
            refine ⟨50289834208404701755058251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67053112277872935673411001 50289834208404701755058251)
            ·
              refine ⟨75434751312607052632587377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50289834208404701755058251 75434751312607052632587377)
              ·
                refine ⟨56576063484455289474440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75434751312607052632587377 56576063484455289474440533)
                ·
                  refine ⟨82875092994807552941075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 56576063484455289474440533 82875092994807552941075)
                  ·
                    rfl

theorem cell23_1452588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_1452588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452588 prefixEnd_1452588 := by exact prefixLift 1452588
  have htrace : WordTrace (prefixWord ++ tailWord_1452588) baseStart_1452588 baseEnd_1452588 := by
    simpa [prefixWord, tailWord_1452588, baseEnd_1452588] using wordTrace_append hprefix tailTrace_1452588
  have hstable : (prefixWord ++ tailWord_1452588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452588).length < 2 ^ (prefixWord ++ tailWord_1452588).sum := by decide
  have hdescent : baseEnd_1452588 < baseStart_1452588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452595 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4]
def baseStart_1452595 : Nat := 118140960795 + 1452595 * 2 ^ 59
def prefixEnd_1452595 : Nat := 4983230072969 + 3 ^ 40 * 1452595 * 2
def baseEnd_1452595 : Nat := 745879431317849449082143

theorem tailTrace_1452595 : CollatzResearch.WordTrace tailWord_1452595 prefixEnd_1452595 745879431317849449082143 := by
  unfold tailWord_1452595
  simp only [CollatzResearch.WordTrace]
  refine ⟨52980492172503873320175239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35320328115002582213450159 52980492172503873320175239)
  ·
    refine ⟨79470738258755809980262859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52980492172503873320175239 79470738258755809980262859)
    ·
      refine ⟨119206107388133714970394289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79470738258755809980262859 119206107388133714970394289)
      ·
        refine ⟨89404580541100286227795717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119206107388133714970394289 89404580541100286227795717)
        ·
          refine ⟨16763358851456303667711697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89404580541100286227795717 16763358851456303667711697)
          ·
            refine ⟨12572519138592227750783773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16763358851456303667711697 12572519138592227750783773)
            ·
              refine ⟨4714694676972085406543915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12572519138592227750783773 4714694676972085406543915)
              ·
                refine ⟨7072042015458128109815873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714694676972085406543915 7072042015458128109815873)
                ·
                  refine ⟨5304031511593596082361905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7072042015458128109815873 5304031511593596082361905)
                  ·
                    refine ⟨3978023633695197061771429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5304031511593596082361905 3978023633695197061771429)
                    ·
                      refine ⟨745879431317849449082143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3978023633695197061771429 745879431317849449082143)
                      ·
                        rfl

theorem cell23_1452595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_1452595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452595 prefixEnd_1452595 := by exact prefixLift 1452595
  have htrace : WordTrace (prefixWord ++ tailWord_1452595) baseStart_1452595 baseEnd_1452595 := by
    simpa [prefixWord, tailWord_1452595, baseEnd_1452595] using wordTrace_append hprefix tailTrace_1452595
  have hstable : (prefixWord ++ tailWord_1452595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452595).length < 2 ^ (prefixWord ++ tailWord_1452595).sum := by decide
  have hdescent : baseEnd_1452595 < baseStart_1452595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452599 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_1452599 : Nat := 118140960795 + 1452599 * 2 ^ 59
def prefixEnd_1452599 : Nat := 4983230072969 + 3 ^ 40 * 1452599 * 2
def baseEnd_1452599 : Nat := 745881485240467433432125

theorem tailTrace_1452599 : CollatzResearch.WordTrace tailWord_1452599 prefixEnd_1452599 745881485240467433432125 := by
  unfold tailWord_1452599
  simp only [CollatzResearch.WordTrace]
  refine ⟨52980638064489382003320851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35320425376326254668880567 52980638064489382003320851)
  ·
    refine ⟨79470957096734073004981277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52980638064489382003320851 79470957096734073004981277)
    ·
      refine ⟨29801608911275277376867979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79470957096734073004981277 29801608911275277376867979)
      ·
        refine ⟨44702413366912916065301969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801608911275277376867979 44702413366912916065301969)
        ·
          refine ⟨33526810025184687048976477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44702413366912916065301969 33526810025184687048976477)
          ·
            refine ⟨12572553759444257643366179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33526810025184687048976477 12572553759444257643366179)
            ·
              refine ⟨18858830639166386465049269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572553759444257643366179 18858830639166386465049269)
              ·
                refine ⟨1768015372421848731098369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18858830639166386465049269 1768015372421848731098369)
                ·
                  refine ⟨1326011529316386548323777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768015372421848731098369 1326011529316386548323777)
                  ·
                    refine ⟨994508646987289911242833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1326011529316386548323777 994508646987289911242833)
                    ·
                      refine ⟨745881485240467433432125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994508646987289911242833 745881485240467433432125)
                      ·
                        rfl

theorem cell23_1452599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_1452599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452599 prefixEnd_1452599 := by exact prefixLift 1452599
  have htrace : WordTrace (prefixWord ++ tailWord_1452599) baseStart_1452599 baseEnd_1452599 := by
    simpa [prefixWord, tailWord_1452599, baseEnd_1452599] using wordTrace_append hprefix tailTrace_1452599
  have hstable : (prefixWord ++ tailWord_1452599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452599).length < 2 ^ (prefixWord ++ tailWord_1452599).sum := by decide
  have hdescent : baseEnd_1452599 < baseStart_1452599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452605 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 9]
def baseStart_1452605 : Nat := 118140960795 + 1452605 * 2 ^ 59
def prefixEnd_1452605 : Nat := 4983230072969 + 3 ^ 40 * 1452605 * 2
def baseEnd_1452605 : Nat := 82876062902710489995233

theorem tailTrace_1452605 : CollatzResearch.WordTrace tailWord_1452605 prefixEnd_1452605 82876062902710489995233 := by
  unfold tailWord_1452605
  simp only [CollatzResearch.WordTrace]
  refine ⟨52980856902467645028039269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35320571268311763352026179 52980856902467645028039269)
  ·
    refine ⟨9933910669212683442757363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52980856902467645028039269 9933910669212683442757363)
    ·
      refine ⟨14900866003819025164136045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933910669212683442757363 14900866003819025164136045)
      ·
        refine ⟨5587824751432134436551017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14900866003819025164136045 5587824751432134436551017)
        ·
          refine ⟨4190868563574100827413263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5587824751432134436551017 4190868563574100827413263)
          ·
            refine ⟨6286302845361151241119895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190868563574100827413263 6286302845361151241119895)
            ·
              refine ⟨9429454268041726861679843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286302845361151241119895 9429454268041726861679843)
              ·
                refine ⟨14144181402062590292519765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429454268041726861679843 14144181402062590292519765)
                ·
                  refine ⟨82876062902710489995233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14144181402062590292519765 82876062902710489995233)
                  ·
                    rfl

theorem cell23_1452605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_1452605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452605 prefixEnd_1452605 := by exact prefixLift 1452605
  have htrace : WordTrace (prefixWord ++ tailWord_1452605) baseStart_1452605 baseEnd_1452605 := by
    simpa [prefixWord, tailWord_1452605, baseEnd_1452605] using wordTrace_append hprefix tailTrace_1452605
  have hstable : (prefixWord ++ tailWord_1452605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452605).length < 2 ^ (prefixWord ++ tailWord_1452605).sum := by decide
  have hdescent : baseEnd_1452605 < baseStart_1452605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452622 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_1452622 : Nat := 118140960795 + 1452622 * 2 ^ 59
def prefixEnd_1452622 : Nat := 4983230072969 + 3 ^ 40 * 1452622 * 2
def baseEnd_1452622 : Nat := 82877032810613427049391

theorem tailTrace_1452622 : CollatzResearch.WordTrace tailWord_1452622 prefixEnd_1452622 82877032810613427049391 := by
  unfold tailWord_1452622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622684617925757116426015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35320984628937371287605413 6622684617925757116426015)
  ·
    refine ⟨9934026926888635674639023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622684617925757116426015 9934026926888635674639023)
    ·
      refine ⟨14901040390332953511958535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9934026926888635674639023 14901040390332953511958535)
      ·
        refine ⟨22351560585499430267937803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14901040390332953511958535 22351560585499430267937803)
        ·
          refine ⟨33527340878249145401906705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22351560585499430267937803 33527340878249145401906705)
          ·
            refine ⟨25145505658686859051430029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33527340878249145401906705 25145505658686859051430029)
            ·
              refine ⟨9429564622007572144286261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25145505658686859051430029 9429564622007572144286261)
              ·
                refine ⟨884021683313209888526837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9429564622007572144286261 884021683313209888526837)
                ·
                  refine ⟨82877032810613427049391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884021683313209888526837 82877032810613427049391)
                  ·
                    rfl

theorem cell23_1452622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_1452622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452622 prefixEnd_1452622 := by exact prefixLift 1452622
  have htrace : WordTrace (prefixWord ++ tailWord_1452622) baseStart_1452622 baseEnd_1452622 := by
    simpa [prefixWord, tailWord_1452622, baseEnd_1452622] using wordTrace_append hprefix tailTrace_1452622
  have hstable : (prefixWord ++ tailWord_1452622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452622).length < 2 ^ (prefixWord ++ tailWord_1452622).sum := by decide
  have hdescent : baseEnd_1452622 < baseStart_1452622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452655 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_1452655 : Nat := 118140960795 + 1452655 * 2 ^ 59
def prefixEnd_1452655 : Nat := 4983230072969 + 3 ^ 40 * 1452655 * 2
def baseEnd_1452655 : Nat := 745910240157119214331867

theorem tailTrace_1452655 : CollatzResearch.WordTrace tailWord_1452655 prefixEnd_1452655 745910240157119214331867 := by
  unfold tailWord_1452655
  simp only [CollatzResearch.WordTrace]
  refine ⟨52982680552286503567359419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35321787034857669044906279 52982680552286503567359419)
  ·
    refine ⟨79474020828429755351039129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52982680552286503567359419 79474020828429755351039129)
    ·
      refine ⟨59605515621322316513279347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79474020828429755351039129 59605515621322316513279347)
      ·
        refine ⟨89408273431983474769919021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59605515621322316513279347 89408273431983474769919021)
        ·
          refine ⟨33528102536993803038719633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89408273431983474769919021 33528102536993803038719633)
          ·
            refine ⟨25146076902745352279039725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33528102536993803038719633 25146076902745352279039725)
            ·
              refine ⟨9429778838529507104639897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25146076902745352279039725 9429778838529507104639897)
              ·
                refine ⟨7072334128897130328479923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9429778838529507104639897 7072334128897130328479923)
                ·
                  refine ⟨10608501193345695492719885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7072334128897130328479923 10608501193345695492719885)
                  ·
                    refine ⟨3978187947504635809769957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10608501193345695492719885 3978187947504635809769957)
                    ·
                      refine ⟨745910240157119214331867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3978187947504635809769957 745910240157119214331867)
                      ·
                        rfl

theorem cell23_1452655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_1452655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452655 prefixEnd_1452655 := by exact prefixLift 1452655
  have htrace : WordTrace (prefixWord ++ tailWord_1452655) baseStart_1452655 baseEnd_1452655 := by
    simpa [prefixWord, tailWord_1452655, baseEnd_1452655] using wordTrace_append hprefix tailTrace_1452655
  have hstable : (prefixWord ++ tailWord_1452655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452655).length < 2 ^ (prefixWord ++ tailWord_1452655).sum := by decide
  have hdescent : baseEnd_1452655 < baseStart_1452655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452695 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 8]
def baseStart_1452695 : Nat := 118140960795 + 1452695 * 2 ^ 59
def prefixEnd_1452695 : Nat := 4983230072969 + 3 ^ 40 * 1452695 * 2
def baseEnd_1452695 : Nat := 82881197709255450870187

theorem tailTrace_1452695 : CollatzResearch.WordTrace tailWord_1452695 prefixEnd_1452695 82881197709255450870187 := by
  unfold tailWord_1452695
  simp only [CollatzResearch.WordTrace]
  refine ⟨52984139472141590398815539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35322759648094393599210359 52984139472141590398815539)
  ·
    refine ⟨79476209208212385598223309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52984139472141590398815539 79476209208212385598223309)
    ·
      refine ⟨29803578453079644599333741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79476209208212385598223309 29803578453079644599333741)
      ·
        refine ⟨11176341919904866724750153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29803578453079644599333741 11176341919904866724750153)
        ·
          refine ⟨8382256439928650043562615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11176341919904866724750153 8382256439928650043562615)
          ·
            refine ⟨12573384659892975065343923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382256439928650043562615 12573384659892975065343923)
            ·
              refine ⟨18860076989839462598015885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12573384659892975065343923 18860076989839462598015885)
              ·
                refine ⟨7072528871189798474255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18860076989839462598015885 7072528871189798474255957)
                ·
                  refine ⟨82881197709255450870187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7072528871189798474255957 82881197709255450870187)
                  ·
                    rfl

theorem cell23_1452695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 8].length) (baseStart_1452695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452695 prefixEnd_1452695 := by exact prefixLift 1452695
  have htrace : WordTrace (prefixWord ++ tailWord_1452695) baseStart_1452695 baseEnd_1452695 := by
    simpa [prefixWord, tailWord_1452695, baseEnd_1452695] using wordTrace_append hprefix tailTrace_1452695
  have hstable : (prefixWord ++ tailWord_1452695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452695).length < 2 ^ (prefixWord ++ tailWord_1452695).sum := by decide
  have hdescent : baseEnd_1452695 < baseStart_1452695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452762 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1452762 : Nat := 118140960795 + 1452762 * 2 ^ 59
def prefixEnd_1452762 : Nat := 4983230072969 + 3 ^ 40 * 1452762 * 2
def baseEnd_1452762 : Nat := 745965182587150295693875

theorem tailTrace_1452762 : CollatzResearch.WordTrace tailWord_1452762 prefixEnd_1452762 745965182587150295693875 := by
  unfold tailWord_1452762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246645790724715210376135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35324388775265907227669693 13246645790724715210376135)
  ·
    refine ⟨19869968686087072815564203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13246645790724715210376135 19869968686087072815564203)
    ·
      refine ⟨29804953029130609223346305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19869968686087072815564203 29804953029130609223346305)
      ·
        refine ⟨22353714771847956917509729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29804953029130609223346305 22353714771847956917509729)
        ·
          refine ⟨16765286078885967688132297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22353714771847956917509729 16765286078885967688132297)
          ·
            refine ⟨12573964559164475766099223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16765286078885967688132297 12573964559164475766099223)
            ·
              refine ⟨18860946838746713649148835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12573964559164475766099223 18860946838746713649148835)
              ·
                refine ⟨28291420258120070473723253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18860946838746713649148835 28291420258120070473723253)
                ·
                  refine ⟨2652320649198756606911555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28291420258120070473723253 2652320649198756606911555)
                  ·
                    refine ⟨3978480973798134910367333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652320649198756606911555 3978480973798134910367333)
                    ·
                      refine ⟨745965182587150295693875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3978480973798134910367333 745965182587150295693875)
                      ·
                        rfl

theorem cell23_1452762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1452762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452762 prefixEnd_1452762 := by exact prefixLift 1452762
  have htrace : WordTrace (prefixWord ++ tailWord_1452762) baseStart_1452762 baseEnd_1452762 := by
    simpa [prefixWord, tailWord_1452762, baseEnd_1452762] using wordTrace_append hprefix tailTrace_1452762
  have hstable : (prefixWord ++ tailWord_1452762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452762).length < 2 ^ (prefixWord ++ tailWord_1452762).sum := by decide
  have hdescent : baseEnd_1452762 < baseStart_1452762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452772 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1452772 : Nat := 118140960795 + 1452772 * 2 ^ 59
def prefixEnd_1452772 : Nat := 4983230072969 + 3 ^ 40 * 1452772 * 2
def baseEnd_1452772 : Nat := 248656772464565085522943

theorem tailTrace_1452772 : CollatzResearch.WordTrace tailWord_1452772 prefixEnd_1452772 248656772464565085522943 := by
  unfold tailWord_1452772
  simp only [CollatzResearch.WordTrace]
  refine ⟨26493473946431316274684285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35324631928575088366245713 26493473946431316274684285)
  ·
    refine ⟨9935052729911743603006607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26493473946431316274684285 9935052729911743603006607)
    ·
      refine ⟨14902579094867615404509911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935052729911743603006607 14902579094867615404509911)
      ·
        refine ⟨22353868642301423106764867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902579094867615404509911 22353868642301423106764867)
        ·
          refine ⟨33530802963452134660147301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22353868642301423106764867 33530802963452134660147301)
          ·
            refine ⟨6287025555647275248777619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33530802963452134660147301 6287025555647275248777619)
            ·
              refine ⟨9430538333470912873166429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287025555647275248777619 9430538333470912873166429)
              ·
                refine ⟨3536451875051592327437411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9430538333470912873166429 3536451875051592327437411)
                ·
                  refine ⟨5304677812577388491156117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536451875051592327437411 5304677812577388491156117)
                  ·
                    refine ⟨248656772464565085522943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5304677812577388491156117 248656772464565085522943)
                    ·
                      rfl

theorem cell23_1452772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1452772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452772 prefixEnd_1452772 := by exact prefixLift 1452772
  have htrace : WordTrace (prefixWord ++ tailWord_1452772) baseStart_1452772 baseEnd_1452772 := by
    simpa [prefixWord, tailWord_1452772, baseEnd_1452772] using wordTrace_append hprefix tailTrace_1452772
  have hstable : (prefixWord ++ tailWord_1452772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452772).length < 2 ^ (prefixWord ++ tailWord_1452772).sum := by decide
  have hdescent : baseEnd_1452772 < baseStart_1452772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452792 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1452792 : Nat := 118140960795 + 1452792 * 2 ^ 59
def prefixEnd_1452792 : Nat := 4983230072969 + 3 ^ 40 * 1452792 * 2
def baseEnd_1452792 : Nat := 745980587006785178318737

theorem tailTrace_1452792 : CollatzResearch.WordTrace tailWord_1452792 prefixEnd_1452792 745980587006785178318737 := by
  unfold tailWord_1452792
  simp only [CollatzResearch.WordTrace]
  refine ⟨26493838676395087982548315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35325118235193450643397753 26493838676395087982548315)
  ·
    refine ⟨39740758014592631973822473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26493838676395087982548315 39740758014592631973822473)
    ·
      refine ⟨29805568510944473980366855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39740758014592631973822473 29805568510944473980366855)
      ·
        refine ⟨44708352766416710970550283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29805568510944473980366855 44708352766416710970550283)
        ·
          refine ⟨67062529149625066455825425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44708352766416710970550283 67062529149625066455825425)
          ·
            refine ⟨50296896862218799841869069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67062529149625066455825425 50296896862218799841869069)
            ·
              refine ⟨18861336323332049940700901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50296896862218799841869069 18861336323332049940700901)
              ·
                refine ⟨3536500560624759363881419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18861336323332049940700901 3536500560624759363881419)
                ·
                  refine ⟨5304750840937139045822129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536500560624759363881419 5304750840937139045822129)
                  ·
                    refine ⟨3978563130702854284366597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5304750840937139045822129 3978563130702854284366597)
                    ·
                      refine ⟨745980587006785178318737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3978563130702854284366597 745980587006785178318737)
                      ·
                        rfl

theorem cell23_1452792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1452792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452792 prefixEnd_1452792 := by exact prefixLift 1452792
  have htrace : WordTrace (prefixWord ++ tailWord_1452792) baseStart_1452792 baseEnd_1452792 := by
    simpa [prefixWord, tailWord_1452792, baseEnd_1452792] using wordTrace_append hprefix tailTrace_1452792
  have hstable : (prefixWord ++ tailWord_1452792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452792).length < 2 ^ (prefixWord ++ tailWord_1452792).sum := by decide
  have hdescent : baseEnd_1452792 < baseStart_1452792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452795 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7]
def baseStart_1452795 : Nat := 118140960795 + 1452795 * 2 ^ 59
def prefixEnd_1452795 : Nat := 4983230072969 + 3 ^ 40 * 1452795 * 2
def baseEnd_1452795 : Nat := 745982127448748666581223

theorem tailTrace_1452795 : CollatzResearch.WordTrace tailWord_1452795 prefixEnd_1452795 745982127448748666581223 := by
  unfold tailWord_1452795
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987786771779307477455839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35325191181186204984970559 52987786771779307477455839)
  ·
    refine ⟨79481680157668961216183759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52987786771779307477455839 79481680157668961216183759)
    ·
      refine ⟨119222520236503441824275639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79481680157668961216183759 119222520236503441824275639)
      ·
        refine ⟨178833780354755162736413459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119222520236503441824275639 178833780354755162736413459)
        ·
          refine ⟨268250670532132744104620189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178833780354755162736413459 268250670532132744104620189)
          ·
            refine ⟨100594001449549779039232571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268250670532132744104620189 100594001449549779039232571)
            ·
              refine ⟨150891002174324668558848857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100594001449549779039232571 150891002174324668558848857)
              ·
                refine ⟨113168251630743501419136643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150891002174324668558848857 113168251630743501419136643)
                ·
                  refine ⟨169752377446115252128704965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113168251630743501419136643 169752377446115252128704965)
                  ·
                    refine ⟨31828570771146609774132181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169752377446115252128704965 31828570771146609774132181)
                    ·
                      refine ⟨745982127448748666581223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31828570771146609774132181 745982127448748666581223)
                      ·
                        rfl

theorem cell23_1452795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_1452795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452795 prefixEnd_1452795 := by exact prefixLift 1452795
  have htrace : WordTrace (prefixWord ++ tailWord_1452795) baseStart_1452795 baseEnd_1452795 := by
    simpa [prefixWord, tailWord_1452795, baseEnd_1452795] using wordTrace_append hprefix tailTrace_1452795
  have hstable : (prefixWord ++ tailWord_1452795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452795).length < 2 ^ (prefixWord ++ tailWord_1452795).sum := by decide
  have hdescent : baseEnd_1452795 < baseStart_1452795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452796 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_1452796 : Nat := 118140960795 + 1452796 * 2 ^ 59
def prefixEnd_1452796 : Nat := 4983230072969 + 3 ^ 40 * 1452796 * 2
def baseEnd_1452796 : Nat := 745982640929403162668719

theorem tailTrace_1452796 : CollatzResearch.WordTrace tailWord_1452796 prefixEnd_1452796 745982640929403162668719 := by
  unfold tailWord_1452796
  simp only [CollatzResearch.WordTrace]
  refine ⟨26493911622387842324121121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35325215496517123098828161 26493911622387842324121121)
  ·
    refine ⟨19870433716790881743090841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26493911622387842324121121 19870433716790881743090841)
    ·
      refine ⟨14902825287593161307318131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19870433716790881743090841 14902825287593161307318131)
      ·
        refine ⟨22354237931389741960977197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902825287593161307318131 22354237931389741960977197)
        ·
          refine ⟨8382839224271153235366449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22354237931389741960977197 8382839224271153235366449)
          ·
            refine ⟨6287129418203364926524837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382839224271153235366449 6287129418203364926524837)
            ·
              refine ⟨1178836765913130923723407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6287129418203364926524837 1178836765913130923723407)
              ·
                refine ⟨1768255148869696385585111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178836765913130923723407 1768255148869696385585111)
                ·
                  refine ⟨2652382723304544578377667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768255148869696385585111 2652382723304544578377667)
                  ·
                    refine ⟨3978574084956816867566501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2652382723304544578377667 3978574084956816867566501)
                    ·
                      refine ⟨745982640929403162668719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3978574084956816867566501 745982640929403162668719)
                      ·
                        rfl

theorem cell23_1452796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_1452796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452796 prefixEnd_1452796 := by exact prefixLift 1452796
  have htrace : WordTrace (prefixWord ++ tailWord_1452796) baseStart_1452796 baseEnd_1452796 := by
    simpa [prefixWord, tailWord_1452796, baseEnd_1452796] using wordTrace_append hprefix tailTrace_1452796
  have hstable : (prefixWord ++ tailWord_1452796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452796).length < 2 ^ (prefixWord ++ tailWord_1452796).sum := by decide
  have hdescent : baseEnd_1452796 < baseStart_1452796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452823 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 2, 4]
def baseStart_1452823 : Nat := 118140960795 + 1452823 * 2 ^ 59
def prefixEnd_1452823 : Nat := 4983230072969 + 3 ^ 40 * 1452823 * 2
def baseEnd_1452823 : Nat := 248665501635691519010365

theorem tailTrace_1452823 : CollatzResearch.WordTrace tailWord_1452823 prefixEnd_1452823 248665501635691519010365 := by
  unfold tailWord_1452823
  simp only [CollatzResearch.WordTrace]
  refine ⟨52988808015677868259475123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35325872010451912172983415 52988808015677868259475123)
  ·
    refine ⟨79483212023516802389212685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52988808015677868259475123 79483212023516802389212685)
    ·
      refine ⟨29806204508818800895954757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79483212023516802389212685 29806204508818800895954757)
      ·
        refine ⟨5588663345403525167991517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29806204508818800895954757 5588663345403525167991517)
        ·
          refine ⟨2095748754526321937996819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588663345403525167991517 2095748754526321937996819)
          ·
            refine ⟨3143623131789482906995229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095748754526321937996819 3143623131789482906995229)
            ·
              refine ⟨1178858674421056090123211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143623131789482906995229 1178858674421056090123211)
              ·
                refine ⟨1768288011631584135184817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178858674421056090123211 1768288011631584135184817)
                ·
                  refine ⟨1326216008723688101388613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768288011631584135184817 1326216008723688101388613)
                  ·
                    refine ⟨248665501635691519010365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326216008723688101388613 248665501635691519010365)
                    ·
                      rfl

theorem cell23_1452823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_1452823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452823 prefixEnd_1452823 := by exact prefixLift 1452823
  have htrace : WordTrace (prefixWord ++ tailWord_1452823) baseStart_1452823 baseEnd_1452823 := by
    simpa [prefixWord, tailWord_1452823, baseEnd_1452823] using wordTrace_append hprefix tailTrace_1452823
  have hstable : (prefixWord ++ tailWord_1452823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452823).length < 2 ^ (prefixWord ++ tailWord_1452823).sum := by decide
  have hdescent : baseEnd_1452823 < baseStart_1452823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452836 : List Nat := [2, 3, 1, 3, 3, 2, 2, 7]
def baseStart_1452836 : Nat := 118140960795 + 1452836 * 2 ^ 59
def prefixEnd_1452836 : Nat := 4983230072969 + 3 ^ 40 * 1452836 * 2
def baseEnd_1452836 : Nat := 27629747413169740969205

theorem tailTrace_1452836 : CollatzResearch.WordTrace tailWord_1452836 prefixEnd_1452836 27629747413169740969205 := by
  unfold tailWord_1452836
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494641082315385739849181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35326188109753847653132241 26494641082315385739849181)
  ·
    refine ⟨9935490405868269652443443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26494641082315385739849181 9935490405868269652443443)
    ·
      refine ⟨14903235608802404478665165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935490405868269652443443 14903235608802404478665165)
      ·
        refine ⟨5588713353300901679499437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14903235608802404478665165 5588713353300901679499437)
        ·
          refine ⟨2095767507487838129812289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588713353300901679499437 2095767507487838129812289)
          ·
            refine ⟨1571825630615878597359217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095767507487838129812289 1571825630615878597359217)
            ·
              refine ⟨1178869222961908948019413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571825630615878597359217 1178869222961908948019413)
              ·
                refine ⟨27629747413169740969205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1178869222961908948019413 27629747413169740969205)
                ·
                  rfl

theorem cell23_1452836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 7].length) (baseStart_1452836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452836 prefixEnd_1452836 := by exact prefixLift 1452836
  have htrace : WordTrace (prefixWord ++ tailWord_1452836) baseStart_1452836 baseEnd_1452836 := by
    simpa [prefixWord, tailWord_1452836, baseEnd_1452836] using wordTrace_append hprefix tailTrace_1452836
  have hstable : (prefixWord ++ tailWord_1452836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452836).length < 2 ^ (prefixWord ++ tailWord_1452836).sum := by decide
  have hdescent : baseEnd_1452836 < baseStart_1452836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452856 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_1452856 : Nat := 118140960795 + 1452856 * 2 ^ 59
def prefixEnd_1452856 : Nat := 4983230072969 + 3 ^ 40 * 1452856 * 2
def baseEnd_1452856 : Nat := 746013449768672927918443

theorem tailTrace_1452856 : CollatzResearch.WordTrace tailWord_1452856 prefixEnd_1452856 746013449768672927918443 := by
  unfold tailWord_1452856
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495005812279157447713211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35326674416372209930284281 26495005812279157447713211)
  ·
    refine ⟨39742508718418736171569817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26495005812279157447713211 39742508718418736171569817)
    ·
      refine ⟨29806881538814052128677363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39742508718418736171569817 29806881538814052128677363)
      ·
        refine ⟨44710322308221078193016045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29806881538814052128677363 44710322308221078193016045)
        ·
          refine ⟨16766370865582904322381017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44710322308221078193016045 16766370865582904322381017)
          ·
            refine ⟨12574778149187178241785763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16766370865582904322381017 12574778149187178241785763)
            ·
              refine ⟨18862167223780767362678645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12574778149187178241785763 18862167223780767362678645)
              ·
                refine ⟨1768328177229446940251123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18862167223780767362678645 1768328177229446940251123)
                ·
                  refine ⟨2652492265844170410376685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768328177229446940251123 2652492265844170410376685)
                  ·
                    refine ⟨994684599691563903891257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652492265844170410376685 994684599691563903891257)
                    ·
                      refine ⟨746013449768672927918443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994684599691563903891257 746013449768672927918443)
                      ·
                        rfl

theorem cell23_1452856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_1452856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452856 prefixEnd_1452856 := by exact prefixLift 1452856
  have htrace : WordTrace (prefixWord ++ tailWord_1452856) baseStart_1452856 baseEnd_1452856 := by
    simpa [prefixWord, tailWord_1452856, baseEnd_1452856] using wordTrace_append hprefix tailTrace_1452856
  have hstable : (prefixWord ++ tailWord_1452856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452856).length < 2 ^ (prefixWord ++ tailWord_1452856).sum := by decide
  have hdescent : baseEnd_1452856 < baseStart_1452856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452869 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_1452869 : Nat := 118140960795 + 1452869 * 2 ^ 59
def prefixEnd_1452869 : Nat := 4983230072969 + 3 ^ 40 * 1452869 * 2
def baseEnd_1452869 : Nat := 746020125017181377055883

theorem tailTrace_1452869 : CollatzResearch.WordTrace tailWord_1452869 prefixEnd_1452869 746020125017181377055883 := by
  unfold tailWord_1452869
  simp only [CollatzResearch.WordTrace]
  refine ⟨52990485773511218115649661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35326990515674145410433107 52990485773511218115649661)
  ·
    refine ⟨19871432165066706793368623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52990485773511218115649661 19871432165066706793368623)
    ·
      refine ⟨29807148247600060190052935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19871432165066706793368623 29807148247600060190052935)
      ·
        refine ⟨44710722371400090285079403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29807148247600060190052935 44710722371400090285079403)
        ·
          refine ⟨67066083557100135427619105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44710722371400090285079403 67066083557100135427619105)
          ·
            refine ⟨50299562667825101570714329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67066083557100135427619105 50299562667825101570714329)
            ·
              refine ⟨37724672000868826178035747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50299562667825101570714329 37724672000868826178035747)
              ·
                refine ⟨56587008001303239267053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37724672000868826178035747 56587008001303239267053621)
                ·
                  refine ⟨5305032000122178681286277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56587008001303239267053621 5305032000122178681286277)
                  ·
                    refine ⟨994693500022908502741177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5305032000122178681286277 994693500022908502741177)
                    ·
                      refine ⟨746020125017181377055883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994693500022908502741177 746020125017181377055883)
                      ·
                        rfl

theorem cell23_1452869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_1452869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452869 prefixEnd_1452869 := by exact prefixLift 1452869
  have htrace : WordTrace (prefixWord ++ tailWord_1452869) baseStart_1452869 baseEnd_1452869 := by
    simpa [prefixWord, tailWord_1452869, baseEnd_1452869] using wordTrace_append hprefix tailTrace_1452869
  have hstable : (prefixWord ++ tailWord_1452869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452869).length < 2 ^ (prefixWord ++ tailWord_1452869).sum := by decide
  have hdescent : baseEnd_1452869 < baseStart_1452869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452872 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1452872 : Nat := 118140960795 + 1452872 * 2 ^ 59
def prefixEnd_1452872 : Nat := 4983230072969 + 3 ^ 40 * 1452872 * 2
def baseEnd_1452872 : Nat := 746021665459144865318369

theorem tailTrace_1452872 : CollatzResearch.WordTrace tailWord_1452872 prefixEnd_1452872 746021665459144865318369 := by
  unfold tailWord_1452872
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495297596250174814004435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35327063461666899752005913 26495297596250174814004435)
  ·
    refine ⟨39742946394375262221006653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26495297596250174814004435 39742946394375262221006653)
    ·
      refine ⟨14903604897890723332877495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39742946394375262221006653 14903604897890723332877495)
      ·
        refine ⟨22355407346836084999316243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14903604897890723332877495 22355407346836084999316243)
        ·
          refine ⟨33533111020254127498974365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22355407346836084999316243 33533111020254127498974365)
          ·
            refine ⟨12574916632595297812115387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33533111020254127498974365 12574916632595297812115387)
            ·
              refine ⟨18862374948892946718173081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12574916632595297812115387 18862374948892946718173081)
              ·
                refine ⟨14146781211669710038629811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18862374948892946718173081 14146781211669710038629811)
                ·
                  refine ⟨21220171817504565057944717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14146781211669710038629811 21220171817504565057944717)
                  ·
                    refine ⟨7957564431564211896729269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21220171817504565057944717 7957564431564211896729269)
                    ·
                      refine ⟨746021665459144865318369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7957564431564211896729269 746021665459144865318369)
                      ·
                        rfl

theorem cell23_1452872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1452872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452872 prefixEnd_1452872 := by exact prefixLift 1452872
  have htrace : WordTrace (prefixWord ++ tailWord_1452872) baseStart_1452872 baseEnd_1452872 := by
    simpa [prefixWord, tailWord_1452872, baseEnd_1452872] using wordTrace_append hprefix tailTrace_1452872
  have hstable : (prefixWord ++ tailWord_1452872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452872).length < 2 ^ (prefixWord ++ tailWord_1452872).sum := by decide
  have hdescent : baseEnd_1452872 < baseStart_1452872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452922 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_1452922 : Nat := 118140960795 + 1452922 * 2 ^ 59
def prefixEnd_1452922 : Nat := 4983230072969 + 3 ^ 40 * 1452922 * 2
def baseEnd_1452922 : Nat := 248682446497289889897713

theorem tailTrace_1452922 : CollatzResearch.WordTrace tailWord_1452922 prefixEnd_1452922 248682446497289889897713 := by
  unfold tailWord_1452922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248104710579802041832255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35328279228212805444886013 13248104710579802041832255)
  ·
    refine ⟨19872157065869703062748383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13248104710579802041832255 19872157065869703062748383)
    ·
      refine ⟨29808235598804554594122575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19872157065869703062748383 29808235598804554594122575)
      ·
        refine ⟨44712353398206831891183863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29808235598804554594122575 44712353398206831891183863)
        ·
          refine ⟨67068530097310247836775795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44712353398206831891183863 67068530097310247836775795)
          ·
            refine ⟨100602795145965371755163693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67068530097310247836775795 100602795145965371755163693)
            ·
              refine ⟨37726048179737014408186385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100602795145965371755163693 37726048179737014408186385)
              ·
                refine ⟨28294536134802760806139789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37726048179737014408186385 28294536134802760806139789)
                ·
                  refine ⟨10610451050551035302302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28294536134802760806139789 10610451050551035302302421)
                  ·
                    refine ⟨248682446497289889897713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10610451050551035302302421 248682446497289889897713)
                    ·
                      rfl

theorem cell23_1452922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_1452922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452922 prefixEnd_1452922 := by exact prefixLift 1452922
  have htrace : WordTrace (prefixWord ++ tailWord_1452922) baseStart_1452922 baseEnd_1452922 := by
    simpa [prefixWord, tailWord_1452922, baseEnd_1452922] using wordTrace_append hprefix tailTrace_1452922
  have hstable : (prefixWord ++ tailWord_1452922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452922).length < 2 ^ (prefixWord ++ tailWord_1452922).sum := by decide
  have hdescent : baseEnd_1452922 < baseStart_1452922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452936 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1452936 : Nat := 118140960795 + 1452936 * 2 ^ 59
def prefixEnd_1452936 : Nat := 4983230072969 + 3 ^ 40 * 1452936 * 2
def baseEnd_1452936 : Nat := 746054528221032614918075

theorem tailTrace_1452936 : CollatzResearch.WordTrace tailWord_1452936 prefixEnd_1452936 746054528221032614918075 := by
  unfold tailWord_1452936
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496464732134244279169331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35328619642845659038892441 26496464732134244279169331)
  ·
    refine ⟨39744697098201366418753997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26496464732134244279169331 39744697098201366418753997)
    ·
      refine ⟨14904261411825512407032749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39744697098201366418753997 14904261411825512407032749)
      ·
        refine ⟨5589098029434567152637281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14904261411825512407032749 5589098029434567152637281)
        ·
          refine ⟨4191823522075925364477961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5589098029434567152637281 4191823522075925364477961)
          ·
            refine ⟨3143867641556944023358471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191823522075925364477961 3143867641556944023358471)
            ·
              refine ⟨4715801462335416035037707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143867641556944023358471 4715801462335416035037707)
              ·
                refine ⟨7073702193503124052556561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715801462335416035037707 7073702193503124052556561)
                ·
                  refine ⟨5305276645127343039417421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7073702193503124052556561 5305276645127343039417421)
                  ·
                    refine ⟨1989478741922753639781533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5305276645127343039417421 1989478741922753639781533)
                    ·
                      refine ⟨746054528221032614918075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1989478741922753639781533 746054528221032614918075)
                      ·
                        rfl

theorem cell23_1452936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1452936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452936 prefixEnd_1452936 := by exact prefixLift 1452936
  have htrace : WordTrace (prefixWord ++ tailWord_1452936) baseStart_1452936 baseEnd_1452936 := by
    simpa [prefixWord, tailWord_1452936, baseEnd_1452936] using wordTrace_append hprefix tailTrace_1452936
  have hstable : (prefixWord ++ tailWord_1452936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452936).length < 2 ^ (prefixWord ++ tailWord_1452936).sum := by decide
  have hdescent : baseEnd_1452936 < baseStart_1452936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452956 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1452956 : Nat := 118140960795 + 1452956 * 2 ^ 59
def prefixEnd_1452956 : Nat := 4983230072969 + 3 ^ 40 * 1452956 * 2
def baseEnd_1452956 : Nat := 248688265944707512222661

theorem tailTrace_1452956 : CollatzResearch.WordTrace tailWord_1452956 prefixEnd_1452956 248688265944707512222661 := by
  unfold tailWord_1452956
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496829462098015987033361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35329105949464021316044481 26496829462098015987033361)
  ·
    refine ⟨19872622096573511990275021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26496829462098015987033361 19872622096573511990275021)
    ·
      refine ⟨7452233286215066996353133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19872622096573511990275021 7452233286215066996353133)
      ·
        refine ⟨2794587482330650123632425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7452233286215066996353133 2794587482330650123632425)
        ·
          refine ⟨2095940611747987592724319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794587482330650123632425 2095940611747987592724319)
          ·
            refine ⟨3143910917621981389086479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095940611747987592724319 3143910917621981389086479)
            ·
              refine ⟨4715866376432972083629719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143910917621981389086479 4715866376432972083629719)
              ·
                refine ⟨7073799564649458125444579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715866376432972083629719 7073799564649458125444579)
                ·
                  refine ⟨10610699346974187188166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073799564649458125444579 10610699346974187188166869)
                  ·
                    refine ⟨248688265944707512222661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10610699346974187188166869 248688265944707512222661)
                    ·
                      rfl

theorem cell23_1452956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1452956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452956 prefixEnd_1452956 := by exact prefixLift 1452956
  have htrace : WordTrace (prefixWord ++ tailWord_1452956) baseStart_1452956 baseEnd_1452956 := by
    simpa [prefixWord, tailWord_1452956, baseEnd_1452956] using wordTrace_append hprefix tailTrace_1452956
  have hstable : (prefixWord ++ tailWord_1452956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452956).length < 2 ^ (prefixWord ++ tailWord_1452956).sum := by decide
  have hdescent : baseEnd_1452956 < baseStart_1452956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452969 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 5, 4]
def baseStart_1452969 : Nat := 118140960795 + 1452969 * 2 ^ 59
def prefixEnd_1452969 : Nat := 4983230072969 + 3 ^ 40 * 1452969 * 2
def baseEnd_1452969 : Nat := 248690491027543661935141

theorem tailTrace_1452969 : CollatzResearch.WordTrace tailWord_1452969 prefixEnd_1452969 248690491027543661935141 := by
  unfold tailWord_1452969
  simp only [CollatzResearch.WordTrace]
  refine ⟨52994133073148935194289961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35329422048765956796193307 52994133073148935194289961)
  ·
    refine ⟨39745599804861701395717471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52994133073148935194289961 39745599804861701395717471)
    ·
      refine ⟨59618399707292552093576207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39745599804861701395717471 59618399707292552093576207)
      ·
        refine ⟨89427599560938828140364311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59618399707292552093576207 89427599560938828140364311)
        ·
          refine ⟨134141399341408242210546467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89427599560938828140364311 134141399341408242210546467)
          ·
            refine ⟨201212099012112363315819701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134141399341408242210546467 201212099012112363315819701)
            ·
              refine ⟨18863634282385534060858097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201212099012112363315819701 18863634282385534060858097)
              ·
                refine ⟨14147725711789150545643573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18863634282385534060858097 14147725711789150545643573)
                ·
                  refine ⟨1326349285480232863654085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14147725711789150545643573 1326349285480232863654085)
                  ·
                    refine ⟨248690491027543661935141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326349285480232863654085 248690491027543661935141)
                    ·
                      rfl

theorem cell23_1452969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 4].length) (baseStart_1452969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452969 prefixEnd_1452969 := by exact prefixLift 1452969
  have htrace : WordTrace (prefixWord ++ tailWord_1452969) baseStart_1452969 baseEnd_1452969 := by
    simpa [prefixWord, tailWord_1452969, baseEnd_1452969] using wordTrace_append hprefix tailTrace_1452969
  have hstable : (prefixWord ++ tailWord_1452969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452969).length < 2 ^ (prefixWord ++ tailWord_1452969).sum := by decide
  have hdescent : baseEnd_1452969 < baseStart_1452969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452986 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_1452986 : Nat := 118140960795 + 1452986 * 2 ^ 59
def prefixEnd_1452986 : Nat := 4983230072969 + 3 ^ 40 * 1452986 * 2
def baseEnd_1452986 : Nat := 248693400751252473097615

theorem tailTrace_1452986 : CollatzResearch.WordTrace tailWord_1452986 prefixEnd_1452986 248693400751252473097615 := by
  unfold tailWord_1452986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13248688278521836774414703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35329835409391564731772541 13248688278521836774414703)
  ·
    refine ⟨19873032417782755161622055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13248688278521836774414703 19873032417782755161622055)
    ·
      refine ⟨29809548626674132742433083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19873032417782755161622055 29809548626674132742433083)
      ·
        refine ⟨44714322940011199113649625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29809548626674132742433083 44714322940011199113649625)
        ·
          refine ⟨33535742205008399335237219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44714322940011199113649625 33535742205008399335237219)
          ·
            refine ⟨50303613307512599002855829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33535742205008399335237219 50303613307512599002855829)
            ·
              refine ⟨2357981873789653078258867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50303613307512599002855829 2357981873789653078258867)
              ·
                refine ⟨3536972810684479617388301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357981873789653078258867 3536972810684479617388301)
                ·
                  refine ⟨1326364804006679856520613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3536972810684479617388301 1326364804006679856520613)
                  ·
                    refine ⟨248693400751252473097615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326364804006679856520613 248693400751252473097615)
                    ·
                      rfl

theorem cell23_1452986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_1452986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452986 prefixEnd_1452986 := by exact prefixLift 1452986
  have htrace : WordTrace (prefixWord ++ tailWord_1452986) baseStart_1452986 baseEnd_1452986 := by
    simpa [prefixWord, tailWord_1452986, baseEnd_1452986] using wordTrace_append hprefix tailTrace_1452986
  have hstable : (prefixWord ++ tailWord_1452986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452986).length < 2 ^ (prefixWord ++ tailWord_1452986).sum := by decide
  have hdescent : baseEnd_1452986 < baseStart_1452986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452999 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 6]
def baseStart_1452999 : Nat := 118140960795 + 1452999 * 2 ^ 59
def prefixEnd_1452999 : Nat := 4983230072969 + 3 ^ 40 * 1452999 * 2
def baseEnd_1452999 : Nat := 82898541944696207603365

theorem tailTrace_1452999 : CollatzResearch.WordTrace tailWord_1452999 prefixEnd_1452999 82898541944696207603365 := by
  unfold tailWord_1452999
  simp only [CollatzResearch.WordTrace]
  refine ⟨52995227263040250317882051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35330151508693500211921367 52995227263040250317882051)
  ·
    refine ⟨79492840894560375476823077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52995227263040250317882051 79492840894560375476823077)
    ·
      refine ⟨14904907667730070401904327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79492840894560375476823077 14904907667730070401904327)
      ·
        refine ⟨22357361501595105602856491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14904907667730070401904327 22357361501595105602856491)
        ·
          refine ⟨33536042252392658404284737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22357361501595105602856491 33536042252392658404284737)
          ·
            refine ⟨25152031689294493803213553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33536042252392658404284737 25152031689294493803213553)
            ·
              refine ⟨18864023766970870352410165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25152031689294493803213553 18864023766970870352410165)
              ·
                refine ⟨1768502228153519095538453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18864023766970870352410165 1768502228153519095538453)
                ·
                  refine ⟨82898541944696207603365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1768502228153519095538453 82898541944696207603365)
                  ·
                    rfl

theorem cell23_1452999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 6].length) (baseStart_1452999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1452999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1452999 prefixEnd_1452999 := by exact prefixLift 1452999
  have htrace : WordTrace (prefixWord ++ tailWord_1452999) baseStart_1452999 baseEnd_1452999 := by
    simpa [prefixWord, tailWord_1452999, baseEnd_1452999] using wordTrace_append hprefix tailTrace_1452999
  have hstable : (prefixWord ++ tailWord_1452999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452999).length < 2 ^ (prefixWord ++ tailWord_1452999).sum := by decide
  have hdescent : baseEnd_1452999 < baseStart_1452999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453009 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_1453009 : Nat := 118140960795 + 1453009 * 2 ^ 59
def prefixEnd_1453009 : Nat := 4983230072969 + 3 ^ 40 * 1453009 * 2
def baseEnd_1453009 : Nat := 746092012308810829305239

theorem tailTrace_1453009 : CollatzResearch.WordTrace tailWord_1453009 prefixEnd_1453009 746092012308810829305239 := by
  unfold tailWord_1453009
  simp only [CollatzResearch.WordTrace]
  refine ⟨52995591993004022025746081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35330394662002681350497387 52995591993004022025746081)
  ·
    refine ⟨39746693994753016519309561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52995591993004022025746081 39746693994753016519309561)
    ·
      refine ⟨29810020496064762389482171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39746693994753016519309561 29810020496064762389482171)
      ·
        refine ⟨44715030744097143584223257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29810020496064762389482171 44715030744097143584223257)
        ·
          refine ⟨33536273058072857688167443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44715030744097143584223257 33536273058072857688167443)
          ·
            refine ⟨50304409587109286532251165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33536273058072857688167443 50304409587109286532251165)
            ·
              refine ⟨18864153595165982449594187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50304409587109286532251165 18864153595165982449594187)
              ·
                refine ⟨28296230392748973674391281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18864153595165982449594187 28296230392748973674391281)
                ·
                  refine ⟨21222172794561730255793461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28296230392748973674391281 21222172794561730255793461)
                  ·
                    refine ⟨1989578699490162211480637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21222172794561730255793461 1989578699490162211480637)
                    ·
                      refine ⟨746092012308810829305239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1989578699490162211480637 746092012308810829305239)
                      ·
                        rfl

theorem cell23_1453009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_1453009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453009 prefixEnd_1453009 := by exact prefixLift 1453009
  have htrace : WordTrace (prefixWord ++ tailWord_1453009) baseStart_1453009 baseEnd_1453009 := by
    simpa [prefixWord, tailWord_1453009, baseEnd_1453009] using wordTrace_append hprefix tailTrace_1453009
  have hstable : (prefixWord ++ tailWord_1453009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453009).length < 2 ^ (prefixWord ++ tailWord_1453009).sum := by decide
  have hdescent : baseEnd_1453009 < baseStart_1453009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453070 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1453070 : Nat := 118140960795 + 1453070 * 2 ^ 59
def prefixEnd_1453070 : Nat := 4983230072969 + 3 ^ 40 * 1453070 * 2
def baseEnd_1453070 : Nat := 746123334628735090642459

theorem tailTrace_1453070 : CollatzResearch.WordTrace tailWord_1453070 prefixEnd_1453070 746123334628735090642459 := by
  unfold tailWord_1453070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624727105722878680464583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35331877897188686295811109 6624727105722878680464583)
  ·
    refine ⟨9937090658584318020696875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624727105722878680464583 9937090658584318020696875)
    ·
      refine ⟨14905635987876477031045313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937090658584318020696875 14905635987876477031045313)
      ·
        refine ⟨11179226990907357773283985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14905635987876477031045313 11179226990907357773283985)
        ·
          refine ⟨8384420243180518329962989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11179226990907357773283985 8384420243180518329962989)
          ·
            refine ⟨3144157591192694373736121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8384420243180518329962989 3144157591192694373736121)
            ·
              refine ⟨2358118193394520780302091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144157591192694373736121 2358118193394520780302091)
              ·
                refine ⟨3537177290091781170453137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358118193394520780302091 3537177290091781170453137)
                ·
                  refine ⟨2652882967568835877839853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3537177290091781170453137 2652882967568835877839853)
                  ·
                    refine ⟨994831112838313454189945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2652882967568835877839853 994831112838313454189945)
                    ·
                      refine ⟨746123334628735090642459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994831112838313454189945 746123334628735090642459)
                      ·
                        rfl

theorem cell23_1453070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1453070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453070 prefixEnd_1453070 := by exact prefixLift 1453070
  have htrace : WordTrace (prefixWord ++ tailWord_1453070) baseStart_1453070 baseEnd_1453070 := by
    simpa [prefixWord, tailWord_1453070, baseEnd_1453070] using wordTrace_append hprefix tailTrace_1453070
  have hstable : (prefixWord ++ tailWord_1453070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453070).length < 2 ^ (prefixWord ++ tailWord_1453070).sum := by decide
  have hdescent : baseEnd_1453070 < baseStart_1453070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453089 : List Nat := [1, 2, 3, 2, 3, 12]
def baseStart_1453089 : Nat := 118140960795 + 1453089 * 2 ^ 59
def prefixEnd_1453089 : Nat := 4983230072969 + 3 ^ 40 * 1453089 * 2
def baseEnd_1453089 : Nat := 3070506546342265499197

theorem tailTrace_1453089 : CollatzResearch.WordTrace tailWord_1453089 prefixEnd_1453089 3070506546342265499197 := by
  unfold tailWord_1453089
  simp only [CollatzResearch.WordTrace]
  refine ⟨52998509832714195688658321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35332339888476130459105547 52998509832714195688658321)
  ·
    refine ⟨39748882374535646766493741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52998509832714195688658321 39748882374535646766493741)
    ·
      refine ⟨14905830890450867537435153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39748882374535646766493741 14905830890450867537435153)
      ·
        refine ⟨11179373167838150653076365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14905830890450867537435153 11179373167838150653076365)
        ·
          refine ⟨4192264937939306494903637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11179373167838150653076365 4192264937939306494903637)
          ·
            refine ⟨3070506546342265499197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4192264937939306494903637 3070506546342265499197)
            ·
              rfl

theorem cell23_1453089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 12].length) (baseStart_1453089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453089 prefixEnd_1453089 := by exact prefixLift 1453089
  have htrace : WordTrace (prefixWord ++ tailWord_1453089) baseStart_1453089 baseEnd_1453089 := by
    simpa [prefixWord, tailWord_1453089, baseEnd_1453089] using wordTrace_append hprefix tailTrace_1453089
  have hstable : (prefixWord ++ tailWord_1453089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453089).length < 2 ^ (prefixWord ++ tailWord_1453089).sum := by decide
  have hdescent : baseEnd_1453089 < baseStart_1453089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453093 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_1453093 : Nat := 118140960795 + 1453093 * 2 ^ 59
def prefixEnd_1453093 : Nat := 4983230072969 + 3 ^ 40 * 1453093 * 2
def baseEnd_1453093 : Nat := 248711714894596166884951

theorem tailTrace_1453093 : CollatzResearch.WordTrace tailWord_1453093 prefixEnd_1453093 248711714894596166884951 := by
  unfold tailWord_1453093
  simp only [CollatzResearch.WordTrace]
  refine ⟨52998655724699704371803933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35332437149799802914535955 52998655724699704371803933)
  ·
    refine ⟨19874495896762389139426475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52998655724699704371803933 19874495896762389139426475)
    ·
      refine ⟨29811743845143583709139713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19874495896762389139426475 29811743845143583709139713)
      ·
        refine ⟨22358807883857687781854785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29811743845143583709139713 22358807883857687781854785)
        ·
          refine ⟨16769105912893265836391089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22358807883857687781854785 16769105912893265836391089)
          ·
            refine ⟨12576829434669949377293317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16769105912893265836391089 12576829434669949377293317)
            ·
              refine ⟨2358155519000615508242497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12576829434669949377293317 2358155519000615508242497)
              ·
                refine ⟨1768616639250461631181873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358155519000615508242497 1768616639250461631181873)
                ·
                  refine ⟨1326462479437846223386405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768616639250461631181873 1326462479437846223386405)
                  ·
                    refine ⟨248711714894596166884951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326462479437846223386405 248711714894596166884951)
                    ·
                      rfl

theorem cell23_1453093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_1453093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453093 prefixEnd_1453093 := by exact prefixLift 1453093
  have htrace : WordTrace (prefixWord ++ tailWord_1453093) baseStart_1453093 baseEnd_1453093 := by
    simpa [prefixWord, tailWord_1453093, baseEnd_1453093] using wordTrace_append hprefix tailTrace_1453093
  have hstable : (prefixWord ++ tailWord_1453093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453093).length < 2 ^ (prefixWord ++ tailWord_1453093).sum := by decide
  have hdescent : baseEnd_1453093 < baseStart_1453093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453110 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1453110 : Nat := 118140960795 + 1453110 * 2 ^ 59
def prefixEnd_1453110 : Nat := 4983230072969 + 3 ^ 40 * 1453110 * 2
def baseEnd_1453110 : Nat := 248714624618304978047425

theorem tailTrace_1453110 : CollatzResearch.WordTrace tailWord_1453110 prefixEnd_1453110 248714624618304978047425 := by
  unfold tailWord_1453110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312454735352382267198299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35332850510425410850115189 3312454735352382267198299)
  ·
    refine ⟨4968682103028573400797449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3312454735352382267198299 4968682103028573400797449)
    ·
      refine ⟨3726511577271430050598087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968682103028573400797449 3726511577271430050598087)
      ·
        refine ⟨5589767365907145075897131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726511577271430050598087 5589767365907145075897131)
        ·
          refine ⟨8384651048860717613845697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589767365907145075897131 8384651048860717613845697)
          ·
            refine ⟨6288488286645538210384273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8384651048860717613845697 6288488286645538210384273)
            ·
              refine ⟨4716366214984153657788205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288488286645538210384273 4716366214984153657788205)
              ·
                refine ⟨1768637330619057621670577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716366214984153657788205 1768637330619057621670577)
                ·
                  refine ⟨1326477997964293216252933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768637330619057621670577 1326477997964293216252933)
                  ·
                    refine ⟨248714624618304978047425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326477997964293216252933 248714624618304978047425)
                    ·
                      rfl

theorem cell23_1453110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1453110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453110 prefixEnd_1453110 := by exact prefixLift 1453110
  have htrace : WordTrace (prefixWord ++ tailWord_1453110) baseStart_1453110 baseEnd_1453110 := by
    simpa [prefixWord, tailWord_1453110, baseEnd_1453110] using wordTrace_append hprefix tailTrace_1453110
  have hstable : (prefixWord ++ tailWord_1453110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453110).length < 2 ^ (prefixWord ++ tailWord_1453110).sum := by decide
  have hdescent : baseEnd_1453110 < baseStart_1453110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453113 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1453113 : Nat := 118140960795 + 1453113 * 2 ^ 59
def prefixEnd_1453113 : Nat := 4983230072969 + 3 ^ 40 * 1453113 * 2
def baseEnd_1453113 : Nat := 746145414296878422404761

theorem tailTrace_1453113 : CollatzResearch.WordTrace tailWord_1453113 prefixEnd_1453113 746145414296878422404761 := by
  unfold tailWord_1453113
  simp only [CollatzResearch.WordTrace]
  refine ⟨52999385184627247787531993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35332923456418165191687995 52999385184627247787531993)
  ·
    refine ⟨39749538888470435840648995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52999385184627247787531993 39749538888470435840648995)
    ·
      refine ⟨59624308332705653760973493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39749538888470435840648995 59624308332705653760973493)
      ·
        refine ⟨5589778906191155040091265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59624308332705653760973493 5589778906191155040091265)
        ·
          refine ⟨4192334179643366280068449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5589778906191155040091265 4192334179643366280068449)
          ·
            refine ⟨3144250634732524710051337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192334179643366280068449 3144250634732524710051337)
            ·
              refine ⟨2358187976049393532538503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144250634732524710051337 2358187976049393532538503)
              ·
                refine ⟨3537281964074090298807755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358187976049393532538503 3537281964074090298807755)
                ·
                  refine ⟨5305922946111135448211633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537281964074090298807755 5305922946111135448211633)
                  ·
                    refine ⟨3979442209583351586158725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305922946111135448211633 3979442209583351586158725)
                    ·
                      refine ⟨746145414296878422404761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3979442209583351586158725 746145414296878422404761)
                      ·
                        rfl

theorem cell23_1453113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1453113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453113 prefixEnd_1453113 := by exact prefixLift 1453113
  have htrace : WordTrace (prefixWord ++ tailWord_1453113) baseStart_1453113 baseEnd_1453113 := by
    simpa [prefixWord, tailWord_1453113, baseEnd_1453113] using wordTrace_append hprefix tailTrace_1453113
  have hstable : (prefixWord ++ tailWord_1453113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453113).length < 2 ^ (prefixWord ++ tailWord_1453113).sum := by decide
  have hdescent : baseEnd_1453113 < baseStart_1453113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453119 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 7]
def baseStart_1453119 : Nat := 118140960795 + 1453119 * 2 ^ 59
def prefixEnd_1453119 : Nat := 4983230072969 + 3 ^ 40 * 1453119 * 2
def baseEnd_1453119 : Nat := 248716165060268466309911

theorem tailTrace_1453119 : CollatzResearch.WordTrace tailWord_1453119 prefixEnd_1453119 248716165060268466309911 := by
  unfold tailWord_1453119
  simp only [CollatzResearch.WordTrace]
  refine ⟨52999604022605510812250411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35333069348403673874833607 52999604022605510812250411)
  ·
    refine ⟨79499406033908266218375617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52999604022605510812250411 79499406033908266218375617)
    ·
      refine ⟨59624554525431199663781713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79499406033908266218375617 59624554525431199663781713)
      ·
        refine ⟨44718415894073399747836285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59624554525431199663781713 44718415894073399747836285)
        ·
          refine ⟨16769405960277524905438607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44718415894073399747836285 16769405960277524905438607)
          ·
            refine ⟨25154108940416287358157911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16769405960277524905438607 25154108940416287358157911)
            ·
              refine ⟨37731163410624431037236867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25154108940416287358157911 37731163410624431037236867)
              ·
                refine ⟨56596745115936646555855301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37731163410624431037236867 56596745115936646555855301)
                ·
                  refine ⟨10611889709238121229222869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56596745115936646555855301 10611889709238121229222869)
                  ·
                    refine ⟨248716165060268466309911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10611889709238121229222869 248716165060268466309911)
                    ·
                      rfl

theorem cell23_1453119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_1453119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453119 prefixEnd_1453119 := by exact prefixLift 1453119
  have htrace : WordTrace (prefixWord ++ tailWord_1453119) baseStart_1453119 baseEnd_1453119 := by
    simpa [prefixWord, tailWord_1453119, baseEnd_1453119] using wordTrace_append hprefix tailTrace_1453119
  have hstable : (prefixWord ++ tailWord_1453119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453119).length < 2 ^ (prefixWord ++ tailWord_1453119).sum := by decide
  have hdescent : baseEnd_1453119 < baseStart_1453119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453176 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1453176 : Nat := 118140960795 + 1453176 * 2 ^ 59
def prefixEnd_1453176 : Nat := 4983230072969 + 3 ^ 40 * 1453176 * 2
def baseEnd_1453176 : Nat := 746177763578111675916971

theorem tailTrace_1453176 : CollatzResearch.WordTrace tailWord_1453176 prefixEnd_1453176 746177763578111675916971 := by
  unfold tailWord_1453176
  simp only [CollatzResearch.WordTrace]
  refine ⟨26500841491699504773537691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35334455322266006364716921 26500841491699504773537691)
  ·
    refine ⟨39751262237549257160306537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26500841491699504773537691 39751262237549257160306537)
    ·
      refine ⟨29813446678161942870229903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39751262237549257160306537 29813446678161942870229903)
      ·
        refine ⟨44720170017242914305344855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29813446678161942870229903 44720170017242914305344855)
        ·
          refine ⟨67080255025864371458017283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44720170017242914305344855 67080255025864371458017283)
          ·
            refine ⟨100620382538796557187025925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67080255025864371458017283 100620382538796557187025925)
            ·
              refine ⟨18866321726024354472567361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100620382538796557187025925 18866321726024354472567361)
              ·
                refine ⟨14149741294518265854425521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18866321726024354472567361 14149741294518265854425521)
                ·
                  refine ⟨10612305970888699390819141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14149741294518265854425521 10612305970888699390819141)
                  ·
                    refine ⟨1989807369541631135778589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10612305970888699390819141 1989807369541631135778589)
                    ·
                      refine ⟨746177763578111675916971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1989807369541631135778589 746177763578111675916971)
                      ·
                        rfl

theorem cell23_1453176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1453176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453176 prefixEnd_1453176 := by exact prefixLift 1453176
  have htrace : WordTrace (prefixWord ++ tailWord_1453176) baseStart_1453176 baseEnd_1453176 := by
    simpa [prefixWord, tailWord_1453176, baseEnd_1453176] using wordTrace_append hprefix tailTrace_1453176
  have hstable : (prefixWord ++ tailWord_1453176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453176).length < 2 ^ (prefixWord ++ tailWord_1453176).sum := by decide
  have hdescent : baseEnd_1453176 < baseStart_1453176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453177 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 1, 3, 2]
def baseStart_1453177 : Nat := 118140960795 + 1453177 * 2 ^ 59
def prefixEnd_1453177 : Nat := 4983230072969 + 3 ^ 40 * 1453177 * 2
def baseEnd_1453177 : Nat := 746178277058766172004467

theorem tailTrace_1453177 : CollatzResearch.WordTrace tailWord_1453177 prefixEnd_1453177 746178277058766172004467 := by
  unfold tailWord_1453177
  simp only [CollatzResearch.WordTrace]
  refine ⟨53001719456395386717861785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35334479637596924478574523 53001719456395386717861785)
  ·
    refine ⟨39751289592296540038396339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53001719456395386717861785 39751289592296540038396339)
    ·
      refine ⟨59626934388444810057594509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39751289592296540038396339 59626934388444810057594509)
      ·
        refine ⟨22360100395666803771597941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59626934388444810057594509 22360100395666803771597941)
        ·
          refine ⟨2096259412093762853587307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22360100395666803771597941 2096259412093762853587307)
          ·
            refine ⟨3144389118140644280380961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096259412093762853587307 3144389118140644280380961)
            ·
              refine ⟨2358291838605483210285721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144389118140644280380961 2358291838605483210285721)
              ·
                refine ⟨1768718878954112407714291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358291838605483210285721 1768718878954112407714291)
                ·
                  refine ⟨2653078318431168611571437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768718878954112407714291 2653078318431168611571437)
                  ·
                    refine ⟨994904369411688229339289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653078318431168611571437 994904369411688229339289)
                    ·
                      refine ⟨746178277058766172004467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994904369411688229339289 746178277058766172004467)
                      ·
                        rfl

theorem cell23_1453177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_1453177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453177 prefixEnd_1453177 := by exact prefixLift 1453177
  have htrace : WordTrace (prefixWord ++ tailWord_1453177) baseStart_1453177 baseEnd_1453177 := by
    simpa [prefixWord, tailWord_1453177, baseEnd_1453177] using wordTrace_append hprefix tailTrace_1453177
  have hstable : (prefixWord ++ tailWord_1453177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453177).length < 2 ^ (prefixWord ++ tailWord_1453177).sum := by decide
  have hdescent : baseEnd_1453177 < baseStart_1453177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453273 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_1453273 : Nat := 118140960795 + 1453273 * 2 ^ 59
def prefixEnd_1453273 : Nat := 4983230072969 + 3 ^ 40 * 1453273 * 2
def baseEnd_1453273 : Nat := 248742523733865932134675

theorem tailTrace_1453273 : CollatzResearch.WordTrace tailWord_1453273 prefixEnd_1453273 248742523733865932134675 := by
  unfold tailWord_1453273
  simp only [CollatzResearch.WordTrace]
  refine ⟨53005220864047595113356473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35336813909365063408904315 53005220864047595113356473)
  ·
    refine ⟨39753915648035696335017355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53005220864047595113356473 39753915648035696335017355)
    ·
      refine ⟨59630873472053544502526033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39753915648035696335017355 59630873472053544502526033)
      ·
        refine ⟨44723155104040158376894525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59630873472053544502526033 44723155104040158376894525)
        ·
          refine ⟨16771183164015059391335447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44723155104040158376894525 16771183164015059391335447)
          ·
            refine ⟨25156774746022589087003171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771183164015059391335447 25156774746022589087003171)
            ·
              refine ⟨37735162119033883630504757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25156774746022589087003171 37735162119033883630504757)
              ·
                refine ⟨3537671448659426590359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37735162119033883630504757 3537671448659426590359821)
                ·
                  refine ⟨1326626793247284971384933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3537671448659426590359821 1326626793247284971384933)
                  ·
                    refine ⟨248742523733865932134675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326626793247284971384933 248742523733865932134675)
                    ·
                      rfl

theorem cell23_1453273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_1453273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453273 prefixEnd_1453273 := by exact prefixLift 1453273
  have htrace : WordTrace (prefixWord ++ tailWord_1453273) baseStart_1453273 baseEnd_1453273 := by
    simpa [prefixWord, tailWord_1453273, baseEnd_1453273] using wordTrace_append hprefix tailTrace_1453273
  have hstable : (prefixWord ++ tailWord_1453273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453273).length < 2 ^ (prefixWord ++ tailWord_1453273).sum := by decide
  have hdescent : baseEnd_1453273 < baseStart_1453273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453280 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2]
def baseStart_1453280 : Nat := 118140960795 + 1453280 * 2 ^ 59
def prefixEnd_1453280 : Nat := 4983230072969 + 3 ^ 40 * 1453280 * 2
def baseEnd_1453280 : Nat := 746231165566179269016493

theorem tailTrace_1453280 : CollatzResearch.WordTrace tailWord_1453280 prefixEnd_1453280 746231165566179269016493 := by
  unfold tailWord_1453280
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502738087511117654430647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35336984116681490205907529 26502738087511117654430647)
  ·
    refine ⟨39754107131266676481645971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26502738087511117654430647 39754107131266676481645971)
    ·
      refine ⟨59631160696900014722468957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39754107131266676481645971 59631160696900014722468957)
      ·
        refine ⟨22361685261337505520925859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59631160696900014722468957 22361685261337505520925859)
        ·
          refine ⟨33542527892006258281388789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22361685261337505520925859 33542527892006258281388789)
          ·
            refine ⟨3144611989875586713880199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33542527892006258281388789 3144611989875586713880199)
            ·
              refine ⟨4716917984813380070820299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144611989875586713880199 4716917984813380070820299)
              ·
                refine ⟨7075376977220070106230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716917984813380070820299 7075376977220070106230449)
                ·
                  refine ⟨5306532732915052579672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7075376977220070106230449 5306532732915052579672837)
                  ·
                    refine ⟨994974887421572358688657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306532732915052579672837 994974887421572358688657)
                    ·
                      refine ⟨746231165566179269016493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 994974887421572358688657 746231165566179269016493)
                      ·
                        rfl

theorem cell23_1453280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_1453280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453280 prefixEnd_1453280 := by exact prefixLift 1453280
  have htrace : WordTrace (prefixWord ++ tailWord_1453280) baseStart_1453280 baseEnd_1453280 := by
    simpa [prefixWord, tailWord_1453280, baseEnd_1453280] using wordTrace_append hprefix tailTrace_1453280
  have hstable : (prefixWord ++ tailWord_1453280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453280).length < 2 ^ (prefixWord ++ tailWord_1453280).sum := by decide
  have hdescent : baseEnd_1453280 < baseStart_1453280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453290 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1453290 : Nat := 118140960795 + 1453290 * 2 ^ 59
def prefixEnd_1453290 : Nat := 4983230072969 + 3 ^ 40 * 1453290 * 2
def baseEnd_1453290 : Nat := 248745433457574743297149

theorem tailTrace_1453290 : CollatzResearch.WordTrace tailWord_1453290 prefixEnd_1453290 248745433457574743297149 := by
  unfold tailWord_1453290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251460226246501754181331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35337227269990671344483549 13251460226246501754181331)
  ·
    refine ⟨19877190339369752631271997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251460226246501754181331 19877190339369752631271997)
    ·
      refine ⟨7453946377263657236726999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19877190339369752631271997 7453946377263657236726999)
      ·
        refine ⟨11180919565895485855090499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7453946377263657236726999 11180919565895485855090499)
        ·
          refine ⟨16771379348843228782635749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11180919565895485855090499 16771379348843228782635749)
          ·
            refine ⟨3144633627908105396744203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16771379348843228782635749 3144633627908105396744203)
            ·
              refine ⟨4716950441862158095116305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144633627908105396744203 4716950441862158095116305)
              ·
                refine ⟨3537712831396618571337229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716950441862158095116305 3537712831396618571337229)
                ·
                  refine ⟨1326642311773731964251461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3537712831396618571337229 1326642311773731964251461)
                  ·
                    refine ⟨248745433457574743297149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326642311773731964251461 248745433457574743297149)
                    ·
                      rfl

theorem cell23_1453290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1453290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453290 prefixEnd_1453290 := by exact prefixLift 1453290
  have htrace : WordTrace (prefixWord ++ tailWord_1453290) baseStart_1453290 baseEnd_1453290 := by
    simpa [prefixWord, tailWord_1453290, baseEnd_1453290] using wordTrace_append hprefix tailTrace_1453290
  have hstable : (prefixWord ++ tailWord_1453290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453290).length < 2 ^ (prefixWord ++ tailWord_1453290).sum := by decide
  have hdescent : baseEnd_1453290 < baseStart_1453290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453340 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1453340 : Nat := 118140960795 + 1453340 * 2 ^ 59
def prefixEnd_1453340 : Nat := 4983230072969 + 3 ^ 40 * 1453340 * 2
def baseEnd_1453340 : Nat := 746261974405449034266217

theorem tailTrace_1453340 : CollatzResearch.WordTrace tailWord_1453340 prefixEnd_1453340 746261974405449034266217 := by
  unfold tailWord_1453340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26503832277402432778022737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35338443036536577037363649 26503832277402432778022737)
  ·
    refine ⟨19877874208051824583517053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26503832277402432778022737 19877874208051824583517053)
    ·
      refine ⟨7454202828019434218818895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19877874208051824583517053 7454202828019434218818895)
      ·
        refine ⟨11181304242029151328228343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7454202828019434218818895 11181304242029151328228343)
        ·
          refine ⟨16771956363043726992342515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11181304242029151328228343 16771956363043726992342515)
          ·
            refine ⟨25157934544565590488513773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771956363043726992342515 25157934544565590488513773)
            ·
              refine ⟨9434225454212096433192665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25157934544565590488513773 9434225454212096433192665)
              ·
                refine ⟨7075669090659072324894499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434225454212096433192665 7075669090659072324894499)
                ·
                  refine ⟨10613503635988608487341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7075669090659072324894499 10613503635988608487341749)
                  ·
                    refine ⟨995015965873932045688289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10613503635988608487341749 995015965873932045688289)
                    ·
                      refine ⟨746261974405449034266217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995015965873932045688289 746261974405449034266217)
                      ·
                        rfl

theorem cell23_1453340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1453340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453340 prefixEnd_1453340 := by exact prefixLift 1453340
  have htrace : WordTrace (prefixWord ++ tailWord_1453340) baseStart_1453340 baseEnd_1453340 := by
    simpa [prefixWord, tailWord_1453340, baseEnd_1453340] using wordTrace_append hprefix tailTrace_1453340
  have hstable : (prefixWord ++ tailWord_1453340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453340).length < 2 ^ (prefixWord ++ tailWord_1453340).sum := by decide
  have hdescent : baseEnd_1453340 < baseStart_1453340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453370 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_1453370 : Nat := 118140960795 + 1453370 * 2 ^ 59
def prefixEnd_1453370 : Nat := 4983230072969 + 3 ^ 40 * 1453370 * 2
def baseEnd_1453370 : Nat := 746277378825083916891079

theorem tailTrace_1453370 : CollatzResearch.WordTrace tailWord_1453370 prefixEnd_1453370 746277378825083916891079 := by
  unfold tailWord_1453370
  simp only [CollatzResearch.WordTrace]
  refine ⟨13252189686174045169909391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35339172496464120453091709 13252189686174045169909391)
  ·
    refine ⟨19878284529261067754864087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13252189686174045169909391 19878284529261067754864087)
    ·
      refine ⟨29817426793891601632296131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19878284529261067754864087 29817426793891601632296131)
      ·
        refine ⟨44726140190837402448444197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29817426793891601632296131 44726140190837402448444197)
        ·
          refine ⟨8386151285782012959083287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44726140190837402448444197 8386151285782012959083287)
          ·
            refine ⟨12579226928673019438624931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386151285782012959083287 12579226928673019438624931)
            ·
              refine ⟨18868840393009529157937397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12579226928673019438624931 18868840393009529157937397)
              ·
                refine ⟨1768953786844643358556631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18868840393009529157937397 1768953786844643358556631)
                ·
                  refine ⟨2653430680266965037834947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768953786844643358556631 2653430680266965037834947)
                  ·
                    refine ⟨3980146020400447556752421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2653430680266965037834947 3980146020400447556752421)
                    ·
                      refine ⟨746277378825083916891079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3980146020400447556752421 746277378825083916891079)
                      ·
                        rfl

theorem cell23_1453370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_1453370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453370 prefixEnd_1453370 := by exact prefixLift 1453370
  have htrace : WordTrace (prefixWord ++ tailWord_1453370) baseStart_1453370 baseEnd_1453370 := by
    simpa [prefixWord, tailWord_1453370, baseEnd_1453370] using wordTrace_append hprefix tailTrace_1453370
  have hstable : (prefixWord ++ tailWord_1453370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453370).length < 2 ^ (prefixWord ++ tailWord_1453370).sum := by decide
  have hdescent : baseEnd_1453370 < baseStart_1453370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453383 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1453383 : Nat := 118140960795 + 1453383 * 2 ^ 59
def prefixEnd_1453383 : Nat := 4983230072969 + 3 ^ 40 * 1453383 * 2
def baseEnd_1453383 : Nat := 746284054073592366028519

theorem tailTrace_1453383 : CollatzResearch.WordTrace tailWord_1453383 prefixEnd_1453383 746284054073592366028519 := by
  unfold tailWord_1453383
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009232893649083899860803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35339488595766055933240535 53009232893649083899860803)
  ·
    refine ⟨79513849340473625849791205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53009232893649083899860803 79513849340473625849791205)
    ·
      refine ⟨14908846751338804846835851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79513849340473625849791205 14908846751338804846835851)
      ·
        refine ⟨22363270127008207270253777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14908846751338804846835851 22363270127008207270253777)
        ·
          refine ⟨16772452595256155452690333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22363270127008207270253777 16772452595256155452690333)
          ·
            refine ⟨6289669723221058294758875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16772452595256155452690333 6289669723221058294758875)
            ·
              refine ⟨9434504584831587442138313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289669723221058294758875 9434504584831587442138313)
              ·
                refine ⟨7075878438623690581603735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434504584831587442138313 7075878438623690581603735)
                ·
                  refine ⟨10613817657935535872405603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7075878438623690581603735 10613817657935535872405603)
                  ·
                    refine ⟨15920726486903303808608405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10613817657935535872405603 15920726486903303808608405)
                    ·
                      refine ⟨746284054073592366028519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15920726486903303808608405 746284054073592366028519)
                      ·
                        rfl

theorem cell23_1453383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1453383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453383 prefixEnd_1453383 := by exact prefixLift 1453383
  have htrace : WordTrace (prefixWord ++ tailWord_1453383) baseStart_1453383 baseEnd_1453383 := by
    simpa [prefixWord, tailWord_1453383, baseEnd_1453383] using wordTrace_append hprefix tailTrace_1453383
  have hstable : (prefixWord ++ tailWord_1453383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453383).length < 2 ^ (prefixWord ++ tailWord_1453383).sum := by decide
  have hdescent : baseEnd_1453383 < baseStart_1453383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453390 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1453390 : Nat := 118140960795 + 1453390 * 2 ^ 59
def prefixEnd_1453390 : Nat := 4983230072969 + 3 ^ 40 * 1453390 * 2
def baseEnd_1453390 : Nat := 746287648438173838640987

theorem tailTrace_1453390 : CollatzResearch.WordTrace tailWord_1453390 prefixEnd_1453390 746287648438173838640987 := by
  unfold tailWord_1453390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626186025577965511920703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35339658803082482730243749 6626186025577965511920703)
  ·
    refine ⟨9939279038366948267881055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6626186025577965511920703 9939279038366948267881055)
    ·
      refine ⟨14908918557550422401821583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9939279038366948267881055 14908918557550422401821583)
      ·
        refine ⟨22363377836325633602732375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14908918557550422401821583 22363377836325633602732375)
        ·
          refine ⟨33545066754488450404098563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22363377836325633602732375 33545066754488450404098563)
          ·
            refine ⟨50317600131732675606147845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33545066754488450404098563 50317600131732675606147845)
            ·
              refine ⟨9434550024699876676152721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50317600131732675606147845 9434550024699876676152721)
              ·
                refine ⟨7075912518524907507114541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434550024699876676152721 7075912518524907507114541)
                ·
                  refine ⟨2653467194446840315167953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7075912518524907507114541 2653467194446840315167953)
                  ·
                    refine ⟨1990100395835130236375965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653467194446840315167953 1990100395835130236375965)
                    ·
                      refine ⟨746287648438173838640987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990100395835130236375965 746287648438173838640987)
                      ·
                        rfl

theorem cell23_1453390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1453390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453390 prefixEnd_1453390 := by exact prefixLift 1453390
  have htrace : WordTrace (prefixWord ++ tailWord_1453390) baseStart_1453390 baseEnd_1453390 := by
    simpa [prefixWord, tailWord_1453390, baseEnd_1453390] using wordTrace_append hprefix tailTrace_1453390
  have hstable : (prefixWord ++ tailWord_1453390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453390).length < 2 ^ (prefixWord ++ tailWord_1453390).sum := by decide
  have hdescent : baseEnd_1453390 < baseStart_1453390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453393 : List Nat := [1, 2, 2, 1, 4, 1, 4, 8]
def baseStart_1453393 : Nat := 118140960795 + 1453393 * 2 ^ 59
def prefixEnd_1453393 : Nat := 4983230072969 + 3 ^ 40 * 1453393 * 2
def baseEnd_1453393 : Nat := 27640340328893975070499

theorem tailTrace_1453393 : CollatzResearch.WordTrace tailWord_1453393 prefixEnd_1453393 27640340328893975070499 := by
  unfold tailWord_1453393
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009597623612855607724833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35339731749075237071816555 53009597623612855607724833)
  ·
    refine ⟨39757198217709641705793625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53009597623612855607724833 39757198217709641705793625)
    ·
      refine ⟨29817898663282231279345219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39757198217709641705793625 29817898663282231279345219)
      ·
        refine ⟨44726847994923346919017829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29817898663282231279345219 44726847994923346919017829)
        ·
          refine ⟨8386283999048127547315843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44726847994923346919017829 8386283999048127547315843)
          ·
            refine ⟨12579425998572191320973765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8386283999048127547315843 12579425998572191320973765)
            ·
              refine ⟨2358642374732285872682581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12579425998572191320973765 2358642374732285872682581)
              ·
                refine ⟨27640340328893975070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2358642374732285872682581 27640340328893975070499)
                ·
                  rfl

theorem cell23_1453393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 8].length) (baseStart_1453393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453393 prefixEnd_1453393 := by exact prefixLift 1453393
  have htrace : WordTrace (prefixWord ++ tailWord_1453393) baseStart_1453393 baseEnd_1453393 := by
    simpa [prefixWord, tailWord_1453393, baseEnd_1453393] using wordTrace_append hprefix tailTrace_1453393
  have hstable : (prefixWord ++ tailWord_1453393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453393).length < 2 ^ (prefixWord ++ tailWord_1453393).sum := by decide
  have hdescent : baseEnd_1453393 < baseStart_1453393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453397 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_1453397 : Nat := 118140960795 + 1453397 * 2 ^ 59
def prefixEnd_1453397 : Nat := 4983230072969 + 3 ^ 40 * 1453397 * 2
def baseEnd_1453397 : Nat := 248763747600918437084485

theorem tailTrace_1453397 : CollatzResearch.WordTrace tailWord_1453397 prefixEnd_1453397 248763747600918437084485 := by
  unfold tailWord_1453397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53009743515598364290870445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35339829010398909527246963 53009743515598364290870445)
  ·
    refine ⟨19878653818349386609076417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53009743515598364290870445 19878653818349386609076417)
    ·
      refine ⟨14908990363762039956807313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19878653818349386609076417 14908990363762039956807313)
      ·
        refine ⟨11181742772821529967605485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14908990363762039956807313 11181742772821529967605485)
        ·
          refine ⟨4193153539808073737852057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11181742772821529967605485 4193153539808073737852057)
          ·
            refine ⟨3144865154856055303389043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193153539808073737852057 3144865154856055303389043)
            ·
              refine ⟨4717297732284082955083565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144865154856055303389043 4717297732284082955083565)
              ·
                refine ⟨1768986649606531108156337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4717297732284082955083565 1768986649606531108156337)
                ·
                  refine ⟨1326739987204898331117253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768986649606531108156337 1326739987204898331117253)
                  ·
                    refine ⟨248763747600918437084485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326739987204898331117253 248763747600918437084485)
                    ·
                      rfl

theorem cell23_1453397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_1453397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453397 prefixEnd_1453397 := by exact prefixLift 1453397
  have htrace : WordTrace (prefixWord ++ tailWord_1453397) baseStart_1453397 baseEnd_1453397 := by
    simpa [prefixWord, tailWord_1453397, baseEnd_1453397] using wordTrace_append hprefix tailTrace_1453397
  have hstable : (prefixWord ++ tailWord_1453397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453397).length < 2 ^ (prefixWord ++ tailWord_1453397).sum := by decide
  have hdescent : baseEnd_1453397 < baseStart_1453397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453420 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1453420 : Nat := 118140960795 + 1453420 * 2 ^ 59
def prefixEnd_1453420 : Nat := 4983230072969 + 3 ^ 40 * 1453420 * 2
def baseEnd_1453420 : Nat := 746303052857808721265849

theorem tailTrace_1453420 : CollatzResearch.WordTrace tailWord_1453420 prefixEnd_1453420 746303052857808721265849 := by
  unfold tailWord_1453420
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505291197257519609478857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35340388263010026145971809 26505291197257519609478857)
  ·
    refine ⟨19878968397943139707109143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26505291197257519609478857 19878968397943139707109143)
    ·
      refine ⟨29818452596914709560663715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19878968397943139707109143 29818452596914709560663715)
      ·
        refine ⟨44727678895372064340995573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29818452596914709560663715 44727678895372064340995573)
        ·
          refine ⟨4193219896441131031968335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44727678895372064340995573 4193219896441131031968335)
          ·
            refine ⟨6289829844661696547952503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193219896441131031968335 6289829844661696547952503)
            ·
              refine ⟨9434744766992544821928755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289829844661696547952503 9434744766992544821928755)
              ·
                refine ⟨14152117150488817232893133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9434744766992544821928755 14152117150488817232893133)
                ·
                  refine ⟨5307043931433306462334925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14152117150488817232893133 5307043931433306462334925)
                  ·
                    refine ⟨1990141474287489923375597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5307043931433306462334925 1990141474287489923375597)
                    ·
                      refine ⟨746303052857808721265849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990141474287489923375597 746303052857808721265849)
                      ·
                        rfl

theorem cell23_1453420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1453420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453420 prefixEnd_1453420 := by exact prefixLift 1453420
  have htrace : WordTrace (prefixWord ++ tailWord_1453420) baseStart_1453420 baseEnd_1453420 := by
    simpa [prefixWord, tailWord_1453420, baseEnd_1453420] using wordTrace_append hprefix tailTrace_1453420
  have hstable : (prefixWord ++ tailWord_1453420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453420).length < 2 ^ (prefixWord ++ tailWord_1453420).sum := by decide
  have hdescent : baseEnd_1453420 < baseStart_1453420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453433 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1453433 : Nat := 118140960795 + 1453433 * 2 ^ 59
def prefixEnd_1453433 : Nat := 4983230072969 + 3 ^ 40 * 1453433 * 2
def baseEnd_1453433 : Nat := 746309728106317170403289

theorem tailTrace_1453433 : CollatzResearch.WordTrace tailWord_1453433 prefixEnd_1453433 746309728106317170403289 := by
  unfold tailWord_1453433
  simp only [CollatzResearch.WordTrace]
  refine ⟨53011056543467942439180953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35340704362311961626120635 53011056543467942439180953)
  ·
    refine ⟨39758292407600956829385715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53011056543467942439180953 39758292407600956829385715)
    ·
      refine ⟨59637438611401435244078573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39758292407600956829385715 59637438611401435244078573)
      ·
        refine ⟨22364039479275538216529465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59637438611401435244078573 22364039479275538216529465)
        ·
          refine ⟨16773029609456653662397099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22364039479275538216529465 16773029609456653662397099)
          ·
            refine ⟨25159544414184980493595649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16773029609456653662397099 25159544414184980493595649)
            ·
              refine ⟨18869658310638735370196737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25159544414184980493595649 18869658310638735370196737)
              ·
                refine ⟨14152243732979051527647553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18869658310638735370196737 14152243732979051527647553)
                ·
                  refine ⟨10614182799734288645735665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14152243732979051527647553 10614182799734288645735665)
                  ·
                    refine ⟨7960637099800716484301749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10614182799734288645735665 7960637099800716484301749)
                    ·
                      refine ⟨746309728106317170403289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7960637099800716484301749 746309728106317170403289)
                      ·
                        rfl

theorem cell23_1453433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1453433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453433 prefixEnd_1453433 := by exact prefixLift 1453433
  have htrace : WordTrace (prefixWord ++ tailWord_1453433) baseStart_1453433 baseEnd_1453433 := by
    simpa [prefixWord, tailWord_1453433, baseEnd_1453433] using wordTrace_append hprefix tailTrace_1453433
  have hstable : (prefixWord ++ tailWord_1453433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453433).length < 2 ^ (prefixWord ++ tailWord_1453433).sum := by decide
  have hdescent : baseEnd_1453433 < baseStart_1453433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453447 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_1453447 : Nat := 118140960795 + 1453447 * 2 ^ 59
def prefixEnd_1453447 : Nat := 4983230072969 + 3 ^ 40 * 1453447 * 2
def baseEnd_1453447 : Nat := 746316916835480115628225

theorem tailTrace_1453447 : CollatzResearch.WordTrace tailWord_1453447 prefixEnd_1453447 746316916835480115628225 := by
  unfold tailWord_1453447
  simp only [CollatzResearch.WordTrace]
  refine ⟨53011567165417222830190595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35341044776944815220127063 53011567165417222830190595)
  ·
    refine ⟨79517350748125834245285893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53011567165417222830190595 79517350748125834245285893)
    ·
      refine ⟨14909503265273593920991105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79517350748125834245285893 14909503265273593920991105)
      ·
        refine ⟨11182127448955195440743329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14909503265273593920991105 11182127448955195440743329)
        ·
          refine ⟨8386595586716396580557497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11182127448955195440743329 8386595586716396580557497)
          ·
            refine ⟨6289946690037297435418123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8386595586716396580557497 6289946690037297435418123)
            ·
              refine ⟨9434920035055946153127185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289946690037297435418123 9434920035055946153127185)
              ·
                refine ⟨7076190026291959614845389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9434920035055946153127185 7076190026291959614845389)
                ·
                  refine ⟨2653571259859484855567021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7076190026291959614845389 2653571259859484855567021)
                  ·
                    refine ⟨995089222447306820837633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2653571259859484855567021 995089222447306820837633)
                    ·
                      refine ⟨746316916835480115628225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995089222447306820837633 746316916835480115628225)
                      ·
                        rfl

theorem cell23_1453447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_1453447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453447 prefixEnd_1453447 := by exact prefixLift 1453447
  have htrace : WordTrace (prefixWord ++ tailWord_1453447) baseStart_1453447 baseEnd_1453447 := by
    simpa [prefixWord, tailWord_1453447, baseEnd_1453447] using wordTrace_append hprefix tailTrace_1453447
  have hstable : (prefixWord ++ tailWord_1453447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453447).length < 2 ^ (prefixWord ++ tailWord_1453447).sum := by decide
  have hdescent : baseEnd_1453447 < baseStart_1453447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453454 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1453454 : Nat := 118140960795 + 1453454 * 2 ^ 59
def prefixEnd_1453454 : Nat := 4983230072969 + 3 ^ 40 * 1453454 * 2
def baseEnd_1453454 : Nat := 746320511200061588240693

theorem tailTrace_1453454 : CollatzResearch.WordTrace tailWord_1453454 prefixEnd_1453454 746320511200061588240693 := by
  unfold tailWord_1453454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626477809548982878211927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35341214984261242017130277 6626477809548982878211927)
  ·
    refine ⟨9939716714323474317317891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6626477809548982878211927 9939716714323474317317891)
    ·
      refine ⟨14909575071485211475976837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9939716714323474317317891 14909575071485211475976837)
      ·
        refine ⟨2795545325903477151745657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14909575071485211475976837 2795545325903477151745657)
        ·
          refine ⟨2096658994427607863809243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795545325903477151745657 2096658994427607863809243)
          ·
            refine ⟨3144988491641411795713865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096658994427607863809243 3144988491641411795713865)
            ·
              refine ⟨2358741368731058846785399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144988491641411795713865 2358741368731058846785399)
              ·
                refine ⟨3538112053096588270178099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358741368731058846785399 3538112053096588270178099)
                ·
                  refine ⟨5307168079644882405267149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538112053096588270178099 5307168079644882405267149)
                  ·
                    refine ⟨1990188029866830901975181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5307168079644882405267149 1990188029866830901975181)
                    ·
                      refine ⟨746320511200061588240693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990188029866830901975181 746320511200061588240693)
                      ·
                        rfl

theorem cell23_1453454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1453454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453454 prefixEnd_1453454 := by exact prefixLift 1453454
  have htrace : WordTrace (prefixWord ++ tailWord_1453454) baseStart_1453454 baseEnd_1453454 := by
    simpa [prefixWord, tailWord_1453454, baseEnd_1453454] using wordTrace_append hprefix tailTrace_1453454
  have hstable : (prefixWord ++ tailWord_1453454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453454).length < 2 ^ (prefixWord ++ tailWord_1453454).sum := by decide
  have hdescent : baseEnd_1453454 < baseStart_1453454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453511 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_1453511 : Nat := 118140960795 + 1453511 * 2 ^ 59
def prefixEnd_1453511 : Nat := 4983230072969 + 3 ^ 40 * 1453511 * 2
def baseEnd_1453511 : Nat := 746349779597367865227931

theorem tailTrace_1453511 : CollatzResearch.WordTrace tailWord_1453511 prefixEnd_1453511 746349779597367865227931 := by
  unfold tailWord_1453511
  simp only [CollatzResearch.WordTrace]
  refine ⟨53013901437185361760520387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35342600958123574507013591 53013901437185361760520387)
  ·
    refine ⟨79520852155778042640780581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53013901437185361760520387 79520852155778042640780581)
    ·
      refine ⟨14910159779208382995146359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79520852155778042640780581 14910159779208382995146359)
      ·
        refine ⟨22365239668812574492719539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14910159779208382995146359 22365239668812574492719539)
        ·
          refine ⟨33547859503218861739079309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22365239668812574492719539 33547859503218861739079309)
          ·
            refine ⟨12580447313707073152154741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33547859503218861739079309 12580447313707073152154741)
            ·
              refine ⟨1179416935660038108014507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12580447313707073152154741 1179416935660038108014507)
              ·
                refine ⟨1769125403490057162021761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179416935660038108014507 1769125403490057162021761)
                ·
                  refine ⟨1326844052617542871516321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769125403490057162021761 1326844052617542871516321)
                  ·
                    refine ⟨995133039463157153637241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1326844052617542871516321 995133039463157153637241)
                    ·
                      refine ⟨746349779597367865227931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995133039463157153637241 746349779597367865227931)
                      ·
                        rfl

theorem cell23_1453511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_1453511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453511 prefixEnd_1453511 := by exact prefixLift 1453511
  have htrace : WordTrace (prefixWord ++ tailWord_1453511) baseStart_1453511 baseEnd_1453511 := by
    simpa [prefixWord, tailWord_1453511, baseEnd_1453511] using wordTrace_append hprefix tailTrace_1453511
  have hstable : (prefixWord ++ tailWord_1453511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453511).length < 2 ^ (prefixWord ++ tailWord_1453511).sum := by decide
  have hdescent : baseEnd_1453511 < baseStart_1453511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453530 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_1453530 : Nat := 118140960795 + 1453530 * 2 ^ 59
def prefixEnd_1453530 : Nat := 4983230072969 + 3 ^ 40 * 1453530 * 2
def baseEnd_1453530 : Nat := 248786511909934430296781

theorem tailTrace_1453530 : CollatzResearch.WordTrace tailWord_1453530 prefixEnd_1453530 248786511909934430296781 := by
  unfold tailWord_1453530
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253648606029132001365511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35343062949411018670308029 13253648606029132001365511)
  ·
    refine ⟨19880472909043698002048267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253648606029132001365511 19880472909043698002048267)
    ·
      refine ⟨29820709363565547003072401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19880472909043698002048267 29820709363565547003072401)
      ·
        refine ⟨22365532022674160252304301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29820709363565547003072401 22365532022674160252304301)
        ·
          refine ⟨8387074508502810094614113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22365532022674160252304301 8387074508502810094614113)
          ·
            refine ⟨6290305881377107570960585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8387074508502810094614113 6290305881377107570960585)
            ·
              refine ⟨4717729411032830678220439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290305881377107570960585 4717729411032830678220439)
              ·
                refine ⟨7076594116549246017330659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717729411032830678220439 7076594116549246017330659)
                ·
                  refine ⟨10614891174823869025995989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7076594116549246017330659 10614891174823869025995989)
                  ·
                    refine ⟨248786511909934430296781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10614891174823869025995989 248786511909934430296781)
                    ·
                      rfl

theorem cell23_1453530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_1453530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453530 prefixEnd_1453530 := by exact prefixLift 1453530
  have htrace : WordTrace (prefixWord ++ tailWord_1453530) baseStart_1453530 baseEnd_1453530 := by
    simpa [prefixWord, tailWord_1453530, baseEnd_1453530] using wordTrace_append hprefix tailTrace_1453530
  have hstable : (prefixWord ++ tailWord_1453530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453530).length < 2 ^ (prefixWord ++ tailWord_1453530).sum := by decide
  have hdescent : baseEnd_1453530 < baseStart_1453530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453557 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1453557 : Nat := 118140960795 + 1453557 * 2 ^ 59
def prefixEnd_1453557 : Nat := 4983230072969 + 3 ^ 40 * 1453557 * 2
def baseEnd_1453557 : Nat := 746373399707474685252719

theorem tailTrace_1453557 : CollatzResearch.WordTrace tailWord_1453557 prefixEnd_1453557 746373399707474685252719 := by
  unfold tailWord_1453557
  simp only [CollatzResearch.WordTrace]
  refine ⟨53015579195018711616694925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35343719463345807744463283 53015579195018711616694925)
  ·
    refine ⟨19880842198132016856260597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53015579195018711616694925 19880842198132016856260597)
    ·
      refine ⟨1863828956074876580274431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19880842198132016856260597 1863828956074876580274431)
      ·
        refine ⟨2795743434112314870411647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863828956074876580274431 2795743434112314870411647)
        ·
          refine ⟨4193615151168472305617471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795743434112314870411647 4193615151168472305617471)
          ·
            refine ⟨6290422726752708458426207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193615151168472305617471 6290422726752708458426207)
            ·
              refine ⟨9435634090129062687639311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290422726752708458426207 9435634090129062687639311)
              ·
                refine ⟨14153451135193594031458967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9435634090129062687639311 14153451135193594031458967)
                ·
                  refine ⟨21230176702790391047188451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14153451135193594031458967 21230176702790391047188451)
                  ·
                    refine ⟨31845265054185586570782677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21230176702790391047188451 31845265054185586570782677)
                    ·
                      refine ⟨746373399707474685252719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31845265054185586570782677 746373399707474685252719)
                      ·
                        rfl

theorem cell23_1453557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1453557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453557 prefixEnd_1453557 := by exact prefixLift 1453557
  have htrace : WordTrace (prefixWord ++ tailWord_1453557) baseStart_1453557 baseEnd_1453557 := by
    simpa [prefixWord, tailWord_1453557, baseEnd_1453557] using wordTrace_append hprefix tailTrace_1453557
  have hstable : (prefixWord ++ tailWord_1453557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453557).length < 2 ^ (prefixWord ++ tailWord_1453557).sum := by decide
  have hdescent : baseEnd_1453557 < baseStart_1453557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453587 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3]
def baseStart_1453587 : Nat := 118140960795 + 1453587 * 2 ^ 59
def prefixEnd_1453587 : Nat := 4983230072969 + 3 ^ 40 * 1453587 * 2
def baseEnd_1453587 : Nat := 746388804127109567877581

theorem tailTrace_1453587 : CollatzResearch.WordTrace tailWord_1453587 prefixEnd_1453587 746388804127109567877581 := by
  unfold tailWord_1453587
  simp only [CollatzResearch.WordTrace]
  refine ⟨53016673384910026740287015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35344448923273351160191343 53016673384910026740287015)
  ·
    refine ⟨79525010077365040110430523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53016673384910026740287015 79525010077365040110430523)
    ·
      refine ⟨119287515116047560165645785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79525010077365040110430523 119287515116047560165645785)
      ·
        refine ⟨89465636337035670124234339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119287515116047560165645785 89465636337035670124234339)
        ·
          refine ⟨134198454505553505186351509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89465636337035670124234339 134198454505553505186351509)
          ·
            refine ⟨6290552554947820555610227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134198454505553505186351509 6290552554947820555610227)
            ·
              refine ⟨9435828832421730833415341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290552554947820555610227 9435828832421730833415341)
              ·
                refine ⟨3538435812158149062530753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9435828832421730833415341 3538435812158149062530753)
                ·
                  refine ⟨2653826859118611796898065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538435812158149062530753 2653826859118611796898065)
                  ·
                    refine ⟨1990370144338958847673549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2653826859118611796898065 1990370144338958847673549)
                    ·
                      refine ⟨746388804127109567877581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990370144338958847673549 746388804127109567877581)
                      ·
                        rfl

theorem cell23_1453587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_1453587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453587 prefixEnd_1453587 := by exact prefixLift 1453587
  have htrace : WordTrace (prefixWord ++ tailWord_1453587) baseStart_1453587 baseEnd_1453587 := by
    simpa [prefixWord, tailWord_1453587, baseEnd_1453587] using wordTrace_append hprefix tailTrace_1453587
  have hstable : (prefixWord ++ tailWord_1453587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453587).length < 2 ^ (prefixWord ++ tailWord_1453587).sum := by decide
  have hdescent : baseEnd_1453587 < baseStart_1453587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453594 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_1453594 : Nat := 118140960795 + 1453594 * 2 ^ 59
def prefixEnd_1453594 : Nat := 4983230072969 + 3 ^ 40 * 1453594 * 2
def baseEnd_1453594 : Nat := 248797466163897013496683

theorem tailTrace_1453594 : CollatzResearch.WordTrace tailWord_1453594 prefixEnd_1453594 248797466163897013496683 := by
  unfold tailWord_1453594
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254232173971166733947959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35344619130589777957194557 13254232173971166733947959)
  ·
    refine ⟨19881348260956750100921939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13254232173971166733947959 19881348260956750100921939)
    ·
      refine ⟨29822022391435125151382909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881348260956750100921939 29822022391435125151382909)
      ·
        refine ⟨11183258396788171931768591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29822022391435125151382909 11183258396788171931768591)
        ·
          refine ⟨16774887595182257897652887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183258396788171931768591 16774887595182257897652887)
          ·
            refine ⟨25162331392773386846479331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16774887595182257897652887 25162331392773386846479331)
            ·
              refine ⟨37743497089160080269718997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25162331392773386846479331 37743497089160080269718997)
              ·
                refine ⟨884613213027189381321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37743497089160080269718997 884613213027189381321539)
                ·
                  refine ⟨1326919819540784071982309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884613213027189381321539 1326919819540784071982309)
                  ·
                    refine ⟨248797466163897013496683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326919819540784071982309 248797466163897013496683)
                    ·
                      rfl

theorem cell23_1453594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_1453594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453594 prefixEnd_1453594 := by exact prefixLift 1453594
  have htrace : WordTrace (prefixWord ++ tailWord_1453594) baseStart_1453594 baseEnd_1453594 := by
    simpa [prefixWord, tailWord_1453594, baseEnd_1453594] using wordTrace_append hprefix tailTrace_1453594
  have hstable : (prefixWord ++ tailWord_1453594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453594).length < 2 ^ (prefixWord ++ tailWord_1453594).sum := by decide
  have hdescent : baseEnd_1453594 < baseStart_1453594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453637 : List Nat := [1, 3, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_1453637 : Nat := 118140960795 + 1453637 * 2 ^ 59
def prefixEnd_1453637 : Nat := 4983230072969 + 3 ^ 40 * 1453637 * 2
def baseEnd_1453637 : Nat := 248804826053278124084117

theorem tailTrace_1453637 : CollatzResearch.WordTrace tailWord_1453637 prefixEnd_1453637 248804826053278124084117 := by
  unfold tailWord_1453637
  simp only [CollatzResearch.WordTrace]
  refine ⟨53018497034728885279607165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35345664689819256853071443 53018497034728885279607165)
  ·
    refine ⟨19881936388023331979852687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53018497034728885279607165 19881936388023331979852687)
    ·
      refine ⟨29822904582034997969779031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881936388023331979852687 29822904582034997969779031)
      ·
        refine ⟨44734356873052496954668547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29822904582034997969779031 44734356873052496954668547)
        ·
          refine ⟨67101535309578745432002821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44734356873052496954668547 67101535309578745432002821)
          ·
            refine ⟨12581537870546014768500529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67101535309578745432002821 12581537870546014768500529)
            ·
              refine ⟨9436153402909511076375397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12581537870546014768500529 9436153402909511076375397)
              ·
                refine ⟨1769278763045533326820387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9436153402909511076375397 1769278763045533326820387)
                ·
                  refine ⟨2653918144568299990230581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769278763045533326820387 2653918144568299990230581)
                  ·
                    refine ⟨248804826053278124084117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2653918144568299990230581 248804826053278124084117)
                    ·
                      rfl

theorem cell23_1453637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_1453637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453637 prefixEnd_1453637 := by exact prefixLift 1453637
  have htrace : WordTrace (prefixWord ++ tailWord_1453637) baseStart_1453637 baseEnd_1453637 := by
    simpa [prefixWord, tailWord_1453637, baseEnd_1453637] using wordTrace_append hprefix tailTrace_1453637
  have hstable : (prefixWord ++ tailWord_1453637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453637).length < 2 ^ (prefixWord ++ tailWord_1453637).sum := by decide
  have hdescent : baseEnd_1453637 < baseStart_1453637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453644 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1453644 : Nat := 118140960795 + 1453644 * 2 ^ 59
def prefixEnd_1453644 : Nat := 4983230072969 + 3 ^ 40 * 1453644 * 2
def baseEnd_1453644 : Nat := 746418072524415844864819

theorem tailTrace_1453644 : CollatzResearch.WordTrace tailWord_1453644 prefixEnd_1453644 746418072524415844864819 := by
  unfold tailWord_1453644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26509376172851762737555993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35345834897135683650074657 26509376172851762737555993)
  ·
    refine ⟨19882032129638822053166995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26509376172851762737555993 19882032129638822053166995)
    ·
      refine ⟨29823048194458233079750493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19882032129638822053166995 29823048194458233079750493)
      ·
        refine ⟨11183643072921837404906435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29823048194458233079750493 11183643072921837404906435)
        ·
          refine ⟨16775464609382756107359653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183643072921837404906435 16775464609382756107359653)
          ·
            refine ⟨3145399614259266770129935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16775464609382756107359653 3145399614259266770129935)
            ·
              refine ⟨4718099421388900155194903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145399614259266770129935 4718099421388900155194903)
              ·
                refine ⟨7077149132083350232792355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718099421388900155194903 7077149132083350232792355)
                ·
                  refine ⟨10615723698125025349188533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7077149132083350232792355 10615723698125025349188533)
                  ·
                    refine ⟨995224096699221126486425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10615723698125025349188533 995224096699221126486425)
                    ·
                      refine ⟨746418072524415844864819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995224096699221126486425 746418072524415844864819)
                      ·
                        rfl

theorem cell23_1453644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1453644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453644 prefixEnd_1453644 := by exact prefixLift 1453644
  have htrace : WordTrace (prefixWord ++ tailWord_1453644) baseStart_1453644 baseEnd_1453644 := by
    simpa [prefixWord, tailWord_1453644, baseEnd_1453644] using wordTrace_append hprefix tailTrace_1453644
  have hstable : (prefixWord ++ tailWord_1453644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453644).length < 2 ^ (prefixWord ++ tailWord_1453644).sum := by decide
  have hdescent : baseEnd_1453644 < baseStart_1453644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453657 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 8, 2]
def baseStart_1453657 : Nat := 118140960795 + 1453657 * 2 ^ 59
def prefixEnd_1453657 : Nat := 4983230072969 + 3 ^ 40 * 1453657 * 2
def baseEnd_1453657 : Nat := 746424747772924294002259

theorem tailTrace_1453657 : CollatzResearch.WordTrace tailWord_1453657 prefixEnd_1453657 746424747772924294002259 := by
  unfold tailWord_1453657
  simp only [CollatzResearch.WordTrace]
  refine ⟨53019226494656428695335225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35346150996437619130223483 53019226494656428695335225)
  ·
    refine ⟨39764419870992321521501419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53019226494656428695335225 39764419870992321521501419)
    ·
      refine ⟨59646629806488482282252129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39764419870992321521501419 59646629806488482282252129)
      ·
        refine ⟨44734972354866361711689097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59646629806488482282252129 44734972354866361711689097)
        ·
          refine ⟨33551229266149771283766823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44734972354866361711689097 33551229266149771283766823)
          ·
            refine ⟨50326843899224656925650235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33551229266149771283766823 50326843899224656925650235)
            ·
              refine ⟨75490265848836985388475353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50326843899224656925650235 75490265848836985388475353)
              ·
                refine ⟨56617699386627739041356515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75490265848836985388475353 56617699386627739041356515)
                ·
                  refine ⟨84926549079941608562034773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56617699386627739041356515 84926549079941608562034773)
                  ·
                    refine ⟨995232997030565725336345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84926549079941608562034773 995232997030565725336345)
                    ·
                      refine ⟨746424747772924294002259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995232997030565725336345 746424747772924294002259)
                      ·
                        rfl

theorem cell23_1453657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_1453657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453657 prefixEnd_1453657 := by exact prefixLift 1453657
  have htrace : WordTrace (prefixWord ++ tailWord_1453657) baseStart_1453657 baseEnd_1453657 := by
    simpa [prefixWord, tailWord_1453657, baseEnd_1453657] using wordTrace_append hprefix tailTrace_1453657
  have hstable : (prefixWord ++ tailWord_1453657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453657).length < 2 ^ (prefixWord ++ tailWord_1453657).sum := by decide
  have hdescent : baseEnd_1453657 < baseStart_1453657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453697 : List Nat := [1, 2, 4, 2, 1, 3, 1, 9]
def baseStart_1453697 : Nat := 118140960795 + 1453697 * 2 ^ 59
def prefixEnd_1453697 : Nat := 4983230072969 + 3 ^ 40 * 1453697 * 2
def baseEnd_1453697 : Nat := 27646121740707560648225

theorem tailTrace_1453697 : CollatzResearch.WordTrace tailWord_1453697 prefixEnd_1453697 27646121740707560648225 := by
  unfold tailWord_1453697
  simp only [CollatzResearch.WordTrace]
  refine ⟨53020685414511515526791345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35347123609674343684527563 53020685414511515526791345)
  ·
    refine ⟨39765514060883636645093509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53020685414511515526791345 39765514060883636645093509)
    ·
      refine ⟨7456033886415681870955033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39765514060883636645093509 7456033886415681870955033)
      ·
        refine ⟨5592025414811761403216275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7456033886415681870955033 5592025414811761403216275)
        ·
          refine ⟨8388038122217642104824413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592025414811761403216275 8388038122217642104824413)
          ·
            refine ⟨3145514295831615789309155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8388038122217642104824413 3145514295831615789309155)
            ·
              refine ⟨4718271443747423683963733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145514295831615789309155 4718271443747423683963733)
              ·
                refine ⟨27646121740707560648225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4718271443747423683963733 27646121740707560648225)
                ·
                  rfl

theorem cell23_1453697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 9].length) (baseStart_1453697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453697 prefixEnd_1453697 := by exact prefixLift 1453697
  have htrace : WordTrace (prefixWord ++ tailWord_1453697) baseStart_1453697 baseEnd_1453697 := by
    simpa [prefixWord, tailWord_1453697, baseEnd_1453697] using wordTrace_append hprefix tailTrace_1453697
  have hstable : (prefixWord ++ tailWord_1453697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453697).length < 2 ^ (prefixWord ++ tailWord_1453697).sum := by decide
  have hdescent : baseEnd_1453697 < baseStart_1453697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453707 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3]
def baseStart_1453707 : Nat := 118140960795 + 1453707 * 2 ^ 59
def prefixEnd_1453707 : Nat := 4983230072969 + 3 ^ 40 * 1453707 * 2
def baseEnd_1453707 : Nat := 746450421805649098377029

theorem tailTrace_1453707 : CollatzResearch.WordTrace tailWord_1453707 prefixEnd_1453707 746450421805649098377029 := by
  unfold tailWord_1453707
  simp only [CollatzResearch.WordTrace]
  refine ⟨53021050144475287234655375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35347366762983524823103583 53021050144475287234655375)
  ·
    refine ⟨79531575216712930851983063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53021050144475287234655375 79531575216712930851983063)
    ·
      refine ⟨119297362825069396277974595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79531575216712930851983063 119297362825069396277974595)
      ·
        refine ⟨178946044237604094416961893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119297362825069396277974595 178946044237604094416961893)
        ·
          refine ⟨33552383294550767703180355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178946044237604094416961893 33552383294550767703180355)
          ·
            refine ⟨50328574941826151554770533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33552383294550767703180355 50328574941826151554770533)
            ·
              refine ⟨9436607801592403416519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50328574941826151554770533 9436607801592403416519475)
              ·
                refine ⟨14154911702388605124779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436607801592403416519475 14154911702388605124779213)
                ·
                  refine ⟨5308091888395726921792205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14154911702388605124779213 5308091888395726921792205)
                  ·
                    refine ⟨1990534458148397595672077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5308091888395726921792205 1990534458148397595672077)
                    ·
                      refine ⟨746450421805649098377029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990534458148397595672077 746450421805649098377029)
                      ·
                        rfl

theorem cell23_1453707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 3].length) (baseStart_1453707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453707 prefixEnd_1453707 := by exact prefixLift 1453707
  have htrace : WordTrace (prefixWord ++ tailWord_1453707) baseStart_1453707 baseEnd_1453707 := by
    simpa [prefixWord, tailWord_1453707, baseEnd_1453707] using wordTrace_append hprefix tailTrace_1453707
  have hstable : (prefixWord ++ tailWord_1453707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453707).length < 2 ^ (prefixWord ++ tailWord_1453707).sum := by decide
  have hdescent : baseEnd_1453707 < baseStart_1453707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453714 : List Nat := [3, 2, 3, 1, 3, 2, 9]
def baseStart_1453714 : Nat := 118140960795 + 1453714 * 2 ^ 59
def prefixEnd_1453714 : Nat := 4983230072969 + 3 ^ 40 * 1453714 * 2
def baseEnd_1453714 : Nat := 9215481681113957666537

theorem tailTrace_1453714 : CollatzResearch.WordTrace tailWord_1453714 prefixEnd_1453714 9215481681113957666537 := by
  unfold tailWord_1453714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255326363862481857540049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35347536970299951620106797 13255326363862481857540049)
  ·
    refine ⟨9941494772896861393155037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13255326363862481857540049 9941494772896861393155037)
    ·
      refine ⟨3728060539836323022433139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9941494772896861393155037 3728060539836323022433139)
      ·
        refine ⟨5592090809754484533649709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728060539836323022433139 5592090809754484533649709)
        ·
          refine ⟨2097034053657931700118641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5592090809754484533649709 2097034053657931700118641)
          ·
            refine ⟨1572775540243448775088981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097034053657931700118641 1572775540243448775088981)
            ·
              refine ⟨9215481681113957666537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1572775540243448775088981 9215481681113957666537)
              ·
                rfl

theorem cell23_1453714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 9].length) (baseStart_1453714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453714 prefixEnd_1453714 := by exact prefixLift 1453714
  have htrace : WordTrace (prefixWord ++ tailWord_1453714) baseStart_1453714 baseEnd_1453714 := by
    simpa [prefixWord, tailWord_1453714, baseEnd_1453714] using wordTrace_append hprefix tailTrace_1453714
  have hstable : (prefixWord ++ tailWord_1453714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453714).length < 2 ^ (prefixWord ++ tailWord_1453714).sum := by decide
  have hdescent : baseEnd_1453714 < baseStart_1453714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453751 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_1453751 : Nat := 118140960795 + 1453751 * 2 ^ 59
def prefixEnd_1453751 : Nat := 4983230072969 + 3 ^ 40 * 1453751 * 2
def baseEnd_1453751 : Nat := 746473014954446926226827

theorem tailTrace_1453751 : CollatzResearch.WordTrace tailWord_1453751 prefixEnd_1453751 746473014954446926226827 := by
  unfold tailWord_1453751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53022654956315882749257107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35348436637543921832838071 53022654956315882749257107)
  ·
    refine ⟨79533982434473824123885661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53022654956315882749257107 79533982434473824123885661)
    ·
      refine ⟨29825243412927684046457123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79533982434473824123885661 29825243412927684046457123)
      ·
        refine ⟨44737865119391526069685685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29825243412927684046457123 44737865119391526069685685)
        ·
          refine ⟨4194174854942955569033033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44737865119391526069685685 4194174854942955569033033)
          ·
            refine ⟨3145631141207216676774775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194174854942955569033033 3145631141207216676774775)
            ·
              refine ⟨4718446711810825015162163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145631141207216676774775 4718446711810825015162163)
              ·
                refine ⟨7077670067716237522743245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718446711810825015162163 7077670067716237522743245)
                ·
                  refine ⟨2654126275393589071028717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7077670067716237522743245 2654126275393589071028717)
                  ·
                    refine ⟨995297353272595901635769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654126275393589071028717 995297353272595901635769)
                    ·
                      refine ⟨746473014954446926226827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995297353272595901635769 746473014954446926226827)
                      ·
                        rfl

theorem cell23_1453751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_1453751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453751 prefixEnd_1453751 := by exact prefixLift 1453751
  have htrace : WordTrace (prefixWord ++ tailWord_1453751) baseStart_1453751 baseEnd_1453751 := by
    simpa [prefixWord, tailWord_1453751, baseEnd_1453751] using wordTrace_append hprefix tailTrace_1453751
  have hstable : (prefixWord ++ tailWord_1453751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453751).length < 2 ^ (prefixWord ++ tailWord_1453751).sum := by decide
  have hdescent : baseEnd_1453751 < baseStart_1453751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453762 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1453762 : Nat := 118140960795 + 1453762 * 2 ^ 59
def prefixEnd_1453762 : Nat := 4983230072969 + 3 ^ 40 * 1453762 * 2
def baseEnd_1453762 : Nat := 746478663241646383189277

theorem tailTrace_1453762 : CollatzResearch.WordTrace tailWord_1453762 prefixEnd_1453762 746478663241646383189277 := by
  unfold tailWord_1453762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255764039819007906976885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35348704106184021085271693 13255764039819007906976885)
  ·
    refine ⟨1242727878733031991279083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13255764039819007906976885 1242727878733031991279083)
    ·
      refine ⟨1864091818099547986918625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242727878733031991279083 1864091818099547986918625)
      ·
        refine ⟨1398068863574660990188969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1864091818099547986918625 1398068863574660990188969)
        ·
          refine ⟨1048551647680995742641727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398068863574660990188969 1048551647680995742641727)
          ·
            refine ⟨1572827471521493613962591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048551647680995742641727 1572827471521493613962591)
            ·
              refine ⟨2359241207282240420943887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572827471521493613962591 2359241207282240420943887)
              ·
                refine ⟨3538861810923360631415831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359241207282240420943887 3538861810923360631415831)
                ·
                  refine ⟨5308292716385040947123747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538861810923360631415831 5308292716385040947123747)
                  ·
                    refine ⟨7962439074577561420685621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308292716385040947123747 7962439074577561420685621)
                    ·
                      refine ⟨746478663241646383189277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7962439074577561420685621 746478663241646383189277)
                      ·
                        rfl

theorem cell23_1453762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1453762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453762 prefixEnd_1453762 := by exact prefixLift 1453762
  have htrace : WordTrace (prefixWord ++ tailWord_1453762) baseStart_1453762 baseEnd_1453762 := by
    simpa [prefixWord, tailWord_1453762, baseEnd_1453762] using wordTrace_append hprefix tailTrace_1453762
  have hstable : (prefixWord ++ tailWord_1453762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453762).length < 2 ^ (prefixWord ++ tailWord_1453762).sum := by decide
  have hdescent : baseEnd_1453762 < baseStart_1453762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453767 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1453767 : Nat := 118140960795 + 1453767 * 2 ^ 59
def prefixEnd_1453767 : Nat := 4983230072969 + 3 ^ 40 * 1453767 * 2
def baseEnd_1453767 : Nat := 746481230644918863626753

theorem tailTrace_1453767 : CollatzResearch.WordTrace tailWord_1453767 prefixEnd_1453767 746481230644918863626753 := by
  unfold tailWord_1453767
  simp only [CollatzResearch.WordTrace]
  refine ⟨53023238524257917481839555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35348825682838611654559703 53023238524257917481839555)
  ·
    refine ⟨79534857786386876222759333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53023238524257917481839555 79534857786386876222759333)
    ·
      refine ⟨14912785834947539291767375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79534857786386876222759333 14912785834947539291767375)
      ·
        refine ⟨22369178752421308937651063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912785834947539291767375 22369178752421308937651063)
        ·
          refine ⟨33553768128631963406476595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22369178752421308937651063 33553768128631963406476595)
          ·
            refine ⟨50330652192947945109714893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33553768128631963406476595 50330652192947945109714893)
            ·
              refine ⟨18873994572355479416143085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50330652192947945109714893 18873994572355479416143085)
              ·
                refine ⟨7077747964633304781053657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18873994572355479416143085 7077747964633304781053657)
                ·
                  refine ⟨5308310973474978585790243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7077747964633304781053657 5308310973474978585790243)
                  ·
                    refine ⟨7962466460212467878685365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5308310973474978585790243 7962466460212467878685365)
                    ·
                      refine ⟨746481230644918863626753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7962466460212467878685365 746481230644918863626753)
                      ·
                        rfl

theorem cell23_1453767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1453767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453767 prefixEnd_1453767 := by exact prefixLift 1453767
  have htrace : WordTrace (prefixWord ++ tailWord_1453767) baseStart_1453767 baseEnd_1453767 := by
    simpa [prefixWord, tailWord_1453767, baseEnd_1453767] using wordTrace_append hprefix tailTrace_1453767
  have hstable : (prefixWord ++ tailWord_1453767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453767).length < 2 ^ (prefixWord ++ tailWord_1453767).sum := by decide
  have hdescent : baseEnd_1453767 < baseStart_1453767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453768 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_1453768 : Nat := 118140960795 + 1453768 * 2 ^ 59
def prefixEnd_1453768 : Nat := 4983230072969 + 3 ^ 40 * 1453768 * 2
def baseEnd_1453768 : Nat := 746481744125573359714249

theorem tailTrace_1453768 : CollatzResearch.WordTrace tailWord_1453768 prefixEnd_1453768 746481744125573359714249 := by
  unfold tailWord_1453768
  simp only [CollatzResearch.WordTrace]
  refine ⟨26511637498627147326312979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35348849998169529768417305 26511637498627147326312979)
  ·
    refine ⟨39767456247940720989469469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26511637498627147326312979 39767456247940720989469469)
    ·
      refine ⟨14912796092977770371051051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39767456247940720989469469 14912796092977770371051051)
      ·
        refine ⟨22369194139466655556576577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14912796092977770371051051 22369194139466655556576577)
        ·
          refine ⟨16776895604599991667432433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22369194139466655556576577 16776895604599991667432433)
          ·
            refine ⟨12582671703449993750574325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16776895604599991667432433 12582671703449993750574325)
            ·
              refine ⟨1179625472198436914116343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12582671703449993750574325 1179625472198436914116343)
              ·
                refine ⟨1769438208297655371174515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179625472198436914116343 1769438208297655371174515)
                ·
                  refine ⟨2654157312446483056761773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769438208297655371174515 2654157312446483056761773)
                  ·
                    refine ⟨995308992167431146285665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2654157312446483056761773 995308992167431146285665)
                    ·
                      refine ⟨746481744125573359714249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995308992167431146285665 746481744125573359714249)
                      ·
                        rfl

theorem cell23_1453768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_1453768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453768 prefixEnd_1453768 := by exact prefixLift 1453768
  have htrace : WordTrace (prefixWord ++ tailWord_1453768) baseStart_1453768 baseEnd_1453768 := by
    simpa [prefixWord, tailWord_1453768, baseEnd_1453768] using wordTrace_append hprefix tailTrace_1453768
  have hstable : (prefixWord ++ tailWord_1453768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453768).length < 2 ^ (prefixWord ++ tailWord_1453768).sum := by decide
  have hdescent : baseEnd_1453768 < baseStart_1453768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453824 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2]
def baseStart_1453824 : Nat := 118140960795 + 1453824 * 2 ^ 59
def prefixEnd_1453824 : Nat := 4983230072969 + 3 ^ 40 * 1453824 * 2
def baseEnd_1453824 : Nat := 746510499042225140613991

theorem tailTrace_1453824 : CollatzResearch.WordTrace tailWord_1453824 prefixEnd_1453824 746510499042225140613991 := by
  unfold tailWord_1453824
  simp only [CollatzResearch.WordTrace]
  refine ⟨26512658742525708108332263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35350211656700944144443017 26512658742525708108332263)
  ·
    refine ⟨39768988113788562162498395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26512658742525708108332263 39768988113788562162498395)
    ·
      refine ⟨59653482170682843243747593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39768988113788562162498395 59653482170682843243747593)
      ·
        refine ⟨44740111628012132432810695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59653482170682843243747593 44740111628012132432810695)
        ·
          refine ⟨67110167442018198649216043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44740111628012132432810695 67110167442018198649216043)
          ·
            refine ⟨100665251163027297973824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67110167442018198649216043 100665251163027297973824065)
            ·
              refine ⟨75498938372270473480368049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100665251163027297973824065 75498938372270473480368049)
              ·
                refine ⟨56624203779202855110276037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75498938372270473480368049 56624203779202855110276037)
                ·
                  refine ⟨10617038208600535333176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56624203779202855110276037 10617038208600535333176757)
                  ·
                    refine ⟨995347332056300187485321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10617038208600535333176757 995347332056300187485321)
                    ·
                      refine ⟨746510499042225140613991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995347332056300187485321 746510499042225140613991)
                      ·
                        rfl

theorem cell23_1453824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_1453824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453824 prefixEnd_1453824 := by exact prefixLift 1453824
  have htrace : WordTrace (prefixWord ++ tailWord_1453824) baseStart_1453824 baseEnd_1453824 := by
    simpa [prefixWord, tailWord_1453824, baseEnd_1453824] using wordTrace_append hprefix tailTrace_1453824
  have hstable : (prefixWord ++ tailWord_1453824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453824).length < 2 ^ (prefixWord ++ tailWord_1453824).sum := by decide
  have hdescent : baseEnd_1453824 < baseStart_1453824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453827 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1453827 : Nat := 118140960795 + 1453827 * 2 ^ 59
def prefixEnd_1453827 : Nat := 4983230072969 + 3 ^ 40 * 1453827 * 2
def baseEnd_1453827 : Nat := 746512039484188628876477

theorem tailTrace_1453827 : CollatzResearch.WordTrace tailWord_1453827 prefixEnd_1453827 746512039484188628876477 := by
  unfold tailWord_1453827
  simp only [CollatzResearch.WordTrace]
  refine ⟨53025426904040547729023735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35350284602693698486015823 53025426904040547729023735)
  ·
    refine ⟨79538140356060821593535603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53025426904040547729023735 79538140356060821593535603)
    ·
      refine ⟨119307210534091232390303405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79538140356060821593535603 119307210534091232390303405)
      ·
        refine ⟨44740203950284212146363777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119307210534091232390303405 44740203950284212146363777)
        ·
          refine ⟨33555152962713159109772833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44740203950284212146363777 33555152962713159109772833)
          ·
            refine ⟨25166364722034869332329625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33555152962713159109772833 25166364722034869332329625)
            ·
              refine ⟨18874773541526151999247219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25166364722034869332329625 18874773541526151999247219)
              ·
                refine ⟨28312160312289227998870829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18874773541526151999247219 28312160312289227998870829)
                ·
                  refine ⟨10617060117108460499576561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28312160312289227998870829 10617060117108460499576561)
                  ·
                    refine ⟨7962795087831345374682421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10617060117108460499576561 7962795087831345374682421)
                    ·
                      refine ⟨746512039484188628876477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7962795087831345374682421 746512039484188628876477)
                      ·
                        rfl

theorem cell23_1453827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1453827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453827 prefixEnd_1453827 := by exact prefixLift 1453827
  have htrace : WordTrace (prefixWord ++ tailWord_1453827) baseStart_1453827 baseEnd_1453827 := by
    simpa [prefixWord, tailWord_1453827, baseEnd_1453827] using wordTrace_append hprefix tailTrace_1453827
  have hstable : (prefixWord ++ tailWord_1453827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453827).length < 2 ^ (prefixWord ++ tailWord_1453827).sum := by decide
  have hdescent : baseEnd_1453827 < baseStart_1453827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453891 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3]
def baseStart_1453891 : Nat := 118140960795 + 1453891 * 2 ^ 59
def prefixEnd_1453891 : Nat := 4983230072969 + 3 ^ 40 * 1453891 * 2
def baseEnd_1453891 : Nat := 746544902246076378476183

theorem tailTrace_1453891 : CollatzResearch.WordTrace tailWord_1453891 prefixEnd_1453891 746544902246076378476183 := by
  unfold tailWord_1453891
  simp only [CollatzResearch.WordTrace]
  refine ⟨53027761175808686659353527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35351840783872457772902351 53027761175808686659353527)
  ·
    refine ⟨79541641763713029989030291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53027761175808686659353527 79541641763713029989030291)
    ·
      refine ⟨119312462645569544983545437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79541641763713029989030291 119312462645569544983545437)
      ·
        refine ⟨44742173492088579368829539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119312462645569544983545437 44742173492088579368829539)
        ·
          refine ⟨67113260238132869053244309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44742173492088579368829539 67113260238132869053244309)
          ·
            refine ⟨3145934073662478236870827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67113260238132869053244309 3145934073662478236870827)
            ·
              refine ⟨4718901110493717355306241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145934073662478236870827 4718901110493717355306241)
              ·
                refine ⟨3539175832870288016479681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718901110493717355306241 3539175832870288016479681)
                ·
                  refine ⟨2654381874652716012359761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3539175832870288016479681 2654381874652716012359761)
                  ·
                    refine ⟨1990786405989537009269821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2654381874652716012359761 1990786405989537009269821)
                    ·
                      refine ⟨746544902246076378476183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990786405989537009269821 746544902246076378476183)
                      ·
                        rfl

theorem cell23_1453891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_1453891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453891 prefixEnd_1453891 := by exact prefixLift 1453891
  have htrace : WordTrace (prefixWord ++ tailWord_1453891) baseStart_1453891 baseEnd_1453891 := by
    simpa [prefixWord, tailWord_1453891, baseEnd_1453891] using wordTrace_append hprefix tailTrace_1453891
  have hstable : (prefixWord ++ tailWord_1453891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453891).length < 2 ^ (prefixWord ++ tailWord_1453891).sum := by decide
  have hdescent : baseEnd_1453891 < baseStart_1453891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453907 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 1, 11]
def baseStart_1453907 : Nat := 118140960795 + 1453907 * 2 ^ 59
def prefixEnd_1453907 : Nat := 4983230072969 + 3 ^ 40 * 1453907 * 2
def baseEnd_1453907 : Nat := 248851039312182771958703

theorem tailTrace_1453907 : CollatzResearch.WordTrace tailWord_1453907 prefixEnd_1453907 248851039312182771958703 := by
  unfold tailWord_1453907
  simp only [CollatzResearch.WordTrace]
  refine ⟨53028344743750721391935975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35352229829167147594623983 53028344743750721391935975)
  ·
    refine ⟨79542517115626082087903963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53028344743750721391935975 79542517115626082087903963)
    ·
      refine ⟨119313775673439123131855945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79542517115626082087903963 119313775673439123131855945)
      ·
        refine ⟨89485331755079342348891959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119313775673439123131855945 89485331755079342348891959)
        ·
          refine ⟨134227997632619013523337939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89485331755079342348891959 134227997632619013523337939)
          ·
            refine ⟨201341996448928520285006909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134227997632619013523337939 201341996448928520285006909)
            ·
              refine ⟨75503248668348195106877591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201341996448928520285006909 75503248668348195106877591)
              ·
                refine ⟨113254873002522292660316387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75503248668348195106877591 113254873002522292660316387)
                ·
                  refine ⟨169882309503783438990474581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113254873002522292660316387 169882309503783438990474581)
                  ·
                    refine ⟨248851039312182771958703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 169882309503783438990474581 248851039312182771958703)
                    ·
                      rfl

theorem cell23_1453907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_1453907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453907 prefixEnd_1453907 := by exact prefixLift 1453907
  have htrace : WordTrace (prefixWord ++ tailWord_1453907) baseStart_1453907 baseEnd_1453907 := by
    simpa [prefixWord, tailWord_1453907, baseEnd_1453907] using wordTrace_append hprefix tailTrace_1453907
  have hstable : (prefixWord ++ tailWord_1453907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453907).length < 2 ^ (prefixWord ++ tailWord_1453907).sum := by decide
  have hdescent : baseEnd_1453907 < baseStart_1453907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453911 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 6]
def baseStart_1453911 : Nat := 118140960795 + 1453911 * 2 ^ 59
def prefixEnd_1453911 : Nat := 4983230072969 + 3 ^ 40 * 1453911 * 2
def baseEnd_1453911 : Nat := 82950574651018477802899

theorem tailTrace_1453911 : CollatzResearch.WordTrace tailWord_1453911 prefixEnd_1453911 82950574651018477802899 := by
  unfold tailWord_1453911
  simp only [CollatzResearch.WordTrace]
  refine ⟨53028490635736230075081587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35352327090490820050054391 53028490635736230075081587)
  ·
    refine ⟨79542735953604345112622381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53028490635736230075081587 79542735953604345112622381)
    ·
      refine ⟨29828525982601629417233393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79542735953604345112622381 29828525982601629417233393)
      ·
        refine ⟨22371394486951222062925045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29828525982601629417233393 22371394486951222062925045)
        ·
          refine ⟨2097318233151677068399223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22371394486951222062925045 2097318233151677068399223)
          ·
            refine ⟨3145977349727515602598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097318233151677068399223 3145977349727515602598835)
            ·
              refine ⟨4718966024591273403898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145977349727515602598835 4718966024591273403898253)
              ·
                refine ⟨1769612259221727526461845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4718966024591273403898253 1769612259221727526461845)
                ·
                  refine ⟨82950574651018477802899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1769612259221727526461845 82950574651018477802899)
                  ·
                    rfl

theorem cell23_1453911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 6].length) (baseStart_1453911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453911 prefixEnd_1453911 := by exact prefixLift 1453911
  have htrace : WordTrace (prefixWord ++ tailWord_1453911) baseStart_1453911 baseEnd_1453911 := by
    simpa [prefixWord, tailWord_1453911, baseEnd_1453911] using wordTrace_append hprefix tailTrace_1453911
  have hstable : (prefixWord ++ tailWord_1453911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453911).length < 2 ^ (prefixWord ++ tailWord_1453911).sum := by decide
  have hdescent : baseEnd_1453911 < baseStart_1453911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453921 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_1453921 : Nat := 118140960795 + 1453921 * 2 ^ 59
def prefixEnd_1453921 : Nat := 4983230072969 + 3 ^ 40 * 1453921 * 2
def baseEnd_1453921 : Nat := 746560306665711261101045

theorem tailTrace_1453921 : CollatzResearch.WordTrace tailWord_1453921 prefixEnd_1453921 746560306665711261101045 := by
  unfold tailWord_1453921
  simp only [CollatzResearch.WordTrace]
  refine ⟨53028855365700001782945617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35352570243800001188630411 53028855365700001782945617)
  ·
    refine ⟨39771641524275001337209213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53028855365700001782945617 39771641524275001337209213)
    ·
      refine ⟨14914365571603125501453455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39771641524275001337209213 14914365571603125501453455)
      ·
        refine ⟨22371548357404688252180183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14914365571603125501453455 22371548357404688252180183)
        ·
          refine ⟨33557322536107032378270275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22371548357404688252180183 33557322536107032378270275)
          ·
            refine ⟨50335983804160548567405413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33557322536107032378270275 50335983804160548567405413)
            ·
              refine ⟨9437996963280102856388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50335983804160548567405413 9437996963280102856388515)
              ·
                refine ⟨14156995444920154284582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9437996963280102856388515 14156995444920154284582773)
                ·
                  refine ⟨1327218322961264464179635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14156995444920154284582773 1327218322961264464179635)
                  ·
                    refine ⟨1990827484441896696269453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327218322961264464179635 1990827484441896696269453)
                    ·
                      refine ⟨746560306665711261101045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990827484441896696269453 746560306665711261101045)
                      ·
                        rfl

theorem cell23_1453921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_1453921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453921 prefixEnd_1453921 := by exact prefixLift 1453921
  have htrace : WordTrace (prefixWord ++ tailWord_1453921) baseStart_1453921 baseEnd_1453921 := by
    simpa [prefixWord, tailWord_1453921, baseEnd_1453921] using wordTrace_append hprefix tailTrace_1453921
  have hstable : (prefixWord ++ tailWord_1453921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453921).length < 2 ^ (prefixWord ++ tailWord_1453921).sum := by decide
  have hdescent : baseEnd_1453921 < baseStart_1453921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453955 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 1, 1, 3]
def baseStart_1453955 : Nat := 118140960795 + 1453955 * 2 ^ 59
def prefixEnd_1453955 : Nat := 4983230072969 + 3 ^ 40 * 1453955 * 2
def baseEnd_1453955 : Nat := 746577765007964128075889

theorem tailTrace_1453955 : CollatzResearch.WordTrace tailWord_1453955 prefixEnd_1453955 746577765007964128075889 := by
  unfold tailWord_1453955
  simp only [CollatzResearch.WordTrace]
  refine ⟨53030095447576825589683319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35353396965051217059788879 53030095447576825589683319)
  ·
    refine ⟨79545143171365238384524979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53030095447576825589683319 79545143171365238384524979)
    ·
      refine ⟨119317714757047857576787469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79545143171365238384524979 119317714757047857576787469)
      ·
        refine ⟨44744143033892946591295301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119317714757047857576787469 44744143033892946591295301)
        ·
          refine ⟨8389526818854927485867869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44744143033892946591295301 8389526818854927485867869)
          ·
            refine ⟨3146072557070597807200451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8389526818854927485867869 3146072557070597807200451)
            ·
              refine ⟨4719108835605896710800677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146072557070597807200451 4719108835605896710800677)
              ·
                refine ⟨884832906676105633275127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4719108835605896710800677 884832906676105633275127)
                ·
                  refine ⟨1327249360014158449912691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884832906676105633275127 1327249360014158449912691)
                  ·
                    refine ⟨1990874040021237674869037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327249360014158449912691 1990874040021237674869037)
                    ·
                      refine ⟨746577765007964128075889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990874040021237674869037 746577765007964128075889)
                      ·
                        rfl

theorem cell23_1453955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_1453955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453955 prefixEnd_1453955 := by exact prefixLift 1453955
  have htrace : WordTrace (prefixWord ++ tailWord_1453955) baseStart_1453955 baseEnd_1453955 := by
    simpa [prefixWord, tailWord_1453955, baseEnd_1453955] using wordTrace_append hprefix tailTrace_1453955
  have hstable : (prefixWord ++ tailWord_1453955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453955).length < 2 ^ (prefixWord ++ tailWord_1453955).sum := by decide
  have hdescent : baseEnd_1453955 < baseStart_1453955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1453964 : Nat := 118140960795 + 1453964 * 2 ^ 59
def prefixEnd_1453964 : Nat := 4983230072969 + 3 ^ 40 * 1453964 * 2
def baseEnd_1453964 : Nat := 746582386333854592863347

theorem tailTrace_1453964 : CollatzResearch.WordTrace tailWord_1453964 prefixEnd_1453964 746582386333854592863347 := by
  unfold tailWord_1453964
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515211852272110063380473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35353615803029480084507297 26515211852272110063380473)
  ·
    refine ⟨19886408889204082547535355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26515211852272110063380473 19886408889204082547535355)
    ·
      refine ⟨29829613333806123821303033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19886408889204082547535355 29829613333806123821303033)
      ·
        refine ⟨22372210000354592865977275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29829613333806123821303033 22372210000354592865977275)
        ·
          refine ⟨33558315000531889298965913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22372210000354592865977275 33558315000531889298965913)
          ·
            refine ⟨25168736250398916974224435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33558315000531889298965913 25168736250398916974224435)
            ·
              refine ⟨37753104375598375461336653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25168736250398916974224435 37753104375598375461336653)
              ·
                refine ⟨14157414140849390798001245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37753104375598375461336653 14157414140849390798001245)
                ·
                  refine ⟨5309030302818521549250467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14157414140849390798001245 5309030302818521549250467)
                  ·
                    refine ⟨7963545454227782323875701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5309030302818521549250467 7963545454227782323875701)
                    ·
                      refine ⟨746582386333854592863347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7963545454227782323875701 746582386333854592863347)
                      ·
                        rfl

theorem cell23_1453964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1453964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453964 prefixEnd_1453964 := by exact prefixLift 1453964
  have htrace : WordTrace (prefixWord ++ tailWord_1453964) baseStart_1453964 baseEnd_1453964 := by
    simpa [prefixWord, tailWord_1453964, baseEnd_1453964] using wordTrace_append hprefix tailTrace_1453964
  have hstable : (prefixWord ++ tailWord_1453964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453964).length < 2 ^ (prefixWord ++ tailWord_1453964).sum := by decide
  have hdescent : baseEnd_1453964 < baseStart_1453964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453982 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1453982 : Nat := 118140960795 + 1453982 * 2 ^ 59
def prefixEnd_1453982 : Nat := 4983230072969 + 3 ^ 40 * 1453982 * 2
def baseEnd_1453982 : Nat := 746591628985635522438265

theorem tailTrace_1453982 : CollatzResearch.WordTrace tailWord_1453982 prefixEnd_1453982 746591628985635522438265 := by
  unfold tailWord_1453982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628885027309876150114525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35354053478986006133944133 6628885027309876150114525)
  ·
    refine ⟨2485831885241203556292947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6628885027309876150114525 2485831885241203556292947)
    ·
      refine ⟨3728747827861805334439421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485831885241203556292947 3728747827861805334439421)
      ·
        refine ⟨1398280435448177000414783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3728747827861805334439421 1398280435448177000414783)
        ·
          refine ⟨2097420653172265500622175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398280435448177000414783 2097420653172265500622175)
          ·
            refine ⟨3146130979758398250933263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097420653172265500622175 3146130979758398250933263)
            ·
              refine ⟨4719196469637597376399895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146130979758398250933263 4719196469637597376399895)
              ·
                refine ⟨7078794704456396064599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719196469637597376399895 7078794704456396064599843)
                ·
                  refine ⟨10618192056684594096899765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7078794704456396064599843 10618192056684594096899765)
                  ·
                    refine ⟨995455505314180696584353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10618192056684594096899765 995455505314180696584353)
                    ·
                      refine ⟨746591628985635522438265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995455505314180696584353 746591628985635522438265)
                      ·
                        rfl

theorem cell23_1453982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1453982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1453982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1453982 prefixEnd_1453982 := by exact prefixLift 1453982
  have htrace : WordTrace (prefixWord ++ tailWord_1453982) baseStart_1453982 baseEnd_1453982 := by
    simpa [prefixWord, tailWord_1453982, baseEnd_1453982] using wordTrace_append hprefix tailTrace_1453982
  have hstable : (prefixWord ++ tailWord_1453982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453982).length < 2 ^ (prefixWord ++ tailWord_1453982).sum := by decide
  have hdescent : baseEnd_1453982 < baseStart_1453982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454005 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1454005 : Nat := 118140960795 + 1454005 * 2 ^ 59
def prefixEnd_1454005 : Nat := 4983230072969 + 3 ^ 40 * 1454005 * 2
def baseEnd_1454005 : Nat := 248867813013562977483553

theorem tailTrace_1454005 : CollatzResearch.WordTrace tailWord_1454005 prefixEnd_1454005 248867813013562977483553 := by
  unfold tailWord_1454005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53031919097395684129003469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35354612731597122752668979 53031919097395684129003469)
  ·
    refine ⟨19886969661523381548376301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53031919097395684129003469 19886969661523381548376301)
    ·
      refine ⟨7457613623071268080641113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19886969661523381548376301 7457613623071268080641113)
      ·
        refine ⟨5593210217303451060480835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7457613623071268080641113 5593210217303451060480835)
        ·
          refine ⟨8389815325955176590721253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593210217303451060480835 8389815325955176590721253)
          ·
            refine ⟨1573090373616595610760235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8389815325955176590721253 1573090373616595610760235)
            ·
              refine ⟨2359635560424893416140353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573090373616595610760235 2359635560424893416140353)
              ·
                refine ⟨1769726670318670062105265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359635560424893416140353 1769726670318670062105265)
                ·
                  refine ⟨1327295002739002546578949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769726670318670062105265 1327295002739002546578949)
                  ·
                    refine ⟨248867813013562977483553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327295002739002546578949 248867813013562977483553)
                    ·
                      rfl

theorem cell23_1454005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1454005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454005 prefixEnd_1454005 := by exact prefixLift 1454005
  have htrace : WordTrace (prefixWord ++ tailWord_1454005) baseStart_1454005 baseEnd_1454005 := by
    simpa [prefixWord, tailWord_1454005, baseEnd_1454005] using wordTrace_append hprefix tailTrace_1454005
  have hstable : (prefixWord ++ tailWord_1454005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454005).length < 2 ^ (prefixWord ++ tailWord_1454005).sum := by decide
  have hdescent : baseEnd_1454005 < baseStart_1454005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454021 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_1454021 : Nat := 118140960795 + 1454021 * 2 ^ 59
def prefixEnd_1454021 : Nat := 4983230072969 + 3 ^ 40 * 1454021 * 2
def baseEnd_1454021 : Nat := 746611654731160869850585

theorem tailTrace_1454021 : CollatzResearch.WordTrace tailWord_1454021 prefixEnd_1454021 746611654731160869850585 := by
  unfold tailWord_1454021
  simp only [CollatzResearch.WordTrace]
  refine ⟨53032502665337718861585917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35355001776891812574390611 53032502665337718861585917)
  ·
    refine ⟨19887188499501644573094719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53032502665337718861585917 19887188499501644573094719)
    ·
      refine ⟨29830782749252466859642079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19887188499501644573094719 29830782749252466859642079)
      ·
        refine ⟨44746174123878700289463119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29830782749252466859642079 44746174123878700289463119)
        ·
          refine ⟨67119261185818050434194679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44746174123878700289463119 67119261185818050434194679)
          ·
            refine ⟨100678891778727075651292019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67119261185818050434194679 100678891778727075651292019)
            ·
              refine ⟨151018337668090613476938029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100678891778727075651292019 151018337668090613476938029)
              ·
                refine ⟨56631876625533980053851761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151018337668090613476938029 56631876625533980053851761)
                ·
                  refine ⟨42473907469150485040388821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56631876625533980053851761 42473907469150485040388821)
                  ·
                    refine ⟨995482206308214493134113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42473907469150485040388821 995482206308214493134113)
                    ·
                      refine ⟨746611654731160869850585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995482206308214493134113 746611654731160869850585)
                      ·
                        rfl

theorem cell23_1454021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_1454021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454021 prefixEnd_1454021 := by exact prefixLift 1454021
  have htrace : WordTrace (prefixWord ++ tailWord_1454021) baseStart_1454021 baseEnd_1454021 := by
    simpa [prefixWord, tailWord_1454021, baseEnd_1454021] using wordTrace_append hprefix tailTrace_1454021
  have hstable : (prefixWord ++ tailWord_1454021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454021).length < 2 ^ (prefixWord ++ tailWord_1454021).sum := by decide
  have hdescent : baseEnd_1454021 < baseStart_1454021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454028 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1454028 : Nat := 118140960795 + 1454028 * 2 ^ 59
def prefixEnd_1454028 : Nat := 4983230072969 + 3 ^ 40 * 1454028 * 2
def baseEnd_1454028 : Nat := 746615249095742342463053

theorem tailTrace_1454028 : CollatzResearch.WordTrace tailWord_1454028 prefixEnd_1454028 746615249095742342463053 := by
  unfold tailWord_1454028
  simp only [CollatzResearch.WordTrace]
  refine ⟨26516378988156179528545369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35355171984208239371393825 26516378988156179528545369)
  ·
    refine ⟨19887284241117134646409027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26516378988156179528545369 19887284241117134646409027)
    ·
      refine ⟨29830926361675701969613541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19887284241117134646409027 29830926361675701969613541)
      ·
        refine ⟨5593298692814194119302539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29830926361675701969613541 5593298692814194119302539)
        ·
          refine ⟨8389948039221291178953809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593298692814194119302539 8389948039221291178953809)
          ·
            refine ⟨6292461029415968384215357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8389948039221291178953809 6292461029415968384215357)
            ·
              refine ⟨2359672886030988144080759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6292461029415968384215357 2359672886030988144080759)
              ·
                refine ⟨3539509329046482216121139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359672886030988144080759 3539509329046482216121139)
                ·
                  refine ⟨5309263993569723324181709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539509329046482216121139 5309263993569723324181709)
                  ·
                    refine ⟨1990973997588646246568141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5309263993569723324181709 1990973997588646246568141)
                    ·
                      refine ⟨746615249095742342463053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1990973997588646246568141 746615249095742342463053)
                      ·
                        rfl

theorem cell23_1454028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1454028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454028 prefixEnd_1454028 := by exact prefixLift 1454028
  have htrace : WordTrace (prefixWord ++ tailWord_1454028) baseStart_1454028 baseEnd_1454028 := by
    simpa [prefixWord, tailWord_1454028, baseEnd_1454028] using wordTrace_append hprefix tailTrace_1454028
  have hstable : (prefixWord ++ tailWord_1454028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454028).length < 2 ^ (prefixWord ++ tailWord_1454028).sum := by decide
  have hdescent : baseEnd_1454028 < baseStart_1454028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454081 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1454081 : Nat := 118140960795 + 1454081 * 2 ^ 59
def prefixEnd_1454081 : Nat := 4983230072969 + 3 ^ 40 * 1454081 * 2
def baseEnd_1454081 : Nat := 746642463570430635100309

theorem tailTrace_1454081 : CollatzResearch.WordTrace tailWord_1454081 prefixEnd_1454081 746642463570430635100309 := by
  unfold tailWord_1454081
  simp only [CollatzResearch.WordTrace]
  refine ⟨53034691045120349108770097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35356460696746899405846731 53034691045120349108770097)
  ·
    refine ⟨39776018283840261831577573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53034691045120349108770097 39776018283840261831577573)
    ·
      refine ⟨7458003428220049093420795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39776018283840261831577573 7458003428220049093420795)
      ·
        refine ⟨11187005142330073640131193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7458003428220049093420795 11187005142330073640131193)
        ·
          refine ⟨8390253856747555230098395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11187005142330073640131193 8390253856747555230098395)
          ·
            refine ⟨12585380785121332845147593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8390253856747555230098395 12585380785121332845147593)
            ·
              refine ⟨9439035588840999633860695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12585380785121332845147593 9439035588840999633860695)
              ·
                refine ⟨14158553383261499450791043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439035588840999633860695 14158553383261499450791043)
                ·
                  refine ⟨21237830074892249176186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14158553383261499450791043 21237830074892249176186565)
                  ·
                    refine ⟨3982093139042296720534981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21237830074892249176186565 3982093139042296720534981)
                    ·
                      refine ⟨746642463570430635100309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3982093139042296720534981 746642463570430635100309)
                      ·
                        rfl

theorem cell23_1454081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1454081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454081 prefixEnd_1454081 := by exact prefixLift 1454081
  have htrace : WordTrace (prefixWord ++ tailWord_1454081) baseStart_1454081 baseEnd_1454081 := by
    simpa [prefixWord, tailWord_1454081, baseEnd_1454081] using wordTrace_append hprefix tailTrace_1454081
  have hstable : (prefixWord ++ tailWord_1454081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454081).length < 2 ^ (prefixWord ++ tailWord_1454081).sum := by decide
  have hdescent : baseEnd_1454081 < baseStart_1454081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454128 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2]
def baseStart_1454128 : Nat := 118140960795 + 1454128 * 2 ^ 59
def prefixEnd_1454128 : Nat := 4983230072969 + 3 ^ 40 * 1454128 * 2
def baseEnd_1454128 : Nat := 746666597161191951212593

theorem tailTrace_1454128 : CollatzResearch.WordTrace tailWord_1454128 prefixEnd_1454128 746666597161191951212593 := by
  unfold tailWord_1454128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518202637975038067865519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35357603517300050757154025 26518202637975038067865519)
  ·
    refine ⟨39777303956962557101798279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26518202637975038067865519 39777303956962557101798279)
    ·
      refine ⟨59665955935443835652697419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39777303956962557101798279 59665955935443835652697419)
      ·
        refine ⟨89498933903165753479046129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59665955935443835652697419 89498933903165753479046129)
        ·
          refine ⟨67124200427374315109284597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89498933903165753479046129 67124200427374315109284597)
          ·
            refine ⟨6292893790066342041495431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67124200427374315109284597 6292893790066342041495431)
            ·
              refine ⟨9439340685099513062243147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292893790066342041495431 9439340685099513062243147)
              ·
                refine ⟨14159011027649269593364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9439340685099513062243147 14159011027649269593364721)
                ·
                  refine ⟨10619258270736952195023541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14159011027649269593364721 10619258270736952195023541)
                  ·
                    refine ⟨995555462881589268283457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10619258270736952195023541 995555462881589268283457)
                    ·
                      refine ⟨746666597161191951212593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995555462881589268283457 746666597161191951212593)
                      ·
                        rfl

theorem cell23_1454128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 5, 2].length) (baseStart_1454128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454128 prefixEnd_1454128 := by exact prefixLift 1454128
  have htrace : WordTrace (prefixWord ++ tailWord_1454128) baseStart_1454128 baseEnd_1454128 := by
    simpa [prefixWord, tailWord_1454128, baseEnd_1454128] using wordTrace_append hprefix tailTrace_1454128
  have hstable : (prefixWord ++ tailWord_1454128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454128).length < 2 ^ (prefixWord ++ tailWord_1454128).sum := by decide
  have hdescent : baseEnd_1454128 < baseStart_1454128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454131 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_1454131 : Nat := 118140960795 + 1454131 * 2 ^ 59
def prefixEnd_1454131 : Nat := 4983230072969 + 3 ^ 40 * 1454131 * 2
def baseEnd_1454131 : Nat := 746668137603155439475079

theorem tailTrace_1454131 : CollatzResearch.WordTrace tailWord_1454131 prefixEnd_1454131 746668137603155439475079 := by
  unfold tailWord_1454131
  simp only [CollatzResearch.WordTrace]
  refine ⟨53036514694939207648090247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35357676463292805098726831 53036514694939207648090247)
  ·
    refine ⟨79554772042408811472135371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53036514694939207648090247 79554772042408811472135371)
    ·
      refine ⟨119332158063613217208203057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79554772042408811472135371 119332158063613217208203057)
      ·
        refine ⟨89499118547709912906152293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119332158063613217208203057 89499118547709912906152293)
        ·
          refine ⟨16781084727695608669903555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89499118547709912906152293 16781084727695608669903555)
          ·
            refine ⟨25171627091543413004855333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16781084727695608669903555 25171627091543413004855333)
            ·
              refine ⟨4719680079664389938410375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25171627091543413004855333 4719680079664389938410375)
              ·
                refine ⟨7079520119496584907615563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719680079664389938410375 7079520119496584907615563)
                ·
                  refine ⟨10619280179244877361423345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7079520119496584907615563 10619280179244877361423345)
                  ·
                    refine ⟨7964460134433658021067509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10619280179244877361423345 7964460134433658021067509)
                    ·
                      refine ⟨746668137603155439475079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7964460134433658021067509 746668137603155439475079)
                      ·
                        rfl

theorem cell23_1454131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_1454131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454131 prefixEnd_1454131 := by exact prefixLift 1454131
  have htrace : WordTrace (prefixWord ++ tailWord_1454131) baseStart_1454131 baseEnd_1454131 := by
    simpa [prefixWord, tailWord_1454131, baseEnd_1454131] using wordTrace_append hprefix tailTrace_1454131
  have hstable : (prefixWord ++ tailWord_1454131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454131).length < 2 ^ (prefixWord ++ tailWord_1454131).sum := by decide
  have hdescent : baseEnd_1454131 < baseStart_1454131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454158 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1454158 : Nat := 118140960795 + 1454158 * 2 ^ 59
def prefixEnd_1454158 : Nat := 4983230072969 + 3 ^ 40 * 1454158 * 2
def baseEnd_1454158 : Nat := 746682001580826833837455

theorem tailTrace_1454158 : CollatzResearch.WordTrace tailWord_1454158 prefixEnd_1454158 746682001580826833837455 := by
  unfold tailWord_1454158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629687433230173907415391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35358332977227594172882085 6629687433230173907415391)
  ·
    refine ⟨9944531149845260861123087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629687433230173907415391 9944531149845260861123087)
    ·
      refine ⟨14916796724767891291684631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944531149845260861123087 14916796724767891291684631)
      ·
        refine ⟨22375195087151836937526947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14916796724767891291684631 22375195087151836937526947)
        ·
          refine ⟨33562792630727755406290421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22375195087151836937526947 33562792630727755406290421)
          ·
            refine ⟨3146511809130727069339727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33562792630727755406290421 3146511809130727069339727)
            ·
              refine ⟨4719767713696090604009591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146511809130727069339727 4719767713696090604009591)
              ·
                refine ⟨7079651570544135906014387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4719767713696090604009591 7079651570544135906014387)
                ·
                  refine ⟨10619477355816203859021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7079651570544135906014387 10619477355816203859021581)
                  ·
                    refine ⟨3982304008431076447133093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10619477355816203859021581 3982304008431076447133093)
                    ·
                      refine ⟨746682001580826833837455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3982304008431076447133093 746682001580826833837455)
                      ·
                        rfl

theorem cell23_1454158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1454158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454158 prefixEnd_1454158 := by exact prefixLift 1454158
  have htrace : WordTrace (prefixWord ++ tailWord_1454158) baseStart_1454158 baseEnd_1454158 := by
    simpa [prefixWord, tailWord_1454158, baseEnd_1454158] using wordTrace_append hprefix tailTrace_1454158
  have hstable : (prefixWord ++ tailWord_1454158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454158).length < 2 ^ (prefixWord ++ tailWord_1454158).sum := by decide
  have hdescent : baseEnd_1454158 < baseStart_1454158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454185 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 1, 4]
def baseStart_1454185 : Nat := 118140960795 + 1454185 * 2 ^ 59
def prefixEnd_1454185 : Nat := 4983230072969 + 3 ^ 40 * 1454185 * 2
def baseEnd_1454185 : Nat := 248898621852832742733277

theorem tailTrace_1454185 : CollatzResearch.WordTrace tailWord_1454185 prefixEnd_1454185 248898621852832742733277 := by
  unfold tailWord_1454185
  simp only [CollatzResearch.WordTrace]
  refine ⟨53038484236743574870556009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35358989491162383247037339 53038484236743574870556009)
  ·
    refine ⟨39778863177557681152917007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53038484236743574870556009 39778863177557681152917007)
    ·
      refine ⟨59668294766336521729375511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39778863177557681152917007 59668294766336521729375511)
      ·
        refine ⟨89502442149504782594063267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59668294766336521729375511 89502442149504782594063267)
        ·
          refine ⟨134253663224257173891094901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89502442149504782594063267 134253663224257173891094901)
          ·
            refine ⟨12586280927274110052290147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134253663224257173891094901 12586280927274110052290147)
            ·
              refine ⟨18879421390911165078435221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12586280927274110052290147 18879421390911165078435221)
              ·
                refine ⟨884972877698960863051651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18879421390911165078435221 884972877698960863051651)
                ·
                  refine ⟨1327459316548441294577477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884972877698960863051651 1327459316548441294577477)
                  ·
                    refine ⟨248898621852832742733277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327459316548441294577477 248898621852832742733277)
                    ·
                      rfl

theorem cell23_1454185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_1454185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454185 prefixEnd_1454185 := by exact prefixLift 1454185
  have htrace : WordTrace (prefixWord ++ tailWord_1454185) baseStart_1454185 baseEnd_1454185 := by
    simpa [prefixWord, tailWord_1454185, baseEnd_1454185] using wordTrace_append hprefix tailTrace_1454185
  have hstable : (prefixWord ++ tailWord_1454185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454185).length < 2 ^ (prefixWord ++ tailWord_1454185).sum := by decide
  have hdescent : baseEnd_1454185 < baseStart_1454185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454251 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_1454251 : Nat := 118140960795 + 1454251 * 2 ^ 59
def prefixEnd_1454251 : Nat := 4983230072969 + 3 ^ 40 * 1454251 * 2
def baseEnd_1454251 : Nat := 746729755281694969974527

theorem tailTrace_1454251 : CollatzResearch.WordTrace tailWord_1454251 prefixEnd_1454251 746729755281694969974527 := by
  unfold tailWord_1454251
  simp only [CollatzResearch.WordTrace]
  refine ⟨53040891454504468142458607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35360594303002978761639071 53040891454504468142458607)
  ·
    refine ⟨79561337181756702213687911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53040891454504468142458607 79561337181756702213687911)
    ·
      refine ⟨119342005772635053320531867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79561337181756702213687911 119342005772635053320531867)
      ·
        refine ⟨179013008658952579980797801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119342005772635053320531867 179013008658952579980797801)
        ·
          refine ⟨134259756494214434985598351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179013008658952579980797801 134259756494214434985598351)
          ·
            refine ⟨201389634741321652478397527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134259756494214434985598351 201389634741321652478397527)
            ·
              refine ⟨302084452111982478717596291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201389634741321652478397527 302084452111982478717596291)
              ·
                refine ⟨453126678167973718076394437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302084452111982478717596291 453126678167973718076394437)
                ·
                  refine ⟨84961252156495072139323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453126678167973718076394437 84961252156495072139323957)
                  ·
                    refine ⟨7965117389671413013061621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84961252156495072139323957 7965117389671413013061621)
                    ·
                      refine ⟨746729755281694969974527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7965117389671413013061621 746729755281694969974527)
                      ·
                        rfl

theorem cell23_1454251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_1454251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454251 prefixEnd_1454251 := by exact prefixLift 1454251
  have htrace : WordTrace (prefixWord ++ tailWord_1454251) baseStart_1454251 baseEnd_1454251 := by
    simpa [prefixWord, tailWord_1454251, baseEnd_1454251] using wordTrace_append hprefix tailTrace_1454251
  have hstable : (prefixWord ++ tailWord_1454251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454251).length < 2 ^ (prefixWord ++ tailWord_1454251).sum := by decide
  have hdescent : baseEnd_1454251 < baseStart_1454251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454258 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1454258 : Nat := 118140960795 + 1454258 * 2 ^ 59
def prefixEnd_1454258 : Nat := 4983230072969 + 3 ^ 40 * 1454258 * 2
def baseEnd_1454258 : Nat := 248911116548758814195665

theorem tailTrace_1454258 : CollatzResearch.WordTrace tailWord_1454258 prefixEnd_1454258 248911116548758814195665 := by
  unfold tailWord_1454258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260286691369777084490857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35360764510319405558642285 13260286691369777084490857)
  ·
    refine ⟨9945215018527332813368143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13260286691369777084490857 9945215018527332813368143)
    ·
      refine ⟨14917822527790999220052215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9945215018527332813368143 14917822527790999220052215)
      ·
        refine ⟨22376733791686498830078323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14917822527790999220052215 22376733791686498830078323)
        ·
          refine ⟨33565100687529748245117485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22376733791686498830078323 33565100687529748245117485)
          ·
            refine ⟨12586912757823655591919057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33565100687529748245117485 12586912757823655591919057)
            ·
              refine ⟨9440184568367741693939293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586912757823655591919057 9440184568367741693939293)
              ·
                refine ⟨3540069213137903135227235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9440184568367741693939293 3540069213137903135227235)
                ·
                  refine ⟨5310103819706854702840853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540069213137903135227235 5310103819706854702840853)
                  ·
                    refine ⟨248911116548758814195665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5310103819706854702840853 248911116548758814195665)
                    ·
                      rfl

theorem cell23_1454258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1454258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454258 prefixEnd_1454258 := by exact prefixLift 1454258
  have htrace : WordTrace (prefixWord ++ tailWord_1454258) baseStart_1454258 baseEnd_1454258 := by
    simpa [prefixWord, tailWord_1454258, baseEnd_1454258] using wordTrace_append hprefix tailTrace_1454258
  have hstable : (prefixWord ++ tailWord_1454258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454258).length < 2 ^ (prefixWord ++ tailWord_1454258).sum := by decide
  have hdescent : baseEnd_1454258 < baseStart_1454258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454282 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_1454282 : Nat := 118140960795 + 1454282 * 2 ^ 59
def prefixEnd_1454282 : Nat := 4983230072969 + 3 ^ 40 * 1454282 * 2
def baseEnd_1454282 : Nat := 746745673181984348686885

theorem tailTrace_1454282 : CollatzResearch.WordTrace tailWord_1454282 prefixEnd_1454282 746745673181984348686885 := by
  unfold tailWord_1454282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260505529348040109209275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35361348078261440291224733 13260505529348040109209275)
  ·
    refine ⟨19890758294022060163813913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13260505529348040109209275 19890758294022060163813913)
    ·
      refine ⟨14918068720516545122860435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19890758294022060163813913 14918068720516545122860435)
      ·
        refine ⟨22377103080774817684290653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14918068720516545122860435 22377103080774817684290653)
        ·
          refine ⟨8391413655290556631608995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22377103080774817684290653 8391413655290556631608995)
          ·
            refine ⟨12587120482935834947413493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391413655290556631608995 12587120482935834947413493)
            ·
              refine ⟨1180042545275234526320015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12587120482935834947413493 1180042545275234526320015)
              ·
                refine ⟨1770063817912851789480023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180042545275234526320015 1770063817912851789480023)
                ·
                  refine ⟨2655095726869277684220035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770063817912851789480023 2655095726869277684220035)
                  ·
                    refine ⟨3982643590303916526330053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655095726869277684220035 3982643590303916526330053)
                    ·
                      refine ⟨746745673181984348686885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3982643590303916526330053 746745673181984348686885)
                      ·
                        rfl

theorem cell23_1454282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_1454282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454282 prefixEnd_1454282 := by exact prefixLift 1454282
  have htrace : WordTrace (prefixWord ++ tailWord_1454282) baseStart_1454282 baseEnd_1454282 := by
    simpa [prefixWord, tailWord_1454282, baseEnd_1454282] using wordTrace_append hprefix tailTrace_1454282
  have hstable : (prefixWord ++ tailWord_1454282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454282).length < 2 ^ (prefixWord ++ tailWord_1454282).sum := by decide
  have hdescent : baseEnd_1454282 < baseStart_1454282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454293 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1454293 : Nat := 118140960795 + 1454293 * 2 ^ 59
def prefixEnd_1454293 : Nat := 4983230072969 + 3 ^ 40 * 1454293 * 2
def baseEnd_1454293 : Nat := 746751321469183805649335

theorem tailTrace_1454293 : CollatzResearch.WordTrace tailWord_1454293 prefixEnd_1454293 746751321469183805649335 := by
  unfold tailWord_1454293
  simp only [CollatzResearch.WordTrace]
  refine ⟨53042423320352309315487533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35361615546901539543658355 53042423320352309315487533)
  ·
    refine ⟨19890908745132115993307825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53042423320352309315487533 19890908745132115993307825)
    ·
      refine ⟨14918181558849086994980869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19890908745132115993307825 14918181558849086994980869)
      ·
        refine ⟨2797159042284203811558913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14918181558849086994980869 2797159042284203811558913)
        ·
          refine ⟨2097869281713152858669185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797159042284203811558913 2097869281713152858669185)
          ·
            refine ⟨1573401961284864644001889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097869281713152858669185 1573401961284864644001889)
            ·
              refine ⟨1180051470963648483001417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573401961284864644001889 1180051470963648483001417)
              ·
                refine ⟨885038603222736362251063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180051470963648483001417 885038603222736362251063)
                ·
                  refine ⟨1327557904834104543376595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885038603222736362251063 1327557904834104543376595)
                  ·
                    refine ⟨1991336857251156815064893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1327557904834104543376595 1991336857251156815064893)
                    ·
                      refine ⟨746751321469183805649335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1991336857251156815064893 746751321469183805649335)
                      ·
                        rfl

theorem cell23_1454293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1454293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454293 prefixEnd_1454293 := by exact prefixLift 1454293
  have htrace : WordTrace (prefixWord ++ tailWord_1454293) baseStart_1454293 baseEnd_1454293 := by
    simpa [prefixWord, tailWord_1454293, baseEnd_1454293] using wordTrace_append hprefix tailTrace_1454293
  have hstable : (prefixWord ++ tailWord_1454293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454293).length < 2 ^ (prefixWord ++ tailWord_1454293).sum := by decide
  have hdescent : baseEnd_1454293 < baseStart_1454293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454315 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3]
def baseStart_1454315 : Nat := 118140960795 + 1454315 * 2 ^ 59
def prefixEnd_1454315 : Nat := 4983230072969 + 3 ^ 40 * 1454315 * 2
def baseEnd_1454315 : Nat := 746762618043582719574233

theorem tailTrace_1454315 : CollatzResearch.WordTrace tailWord_1454315 prefixEnd_1454315 746762618043582719574233 := by
  unfold tailWord_1454315
  simp only [CollatzResearch.WordTrace]
  refine ⟨53043225726272607072788399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35362150484181738048525599 53043225726272607072788399)
  ·
    refine ⟨79564838589408910609182599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53043225726272607072788399 79564838589408910609182599)
    ·
      refine ⟨119347257884113365913773899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79564838589408910609182599 119347257884113365913773899)
      ·
        refine ⟨179020886826170048870660849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119347257884113365913773899 179020886826170048870660849)
        ·
          refine ⟨134265665119627536652995637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179020886826170048870660849 134265665119627536652995637)
          ·
            refine ⟨12587406104965081561218341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134265665119627536652995637 12587406104965081561218341)
            ·
              refine ⟨2360138644680952792728439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12587406104965081561218341 2360138644680952792728439)
              ·
                refine ⟨3540207967021429189092659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360138644680952792728439 3540207967021429189092659)
                ·
                  refine ⟨5310311950532143783638989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540207967021429189092659 5310311950532143783638989)
                  ·
                    refine ⟨1991366981449553918864621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5310311950532143783638989 1991366981449553918864621)
                    ·
                      refine ⟨746762618043582719574233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1991366981449553918864621 746762618043582719574233)
                      ·
                        rfl

theorem cell23_1454315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 3].length) (baseStart_1454315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454315 prefixEnd_1454315 := by exact prefixLift 1454315
  have htrace : WordTrace (prefixWord ++ tailWord_1454315) baseStart_1454315 baseEnd_1454315 := by
    simpa [prefixWord, tailWord_1454315, baseEnd_1454315] using wordTrace_append hprefix tailTrace_1454315
  have hstable : (prefixWord ++ tailWord_1454315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454315).length < 2 ^ (prefixWord ++ tailWord_1454315).sum := by decide
  have hdescent : baseEnd_1454315 < baseStart_1454315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454318 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1454318 : Nat := 118140960795 + 1454318 * 2 ^ 59
def prefixEnd_1454318 : Nat := 4983230072969 + 3 ^ 40 * 1454318 * 2
def baseEnd_1454318 : Nat := 248921386161848735945573

theorem tailTrace_1454318 : CollatzResearch.WordTrace tailWord_1454318 prefixEnd_1454318 248921386161848735945573 := by
  unfold tailWord_1454318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630416893157717323143451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35362223430174492390098405 6630416893157717323143451)
  ·
    refine ⟨9945625339736575984715177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6630416893157717323143451 9945625339736575984715177)
    ·
      refine ⟨7459219004802431988536383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9945625339736575984715177 7459219004802431988536383)
      ·
        refine ⟨11188828507203647982804575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459219004802431988536383 11188828507203647982804575)
        ·
          refine ⟨16783242760805471974206863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188828507203647982804575 16783242760805471974206863)
          ·
            refine ⟨25174864141208207961310295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783242760805471974206863 25174864141208207961310295)
            ·
              refine ⟨37762296211812311941965443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25174864141208207961310295 37762296211812311941965443)
              ·
                refine ⟨56643444317718467912948165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37762296211812311941965443 56643444317718467912948165)
                ·
                  refine ⟨10620645809572212733677781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56643444317718467912948165 10620645809572212733677781)
                  ·
                    refine ⟨248921386161848735945573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10620645809572212733677781 248921386161848735945573)
                    ·
                      rfl

theorem cell23_1454318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1454318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454318 prefixEnd_1454318 := by exact prefixLift 1454318
  have htrace : WordTrace (prefixWord ++ tailWord_1454318) baseStart_1454318 baseEnd_1454318 := by
    simpa [prefixWord, tailWord_1454318, baseEnd_1454318] using wordTrace_append hprefix tailTrace_1454318
  have hstable : (prefixWord ++ tailWord_1454318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454318).length < 2 ^ (prefixWord ++ tailWord_1454318).sum := by decide
  have hdescent : baseEnd_1454318 < baseStart_1454318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454348 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1454348 : Nat := 118140960795 + 1454348 * 2 ^ 59
def prefixEnd_1454348 : Nat := 4983230072969 + 3 ^ 40 * 1454348 * 2
def baseEnd_1454348 : Nat := 248926520968393696820527

theorem tailTrace_1454348 : CollatzResearch.WordTrace tailWord_1454348 prefixEnd_1454348 248926520968393696820527 := by
  unfold tailWord_1454348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522214667576526854369849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35362952890102035805826465 26522214667576526854369849)
  ·
    refine ⟨19891661000682395140777387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26522214667576526854369849 19891661000682395140777387)
    ·
      refine ⟨29837491501023592711166081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19891661000682395140777387 29837491501023592711166081)
      ·
        refine ⟨22378118625767694533374561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29837491501023592711166081 22378118625767694533374561)
        ·
          refine ⟨16783588969325770900030921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22378118625767694533374561 16783588969325770900030921)
          ·
            refine ⟨12587691726994328175023191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16783588969325770900030921 12587691726994328175023191)
            ·
              refine ⟨18881537590491492262534787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12587691726994328175023191 18881537590491492262534787)
              ·
                refine ⟨28322306385737238393802181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18881537590491492262534787 28322306385737238393802181)
                ·
                  refine ⟨5310432447325732198837909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28322306385737238393802181 5310432447325732198837909)
                  ·
                    refine ⟨248926520968393696820527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5310432447325732198837909 248926520968393696820527)
                    ·
                      rfl

theorem cell23_1454348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1454348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454348 prefixEnd_1454348 := by exact prefixLift 1454348
  have htrace : WordTrace (prefixWord ++ tailWord_1454348) baseStart_1454348 baseEnd_1454348 := by
    simpa [prefixWord, tailWord_1454348, baseEnd_1454348] using wordTrace_append hprefix tailTrace_1454348
  have hstable : (prefixWord ++ tailWord_1454348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454348).length < 2 ^ (prefixWord ++ tailWord_1454348).sum := by decide
  have hdescent : baseEnd_1454348 < baseStart_1454348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 4, 2]
def baseStart_1454355 : Nat := 118140960795 + 1454355 * 2 ^ 59
def prefixEnd_1454355 : Nat := 4983230072969 + 3 ^ 40 * 1454355 * 2
def baseEnd_1454355 : Nat := 746783157269762563074049

theorem tailTrace_1454355 : CollatzResearch.WordTrace tailWord_1454355 prefixEnd_1454355 746783157269762563074049 := by
  unfold tailWord_1454355
  simp only [CollatzResearch.WordTrace]
  refine ⟨53044684646127693904244519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35363123097418462602829679 53044684646127693904244519)
  ·
    refine ⟨79567026969191540856366779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53044684646127693904244519 79567026969191540856366779)
    ·
      refine ⟨119350540453787311284550169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79567026969191540856366779 119350540453787311284550169)
      ·
        refine ⟨89512905340340483463412627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119350540453787311284550169 89512905340340483463412627)
        ·
          refine ⟨134269358010510725195118941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89512905340340483463412627 134269358010510725195118941)
          ·
            refine ⟨50351009253941521948169603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134269358010510725195118941 50351009253941521948169603)
            ·
              refine ⟨75526513880912282922254405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50351009253941521948169603 75526513880912282922254405)
              ·
                refine ⟨14161221352671053047922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75526513880912282922254405 14161221352671053047922701)
                ·
                  refine ⟨5310458007251644892971013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14161221352671053047922701 5310458007251644892971013)
                  ·
                    refine ⟨995710876359683417432065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5310458007251644892971013 995710876359683417432065)
                    ·
                      refine ⟨746783157269762563074049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995710876359683417432065 746783157269762563074049)
                      ·
                        rfl

theorem cell23_1454355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 4, 2].length) (baseStart_1454355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454355 prefixEnd_1454355 := by exact prefixLift 1454355
  have htrace : WordTrace (prefixWord ++ tailWord_1454355) baseStart_1454355 baseEnd_1454355 := by
    simpa [prefixWord, tailWord_1454355, baseEnd_1454355] using wordTrace_append hprefix tailTrace_1454355
  have hstable : (prefixWord ++ tailWord_1454355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454355).length < 2 ^ (prefixWord ++ tailWord_1454355).sum := by decide
  have hdescent : baseEnd_1454355 < baseStart_1454355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454366 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1454366 : Nat := 118140960795 + 1454366 * 2 ^ 59
def prefixEnd_1454366 : Nat := 4983230072969 + 3 ^ 40 * 1454366 * 2
def baseEnd_1454366 : Nat := 746788805556962020036499

theorem tailTrace_1454366 : CollatzResearch.WordTrace tailWord_1454366 prefixEnd_1454366 746788805556962020036499 := by
  unfold tailWord_1454366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630635731135980347861869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35363390566058561855263301 6630635731135980347861869)
  ·
    refine ⟨2486488399175992630448201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6630635731135980347861869 2486488399175992630448201)
    ·
      refine ⟨1864866299381994472836151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486488399175992630448201 1864866299381994472836151)
      ·
        refine ⟨2797299449072991709254227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864866299381994472836151 2797299449072991709254227)
        ·
          refine ⟨4195949173609487563881341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797299449072991709254227 4195949173609487563881341)
          ·
            refine ⟨1573480940103557836455503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4195949173609487563881341 1573480940103557836455503)
            ·
              refine ⟨2360221410155336754683255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573480940103557836455503 2360221410155336754683255)
              ·
                refine ⟨3540332115233005132024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360221410155336754683255 3540332115233005132024883)
                ·
                  refine ⟨5310498172849507698037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540332115233005132024883 5310498172849507698037325)
                  ·
                    refine ⟨1991436814818565386763997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5310498172849507698037325 1991436814818565386763997)
                    ·
                      refine ⟨746788805556962020036499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1991436814818565386763997 746788805556962020036499)
                      ·
                        rfl

theorem cell23_1454366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1454366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454366 prefixEnd_1454366 := by exact prefixLift 1454366
  have htrace : WordTrace (prefixWord ++ tailWord_1454366) baseStart_1454366 baseEnd_1454366 := by
    simpa [prefixWord, tailWord_1454366, baseEnd_1454366] using wordTrace_append hprefix tailTrace_1454366
  have hstable : (prefixWord ++ tailWord_1454366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454366).length < 2 ^ (prefixWord ++ tailWord_1454366).sum := by decide
  have hdescent : baseEnd_1454366 < baseStart_1454366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454376 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1454376 : Nat := 118140960795 + 1454376 * 2 ^ 59
def prefixEnd_1454376 : Nat := 4983230072969 + 3 ^ 40 * 1454376 * 2
def baseEnd_1454376 : Nat := 746793940363506980911453

theorem tailTrace_1454376 : CollatzResearch.WordTrace tailWord_1454376 prefixEnd_1454376 746793940363506980911453 := by
  unfold tailWord_1454376
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522725289525807245379491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35363633719367742993839321 26522725289525807245379491)
  ·
    refine ⟨39784087934288710868069237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26522725289525807245379491 39784087934288710868069237)
    ·
      refine ⟨3729758243839566643881491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39784087934288710868069237 3729758243839566643881491)
      ·
        refine ⟨5594637365759349965822237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729758243839566643881491 5594637365759349965822237)
        ·
          refine ⟨2097989012159756237183339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5594637365759349965822237 2097989012159756237183339)
          ·
            refine ⟨3146983518239634355775009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097989012159756237183339 3146983518239634355775009)
            ·
              refine ⟨2360237638679725766831257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146983518239634355775009 2360237638679725766831257)
              ·
                refine ⟨1770178229009794325123443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360237638679725766831257 1770178229009794325123443)
                ·
                  refine ⟨2655267343514691487685165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770178229009794325123443 2655267343514691487685165)
                  ·
                    refine ⟨995725253818009307881937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655267343514691487685165 995725253818009307881937)
                    ·
                      refine ⟨746793940363506980911453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995725253818009307881937 746793940363506980911453)
                      ·
                        rfl

theorem cell23_1454376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1454376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454376 prefixEnd_1454376 := by exact prefixLift 1454376
  have htrace : WordTrace (prefixWord ++ tailWord_1454376) baseStart_1454376 baseEnd_1454376 := by
    simpa [prefixWord, tailWord_1454376, baseEnd_1454376] using wordTrace_append hprefix tailTrace_1454376
  have hstable : (prefixWord ++ tailWord_1454376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454376).length < 2 ^ (prefixWord ++ tailWord_1454376).sum := by decide
  have hdescent : baseEnd_1454376 < baseStart_1454376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454442 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1454442 : Nat := 118140960795 + 1454442 * 2 ^ 59
def prefixEnd_1454442 : Nat := 4983230072969 + 3 ^ 40 * 1454442 * 2
def baseEnd_1454442 : Nat := 248942610028901240895383

theorem tailTrace_1454442 : CollatzResearch.WordTrace tailWord_1454442 prefixEnd_1454442 248942610028901240895383 := by
  unfold tailWord_1454442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13261964449203126940665395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35365238531208338508441053 13261964449203126940665395)
  ·
    refine ⟨19892946673804690410998093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13261964449203126940665395 19892946673804690410998093)
    ·
      refine ⟨7459855002676758904124285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19892946673804690410998093 7459855002676758904124285)
      ·
        refine ⟨2797445626003784589046607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7459855002676758904124285 2797445626003784589046607)
        ·
          refine ⟨4196168439005676883569911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797445626003784589046607 4196168439005676883569911)
          ·
            refine ⟨6294252658508515325354867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196168439005676883569911 6294252658508515325354867)
            ·
              refine ⟨9441378987762772988032301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294252658508515325354867 9441378987762772988032301)
              ·
                refine ⟨3540517120411039870512113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9441378987762772988032301 3540517120411039870512113)
                ·
                  refine ⟨2655387840308279902884085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540517120411039870512113 2655387840308279902884085)
                  ·
                    refine ⟨248942610028901240895383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2655387840308279902884085 248942610028901240895383)
                    ·
                      rfl

theorem cell23_1454442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1454442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454442 prefixEnd_1454442 := by exact prefixLift 1454442
  have htrace : WordTrace (prefixWord ++ tailWord_1454442) baseStart_1454442 baseEnd_1454442 := by
    simpa [prefixWord, tailWord_1454442, baseEnd_1454442] using wordTrace_append hprefix tailTrace_1454442
  have hstable : (prefixWord ++ tailWord_1454442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454442).length < 2 ^ (prefixWord ++ tailWord_1454442).sum := by decide
  have hdescent : baseEnd_1454442 < baseStart_1454442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454455 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 7, 4]
def baseStart_1454455 : Nat := 118140960795 + 1454455 * 2 ^ 59
def prefixEnd_1454455 : Nat := 4983230072969 + 3 ^ 40 * 1454455 * 2
def baseEnd_1454455 : Nat := 248944835111737390607863

theorem tailTrace_1454455 : CollatzResearch.WordTrace tailWord_1454455 prefixEnd_1454455 248944835111737390607863 := by
  unfold tailWord_1454455
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048331945765410982884819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35365554630510273988589879 53048331945765410982884819)
  ·
    refine ⟨79572497918648116474327229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53048331945765410982884819 79572497918648116474327229)
    ·
      refine ⟨29839686719493043677872711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79572497918648116474327229 29839686719493043677872711)
      ·
        refine ⟨44759530079239565516809067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29839686719493043677872711 44759530079239565516809067)
        ·
          refine ⟨67139295118859348275213601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44759530079239565516809067 67139295118859348275213601)
          ·
            refine ⟨50354471339144511206410201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67139295118859348275213601 50354471339144511206410201)
            ·
              refine ⟨37765853504358383404807651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50354471339144511206410201 37765853504358383404807651)
              ·
                refine ⟨56648780256537575107211477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37765853504358383404807651 56648780256537575107211477)
                ·
                  refine ⟨1327705787262599416575269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56648780256537575107211477 1327705787262599416575269)
                  ·
                    refine ⟨248944835111737390607863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327705787262599416575269 248944835111737390607863)
                    ·
                      rfl

theorem cell23_1454455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_1454455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454455 prefixEnd_1454455 := by exact prefixLift 1454455
  have htrace : WordTrace (prefixWord ++ tailWord_1454455) baseStart_1454455 baseEnd_1454455 := by
    simpa [prefixWord, tailWord_1454455, baseEnd_1454455] using wordTrace_append hprefix tailTrace_1454455
  have hstable : (prefixWord ++ tailWord_1454455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454455).length < 2 ^ (prefixWord ++ tailWord_1454455).sum := by decide
  have hdescent : baseEnd_1454455 < baseStart_1454455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454472 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1454472 : Nat := 118140960795 + 1454472 * 2 ^ 59
def prefixEnd_1454472 : Nat := 4983230072969 + 3 ^ 40 * 1454472 * 2
def baseEnd_1454472 : Nat := 248947744835446201770337

theorem tailTrace_1454472 : CollatzResearch.WordTrace tailWord_1454472 prefixEnd_1454472 248947744835446201770337 := by
  unfold tailWord_1454472
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524475993351911443126835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35365967991135881924169113 26524475993351911443126835)
  ·
    refine ⟨39786713990027867164690253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26524475993351911443126835 39786713990027867164690253)
    ·
      refine ⟨14920017746260450186758845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39786713990027867164690253 14920017746260450186758845)
      ·
        refine ⟨5595006654847668820034567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14920017746260450186758845 5595006654847668820034567)
        ·
          refine ⟨8392509982271503230051851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595006654847668820034567 8392509982271503230051851)
          ·
            refine ⟨12588764973407254845077777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8392509982271503230051851 12588764973407254845077777)
            ·
              refine ⟨9441573730055441133808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12588764973407254845077777 9441573730055441133808333)
              ·
                refine ⟨3540590148770790425178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9441573730055441133808333 3540590148770790425178125)
                ·
                  refine ⟨1327721305789046409441797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3540590148770790425178125 1327721305789046409441797)
                  ·
                    refine ⟨248947744835446201770337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327721305789046409441797 248947744835446201770337)
                    ·
                      rfl

theorem cell23_1454472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1454472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454472 prefixEnd_1454472 := by exact prefixLift 1454472
  have htrace : WordTrace (prefixWord ++ tailWord_1454472) baseStart_1454472 baseEnd_1454472 := by
    simpa [prefixWord, tailWord_1454472, baseEnd_1454472] using wordTrace_append hprefix tailTrace_1454472
  have hstable : (prefixWord ++ tailWord_1454472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454472).length < 2 ^ (prefixWord ++ tailWord_1454472).sum := by decide
  have hdescent : baseEnd_1454472 < baseStart_1454472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454499 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1454499 : Nat := 118140960795 + 1454499 * 2 ^ 59
def prefixEnd_1454499 : Nat := 4983230072969 + 3 ^ 40 * 1454499 * 2
def baseEnd_1454499 : Nat := 746857098484009999673387

theorem tailTrace_1454499 : CollatzResearch.WordTrace tailWord_1454499 prefixEnd_1454499 746857098484009999673387 := by
  unfold tailWord_1454499
  simp only [CollatzResearch.WordTrace]
  refine ⟨53049936757606006497486551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35366624505070670998324367 53049936757606006497486551)
  ·
    refine ⟨79574905136409009746229827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53049936757606006497486551 79574905136409009746229827)
    ·
      refine ⟨119362357704613514619344741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79574905136409009746229827 119362357704613514619344741)
      ·
        refine ⟨22380442069615033991127139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119362357704613514619344741 22380442069615033991127139)
        ·
          refine ⟨33570663104422550986690709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22380442069615033991127139 33570663104422550986690709)
          ·
            refine ⟨1573624833019807077501127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33570663104422550986690709 1573624833019807077501127)
            ·
              refine ⟨2360437249529710616251691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573624833019807077501127 2360437249529710616251691)
              ·
                refine ⟨3540655874294565924377537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360437249529710616251691 3540655874294565924377537)
                ·
                  refine ⟨2655491905720924443283153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540655874294565924377537 2655491905720924443283153)
                  ·
                    refine ⟨1991618929290693332462365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2655491905720924443283153 1991618929290693332462365)
                    ·
                      refine ⟨746857098484009999673387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1991618929290693332462365 746857098484009999673387)
                      ·
                        rfl

theorem cell23_1454499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1454499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454499 prefixEnd_1454499 := by exact prefixLift 1454499
  have htrace : WordTrace (prefixWord ++ tailWord_1454499) baseStart_1454499 baseEnd_1454499 := by
    simpa [prefixWord, tailWord_1454499, baseEnd_1454499] using wordTrace_append hprefix tailTrace_1454499
  have hstable : (prefixWord ++ tailWord_1454499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454499).length < 2 ^ (prefixWord ++ tailWord_1454499).sum := by decide
  have hdescent : baseEnd_1454499 < baseStart_1454499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454549 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_1454549 : Nat := 118140960795 + 1454549 * 2 ^ 59
def prefixEnd_1454549 : Nat := 4983230072969 + 3 ^ 40 * 1454549 * 2
def baseEnd_1454549 : Nat := 248960924172244934682719

theorem tailTrace_1454549 : CollatzResearch.WordTrace tailWord_1454549 prefixEnd_1454549 248960924172244934682719 := by
  unfold tailWord_1454549
  simp only [CollatzResearch.WordTrace]
  refine ⟨53051760407424865036806701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35367840271616576691204467 53051760407424865036806701)
  ·
    refine ⟨19894410152784324388802513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53051760407424865036806701 19894410152784324388802513)
    ·
      refine ⟨14920807614588243291601885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19894410152784324388802513 14920807614588243291601885)
      ·
        refine ⟨5595302855470591234350707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14920807614588243291601885 5595302855470591234350707)
        ·
          refine ⟨8392954283205886851526061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595302855470591234350707 8392954283205886851526061)
          ·
            refine ⟨3147357856202207569322273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8392954283205886851526061 3147357856202207569322273)
            ·
              refine ⟨2360518392151655676991705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3147357856202207569322273 2360518392151655676991705)
              ·
                refine ⟨1770388794113741757743779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360518392151655676991705 1770388794113741757743779)
                ·
                  refine ⟨2655583191170612636615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770388794113741757743779 2655583191170612636615669)
                  ·
                    refine ⟨248960924172244934682719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2655583191170612636615669 248960924172244934682719)
                    ·
                      rfl

theorem cell23_1454549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_1454549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454549 prefixEnd_1454549 := by exact prefixLift 1454549
  have htrace : WordTrace (prefixWord ++ tailWord_1454549) baseStart_1454549 baseEnd_1454549 := by
    simpa [prefixWord, tailWord_1454549, baseEnd_1454549] using wordTrace_append hprefix tailTrace_1454549
  have hstable : (prefixWord ++ tailWord_1454549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454549).length < 2 ^ (prefixWord ++ tailWord_1454549).sum := by decide
  have hdescent : baseEnd_1454549 < baseStart_1454549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454552 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_1454552 : Nat := 118140960795 + 1454552 * 2 ^ 59
def prefixEnd_1454552 : Nat := 4983230072969 + 3 ^ 40 * 1454552 * 2
def baseEnd_1454552 : Nat := 746884312958698292310643

theorem tailTrace_1454552 : CollatzResearch.WordTrace tailWord_1454552 prefixEnd_1454552 746884312958698292310643 := by
  unfold tailWord_1454552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26525934913206998274582955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35367913217609331032777273 26525934913206998274582955)
  ·
    refine ⟨39788902369810497411874433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26525934913206998274582955 39788902369810497411874433)
    ·
      refine ⟨29841676777357873058905825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39788902369810497411874433 29841676777357873058905825)
      ·
        refine ⟨22381257583018404794179369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29841676777357873058905825 22381257583018404794179369)
        ·
          refine ⟨16785943187263803595634527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22381257583018404794179369 16785943187263803595634527)
          ·
            refine ⟨25178914780895705393451791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16785943187263803595634527 25178914780895705393451791)
            ·
              refine ⟨37768372171343558090177687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25178914780895705393451791 37768372171343558090177687)
              ·
                refine ⟨56652558257015337135266531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37768372171343558090177687 56652558257015337135266531)
                ·
                  refine ⟨84978837385523005702899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56652558257015337135266531 84978837385523005702899797)
                  ·
                    refine ⟨995845750611597723080857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84978837385523005702899797 995845750611597723080857)
                    ·
                      refine ⟨746884312958698292310643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995845750611597723080857 746884312958698292310643)
                      ·
                        rfl

theorem cell23_1454552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_1454552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454552 prefixEnd_1454552 := by exact prefixLift 1454552
  have htrace : WordTrace (prefixWord ++ tailWord_1454552) baseStart_1454552 baseEnd_1454552 := by
    simpa [prefixWord, tailWord_1454552, baseEnd_1454552] using wordTrace_append hprefix tailTrace_1454552
  have hstable : (prefixWord ++ tailWord_1454552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454552).length < 2 ^ (prefixWord ++ tailWord_1454552).sum := by decide
  have hdescent : baseEnd_1454552 < baseStart_1454552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454572 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1454572 : Nat := 118140960795 + 1454572 * 2 ^ 59
def prefixEnd_1454572 : Nat := 4983230072969 + 3 ^ 40 * 1454572 * 2
def baseEnd_1454572 : Nat := 746894582571788214060551

theorem tailTrace_1454572 : CollatzResearch.WordTrace tailWord_1454572 prefixEnd_1454572 746894582571788214060551 := by
  unfold tailWord_1454572
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526299643170769982446985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35368399524227693309929313 26526299643170769982446985)
  ·
    refine ⟨19894724732378077486835239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26526299643170769982446985 19894724732378077486835239)
    ·
      refine ⟨29842087098567116230252859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19894724732378077486835239 29842087098567116230252859)
      ·
        refine ⟨44763130647850674345379289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29842087098567116230252859 44763130647850674345379289)
        ·
          refine ⟨33572347985888005759034467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44763130647850674345379289 33572347985888005759034467)
          ·
            refine ⟨50358521978832008638551701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33572347985888005759034467 50358521978832008638551701)
            ·
              refine ⟨2360555717757750404932111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50358521978832008638551701 2360555717757750404932111)
              ·
                refine ⟨3540833576636625607398167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360555717757750404932111 3540833576636625607398167)
                ·
                  refine ⟨5311250364954938411097251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3540833576636625607398167 5311250364954938411097251)
                  ·
                    refine ⟨7966875547432407616645877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5311250364954938411097251 7966875547432407616645877)
                    ·
                      refine ⟨746894582571788214060551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7966875547432407616645877 746894582571788214060551)
                      ·
                        rfl

theorem cell23_1454572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1454572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454572 prefixEnd_1454572 := by exact prefixLift 1454572
  have htrace : WordTrace (prefixWord ++ tailWord_1454572) baseStart_1454572 baseEnd_1454572 := by
    simpa [prefixWord, tailWord_1454572, baseEnd_1454572] using wordTrace_append hprefix tailTrace_1454572
  have hstable : (prefixWord ++ tailWord_1454572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454572).length < 2 ^ (prefixWord ++ tailWord_1454572).sum := by decide
  have hdescent : baseEnd_1454572 < baseStart_1454572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454582 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1454582 : Nat := 118140960795 + 1454582 * 2 ^ 59
def prefixEnd_1454582 : Nat := 4983230072969 + 3 ^ 40 * 1454582 * 2
def baseEnd_1454582 : Nat := 746899717378333174935505

theorem tailTrace_1454582 : CollatzResearch.WordTrace tailWord_1454582 prefixEnd_1454582 746899717378333174935505 := by
  unfold tailWord_1454582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315810251019081979547375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35368642677536874448505333 3315810251019081979547375)
  ·
    refine ⟨4973715376528622969321063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315810251019081979547375 4973715376528622969321063)
    ·
      refine ⟨7460573064792934453981595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973715376528622969321063 7460573064792934453981595)
      ·
        refine ⟨11190859597189401680972393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460573064792934453981595 11190859597189401680972393)
        ·
          refine ⟨8393144697892051260729295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11190859597189401680972393 8393144697892051260729295)
          ·
            refine ⟨12589717046838076891093943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393144697892051260729295 12589717046838076891093943)
            ·
              refine ⟨18884575570257115336640915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12589717046838076891093943 18884575570257115336640915)
              ·
                refine ⟨28326863355385673004961373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18884575570257115336640915 28326863355385673004961373)
                ·
                  refine ⟨10622573758269627376860515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28326863355385673004961373 10622573758269627376860515)
                  ·
                    refine ⟨15933860637404441065290773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10622573758269627376860515 15933860637404441065290773)
                    ·
                      refine ⟨746899717378333174935505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15933860637404441065290773 746899717378333174935505)
                      ·
                        rfl

theorem cell23_1454582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1454582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454582 prefixEnd_1454582 := by exact prefixLift 1454582
  have htrace : WordTrace (prefixWord ++ tailWord_1454582) baseStart_1454582 baseEnd_1454582 := by
    simpa [prefixWord, tailWord_1454582, baseEnd_1454582] using wordTrace_append hprefix tailTrace_1454582
  have hstable : (prefixWord ++ tailWord_1454582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454582).length < 2 ^ (prefixWord ++ tailWord_1454582).sum := by decide
  have hdescent : baseEnd_1454582 < baseStart_1454582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454595 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1454595 : Nat := 118140960795 + 1454595 * 2 ^ 59
def prefixEnd_1454595 : Nat := 4983230072969 + 3 ^ 40 * 1454595 * 2
def baseEnd_1454595 : Nat := 746906392626841624072945

theorem tailTrace_1454595 : CollatzResearch.WordTrace tailWord_1454595 prefixEnd_1454595 746906392626841624072945 := by
  unfold tailWord_1454595
  simp only [CollatzResearch.WordTrace]
  refine ⟨53053438165258214892981239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35368958776838809928654159 53053438165258214892981239)
  ·
    refine ⟨79580157247887322339471859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53053438165258214892981239 79580157247887322339471859)
    ·
      refine ⟨119370235871830983509207789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79580157247887322339471859 119370235871830983509207789)
      ·
        refine ⟨44763838451936618815952921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119370235871830983509207789 44763838451936618815952921)
        ·
          refine ⟨33572878838952464111964691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44763838451936618815952921 33572878838952464111964691)
          ·
            refine ⟨50359318258428696167947037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33572878838952464111964691 50359318258428696167947037)
            ·
              refine ⟨18884744346910761062980139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50359318258428696167947037 18884744346910761062980139)
              ·
                refine ⟨28327116520366141594470209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18884744346910761062980139 28327116520366141594470209)
                ·
                  refine ⟨21245337390274606195852657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28327116520366141594470209 21245337390274606195852657)
                  ·
                    refine ⟨15934003042705954646889493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21245337390274606195852657 15934003042705954646889493)
                    ·
                      refine ⟨746906392626841624072945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15934003042705954646889493 746906392626841624072945)
                      ·
                        rfl

theorem cell23_1454595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1454595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454595 prefixEnd_1454595 := by exact prefixLift 1454595
  have htrace : WordTrace (prefixWord ++ tailWord_1454595) baseStart_1454595 baseEnd_1454595 := by
    simpa [prefixWord, tailWord_1454595, baseEnd_1454595] using wordTrace_append hprefix tailTrace_1454595
  have hstable : (prefixWord ++ tailWord_1454595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454595).length < 2 ^ (prefixWord ++ tailWord_1454595).sum := by decide
  have hdescent : baseEnd_1454595 < baseStart_1454595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454596 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1454596 : Nat := 118140960795 + 1454596 * 2 ^ 59
def prefixEnd_1454596 : Nat := 4983230072969 + 3 ^ 40 * 1454596 * 2
def baseEnd_1454596 : Nat := 248968968702498706720147

theorem tailTrace_1454596 : CollatzResearch.WordTrace tailWord_1454596 prefixEnd_1454596 248968968702498706720147 := by
  unfold tailWord_1454596
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526737319127296031883821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35368983092169728042511761 26526737319127296031883821)
  ·
    refine ⟨9947526494672736011956433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26526737319127296031883821 9947526494672736011956433)
    ·
      refine ⟨7460644871004552008967325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9947526494672736011956433 7460644871004552008967325)
      ·
        refine ⟨2797741826626707003362747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7460644871004552008967325 2797741826626707003362747)
        ·
          refine ⟨4196612739940060505044121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797741826626707003362747 4196612739940060505044121)
          ·
            refine ⟨3147459554955045378783091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4196612739940060505044121 3147459554955045378783091)
            ·
              refine ⟨4721189332432568068174637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147459554955045378783091 4721189332432568068174637)
              ·
                refine ⟨1770445999662213025565489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4721189332432568068174637 1770445999662213025565489)
                ·
                  refine ⟨1327834499746659769174117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770445999662213025565489 1327834499746659769174117)
                  ·
                    refine ⟨248968968702498706720147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327834499746659769174117 248968968702498706720147)
                    ·
                      rfl

theorem cell23_1454596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1454596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454596 prefixEnd_1454596 := by exact prefixLift 1454596
  have htrace : WordTrace (prefixWord ++ tailWord_1454596) baseStart_1454596 baseEnd_1454596 := by
    simpa [prefixWord, tailWord_1454596, baseEnd_1454596] using wordTrace_append hprefix tailTrace_1454596
  have hstable : (prefixWord ++ tailWord_1454596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454596).length < 2 ^ (prefixWord ++ tailWord_1454596).sum := by decide
  have hdescent : baseEnd_1454596 < baseStart_1454596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454606 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1454606 : Nat := 118140960795 + 1454606 * 2 ^ 59
def prefixEnd_1454606 : Nat := 4983230072969 + 3 ^ 40 * 1454606 * 2
def baseEnd_1454606 : Nat := 746912040914041081035395

theorem tailTrace_1454606 : CollatzResearch.WordTrace tailWord_1454606 prefixEnd_1454606 746912040914041081035395 := by
  unfold tailWord_1454606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631729921027295471453959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35369226245478909181087781 6631729921027295471453959)
  ·
    refine ⟨9947594881540943207180939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631729921027295471453959 9947594881540943207180939)
    ·
      refine ⟨14921392322311414810771409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947594881540943207180939 14921392322311414810771409)
      ·
        refine ⟨11191044241733561108078557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921392322311414810771409 11191044241733561108078557)
        ·
          refine ⟨4196641590650085415529459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11191044241733561108078557 4196641590650085415529459)
          ·
            refine ⟨6294962385975128123294189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196641590650085415529459 6294962385975128123294189)
            ·
              refine ⟨2360610894740673046235321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6294962385975128123294189 2360610894740673046235321)
              ·
                refine ⟨1770458171055504784676491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360610894740673046235321 1770458171055504784676491)
                ·
                  refine ⟨2655687256583257177014737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770458171055504784676491 2655687256583257177014737)
                  ·
                    refine ⟨1991765442437442882761053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2655687256583257177014737 1991765442437442882761053)
                    ·
                      refine ⟨746912040914041081035395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1991765442437442882761053 746912040914041081035395)
                      ·
                        rfl

theorem cell23_1454606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1454606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454606 prefixEnd_1454606 := by exact prefixLift 1454606
  have htrace : WordTrace (prefixWord ++ tailWord_1454606) baseStart_1454606 baseEnd_1454606 := by
    simpa [prefixWord, tailWord_1454606, baseEnd_1454606] using wordTrace_append hprefix tailTrace_1454606
  have hstable : (prefixWord ++ tailWord_1454606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454606).length < 2 ^ (prefixWord ++ tailWord_1454606).sum := by decide
  have hdescent : baseEnd_1454606 < baseStart_1454606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
