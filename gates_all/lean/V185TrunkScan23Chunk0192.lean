import V185TrunkScan23Chunk0191

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1137045 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1137045 : Nat := 118140960795 + 1137045 * 2 ^ 59
def prefixEnd_1137045 : Nat := 4983230072969 + 3 ^ 40 * 1137045 * 2
def baseEnd_1137045 : Nat := 583850610791609039908331

theorem tailTrace_1137045 : CollatzResearch.WordTrace tailWord_1137045 prefixEnd_1137045 583850610791609039908331 := by
  unfold tailWord_1137045
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471438165687631670708589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27647625443791754447139059 41471438165687631670708589)
  ·
    refine ⟨15551789312132861876515721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41471438165687631670708589 15551789312132861876515721)
    ·
      refine ⟨11663841984099646407386791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15551789312132861876515721 11663841984099646407386791)
      ·
        refine ⟨17495762976149469611080187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663841984099646407386791 17495762976149469611080187)
        ·
          refine ⟨26243644464224204416620281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17495762976149469611080187 26243644464224204416620281)
          ·
            refine ⟨19682733348168153312465211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26243644464224204416620281 19682733348168153312465211)
            ·
              refine ⟨29524100022252229968697817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19682733348168153312465211 29524100022252229968697817)
              ·
                refine ⟨22143075016689172476523363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29524100022252229968697817 22143075016689172476523363)
                ·
                  refine ⟨33214612525033758714785045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22143075016689172476523363 33214612525033758714785045)
                  ·
                    refine ⟨1556934962110957439755549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33214612525033758714785045 1556934962110957439755549)
                    ·
                      refine ⟨583850610791609039908331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1556934962110957439755549 583850610791609039908331)
                      ·
                        rfl

theorem cell23_1137045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1137045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137045 prefixEnd_1137045 := by exact prefixLift 1137045
  have htrace : WordTrace (prefixWord ++ tailWord_1137045) baseStart_1137045 baseEnd_1137045 := by
    simpa [prefixWord, tailWord_1137045, baseEnd_1137045] using wordTrace_append hprefix tailTrace_1137045
  have hstable : (prefixWord ++ tailWord_1137045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137045).length < 2 ^ (prefixWord ++ tailWord_1137045).sum := by decide
  have hdescent : baseEnd_1137045 < baseStart_1137045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137059 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 4, 2, 2]
def baseStart_1137059 : Nat := 118140960795 + 1137059 * 2 ^ 59
def prefixEnd_1137059 : Nat := 4983230072969 + 3 ^ 40 * 1137059 * 2
def baseEnd_1137059 : Nat := 583857799520771985133267

theorem tailTrace_1137059 : CollatzResearch.WordTrace tailWord_1137059 prefixEnd_1137059 583857799520771985133267 := by
  unfold tailWord_1137059
  simp only [CollatzResearch.WordTrace]
  refine ⟨41471948787636912061718231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27647965858424608041145487 41471948787636912061718231)
  ·
    refine ⟨62207923181455368092577347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41471948787636912061718231 62207923181455368092577347)
    ·
      refine ⟨93311884772183052138866021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62207923181455368092577347 93311884772183052138866021)
      ·
        refine ⟨17495978394784322276037379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93311884772183052138866021 17495978394784322276037379)
        ·
          refine ⟨26243967592176483414056069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17495978394784322276037379 26243967592176483414056069)
          ·
            refine ⟨4920743923533090640135513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26243967592176483414056069 4920743923533090640135513)
            ·
              refine ⟨3690557942649817980101635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920743923533090640135513 3690557942649817980101635)
              ·
                refine ⟨5535836913974726970152453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690557942649817980101635 5535836913974726970152453)
                ·
                  refine ⟨1037969421370261306903585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5535836913974726970152453 1037969421370261306903585)
                  ·
                    refine ⟨778477066027695980177689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1037969421370261306903585 778477066027695980177689)
                    ·
                      refine ⟨583857799520771985133267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778477066027695980177689 583857799520771985133267)
                      ·
                        rfl

theorem cell23_1137059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_1137059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137059 prefixEnd_1137059 := by exact prefixLift 1137059
  have htrace : WordTrace (prefixWord ++ tailWord_1137059) baseStart_1137059 baseEnd_1137059 := by
    simpa [prefixWord, tailWord_1137059, baseEnd_1137059] using wordTrace_append hprefix tailTrace_1137059
  have hstable : (prefixWord ++ tailWord_1137059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137059).length < 2 ^ (prefixWord ++ tailWord_1137059).sum := by decide
  have hdescent : baseEnd_1137059 < baseStart_1137059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137155 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 8]
def baseStart_1137155 : Nat := 118140960795 + 1137155 * 2 ^ 59
def prefixEnd_1137155 : Nat := 4983230072969 + 3 ^ 40 * 1137155 * 2
def baseEnd_1137155 : Nat := 64878565962622623281425

theorem tailTrace_1137155 : CollatzResearch.WordTrace tailWord_1137155 prefixEnd_1137155 64878565962622623281425 := by
  unfold tailWord_1137155
  simp only [CollatzResearch.WordTrace]
  refine ⟨41475450195289120457212919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27650300130192746971475279 41475450195289120457212919)
  ·
    refine ⟨62213175292933680685819379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41475450195289120457212919 62213175292933680685819379)
    ·
      refine ⟨93319762939400521028729069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62213175292933680685819379 93319762939400521028729069)
      ·
        refine ⟨34994911102275195385773401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93319762939400521028729069 34994911102275195385773401)
        ·
          refine ⟨26246183326706396539330051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34994911102275195385773401 26246183326706396539330051)
          ·
            refine ⟨39369274990059594808995077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26246183326706396539330051 39369274990059594808995077)
            ·
              refine ⟨7381739060636174026686577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39369274990059594808995077 7381739060636174026686577)
              ·
                refine ⟨5536304295477130520014933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7381739060636174026686577 5536304295477130520014933)
                ·
                  refine ⟨64878565962622623281425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5536304295477130520014933 64878565962622623281425)
                  ·
                    rfl

theorem cell23_1137155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 8].length) (baseStart_1137155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137155 prefixEnd_1137155 := by exact prefixLift 1137155
  have htrace : WordTrace (prefixWord ++ tailWord_1137155) baseStart_1137155 baseEnd_1137155 := by
    simpa [prefixWord, tailWord_1137155, baseEnd_1137155] using wordTrace_append hprefix tailTrace_1137155
  have hstable : (prefixWord ++ tailWord_1137155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137155).length < 2 ^ (prefixWord ++ tailWord_1137155).sum := by decide
  have hdescent : baseEnd_1137155 < baseStart_1137155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137176 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 1, 4]
def baseStart_1137176 : Nat := 118140960795 + 1137176 * 2 ^ 59
def prefixEnd_1137176 : Nat := 4983230072969 + 3 ^ 40 * 1137176 * 2
def baseEnd_1137176 : Nat := 194639292252449342456743

theorem tailTrace_1137176 : CollatzResearch.WordTrace tailWord_1137176 prefixEnd_1137176 194639292252449342456743 := by
  unfold tailWord_1137176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20738108064106520521863691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27650810752142027362484921 20738108064106520521863691)
  ·
    refine ⟨31107162096159780782795537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20738108064106520521863691 31107162096159780782795537)
    ·
      refine ⟨23330371572119835587096653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31107162096159780782795537 23330371572119835587096653)
      ·
        refine ⟨8748889339544938345161245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23330371572119835587096653 8748889339544938345161245)
        ·
          refine ⟨3280833502329351879435467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8748889339544938345161245 3280833502329351879435467)
          ·
            refine ⟨4921250253494027819153201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280833502329351879435467 4921250253494027819153201)
            ·
              refine ⟨3690937690120520864364901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4921250253494027819153201 3690937690120520864364901)
              ·
                refine ⟨692050816897597662068419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3690937690120520864364901 692050816897597662068419)
                ·
                  refine ⟨1038076225346396493102629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692050816897597662068419 1038076225346396493102629)
                  ·
                    refine ⟨194639292252449342456743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038076225346396493102629 194639292252449342456743)
                    ·
                      rfl

theorem cell23_1137176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_1137176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137176 prefixEnd_1137176 := by exact prefixLift 1137176
  have htrace : WordTrace (prefixWord ++ tailWord_1137176) baseStart_1137176 baseEnd_1137176 := by
    simpa [prefixWord, tailWord_1137176, baseEnd_1137176] using wordTrace_append hprefix tailTrace_1137176
  have hstable : (prefixWord ++ tailWord_1137176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137176).length < 2 ^ (prefixWord ++ tailWord_1137176).sum := by decide
  have hdescent : baseEnd_1137176 < baseStart_1137176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137195 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7]
def baseStart_1137195 : Nat := 118140960795 + 1137195 * 2 ^ 59
def prefixEnd_1137195 : Nat := 4983230072969 + 3 ^ 40 * 1137195 * 2
def baseEnd_1137195 : Nat := 583927632889783453032641

theorem tailTrace_1137195 : CollatzResearch.WordTrace tailWord_1137195 prefixEnd_1137195 583927632889783453032641 := by
  unfold tailWord_1137195
  simp only [CollatzResearch.WordTrace]
  refine ⟨41476909115144207288669039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27651272743429471525779359 41476909115144207288669039)
  ·
    refine ⟨62215363672716310933003559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41476909115144207288669039 62215363672716310933003559)
    ·
      refine ⟨93323045509074466399505339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62215363672716310933003559 93323045509074466399505339)
      ·
        refine ⟨139984568263611699599258009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93323045509074466399505339 139984568263611699599258009)
        ·
          refine ⟨104988426197708774699443507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139984568263611699599258009 104988426197708774699443507)
          ·
            refine ⟨157482639296563162049165261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104988426197708774699443507 157482639296563162049165261)
            ·
              refine ⟨59055989736211185768436973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157482639296563162049165261 59055989736211185768436973)
              ·
                refine ⟨22145996151079194663163865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59055989736211185768436973 22145996151079194663163865)
                ·
                  refine ⟨16609497113309395997372899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22145996151079194663163865 16609497113309395997372899)
                  ·
                    refine ⟨24914245669964093996059349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16609497113309395997372899 24914245669964093996059349)
                    ·
                      refine ⟨583927632889783453032641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24914245669964093996059349 583927632889783453032641)
                      ·
                        rfl

theorem cell23_1137195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_1137195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137195 prefixEnd_1137195 := by exact prefixLift 1137195
  have htrace : WordTrace (prefixWord ++ tailWord_1137195) baseStart_1137195 baseEnd_1137195 := by
    simpa [prefixWord, tailWord_1137195, baseEnd_1137195] using wordTrace_append hprefix tailTrace_1137195
  have hstable : (prefixWord ++ tailWord_1137195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137195).length < 2 ^ (prefixWord ++ tailWord_1137195).sum := by decide
  have hdescent : baseEnd_1137195 < baseStart_1137195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137202 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_1137202 : Nat := 118140960795 + 1137202 * 2 ^ 59
def prefixEnd_1137202 : Nat := 4983230072969 + 3 ^ 40 * 1137202 * 2
def baseEnd_1137202 : Nat := 194643742418121641881703

theorem tailTrace_1137202 : CollatzResearch.WordTrace tailWord_1137202 prefixEnd_1137202 194643742418121641881703 := by
  unfold tailWord_1137202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369291106529711871043465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27651442950745898322782573 10369291106529711871043465)
  ·
    refine ⟨7776968329897283903282599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10369291106529711871043465 7776968329897283903282599)
    ·
      refine ⟨11665452494845925854923899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7776968329897283903282599 11665452494845925854923899)
      ·
        refine ⟨17498178742268888782385849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665452494845925854923899 17498178742268888782385849)
        ·
          refine ⟨13123634056701666586789387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17498178742268888782385849 13123634056701666586789387)
          ·
            refine ⟨19685451085052499880184081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13123634056701666586789387 19685451085052499880184081)
            ·
              refine ⟨14764088313789374910138061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19685451085052499880184081 14764088313789374910138061)
              ·
                refine ⟨5536533117671015591301773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14764088313789374910138061 5536533117671015591301773)
                ·
                  refine ⟨2076199919126630846738165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5536533117671015591301773 2076199919126630846738165)
                  ·
                    refine ⟨194643742418121641881703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2076199919126630846738165 194643742418121641881703)
                    ·
                      rfl

theorem cell23_1137202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_1137202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137202 prefixEnd_1137202 := by exact prefixLift 1137202
  have htrace : WordTrace (prefixWord ++ tailWord_1137202) baseStart_1137202 baseEnd_1137202 := by
    simpa [prefixWord, tailWord_1137202, baseEnd_1137202] using wordTrace_append hprefix tailTrace_1137202
  have hstable : (prefixWord ++ tailWord_1137202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137202).length < 2 ^ (prefixWord ++ tailWord_1137202).sum := by decide
  have hdescent : baseEnd_1137202 < baseStart_1137202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137209 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1137209 : Nat := 118140960795 + 1137209 * 2 ^ 59
def prefixEnd_1137209 : Nat := 4983230072969 + 3 ^ 40 * 1137209 * 2
def baseEnd_1137209 : Nat := 583934821618946398257577

theorem tailTrace_1137209 : CollatzResearch.WordTrace tailWord_1137209 prefixEnd_1137209 583934821618946398257577 := by
  unfold tailWord_1137209
  simp only [CollatzResearch.WordTrace]
  refine ⟨41477419737093487679678681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27651613158062325119785787 41477419737093487679678681)
  ·
    refine ⟨31108064802820115759759011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41477419737093487679678681 31108064802820115759759011)
    ·
      refine ⟨46662097204230173639638517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31108064802820115759759011 46662097204230173639638517)
      ·
        refine ⟨4374571612896578778716111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46662097204230173639638517 4374571612896578778716111)
        ·
          refine ⟨6561857419344868168074167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4374571612896578778716111 6561857419344868168074167)
          ·
            refine ⟨9842786129017302252111251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6561857419344868168074167 9842786129017302252111251)
            ·
              refine ⟨14764179193525953378166877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9842786129017302252111251 14764179193525953378166877)
              ·
                refine ⟨5536567197572232516812579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14764179193525953378166877 5536567197572232516812579)
                ·
                  refine ⟨8304850796358348775218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536567197572232516812579 8304850796358348775218869)
                  ·
                    refine ⟨778579762158595197676769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8304850796358348775218869 778579762158595197676769)
                    ·
                      refine ⟨583934821618946398257577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778579762158595197676769 583934821618946398257577)
                      ·
                        rfl

theorem cell23_1137209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1137209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137209 prefixEnd_1137209 := by exact prefixLift 1137209
  have htrace : WordTrace (prefixWord ++ tailWord_1137209) baseStart_1137209 baseEnd_1137209 := by
    simpa [prefixWord, tailWord_1137209, baseEnd_1137209] using wordTrace_append hprefix tailTrace_1137209
  have hstable : (prefixWord ++ tailWord_1137209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137209).length < 2 ^ (prefixWord ++ tailWord_1137209).sum := by decide
  have hdescent : baseEnd_1137209 < baseStart_1137209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137220 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1137220 : Nat := 118140960795 + 1137220 * 2 ^ 59
def prefixEnd_1137220 : Nat := 4983230072969 + 3 ^ 40 * 1137220 * 2
def baseEnd_1137220 : Nat := 583940469906145855220027

theorem tailTrace_1137220 : CollatzResearch.WordTrace tailWord_1137220 prefixEnd_1137220 583940469906145855220027 := by
  unfold tailWord_1137220
  simp only [CollatzResearch.WordTrace]
  refine ⟨20738910470026818279164557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27651880626702424372219409 20738910470026818279164557)
  ·
    refine ⟨7777091426260056854686709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20738910470026818279164557 7777091426260056854686709)
    ·
      refine ⟨729102321211880330126879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7777091426260056854686709 729102321211880330126879)
      ·
        refine ⟨1093653481817820495190319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729102321211880330126879 1093653481817820495190319)
        ·
          refine ⟨1640480222726730742785479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093653481817820495190319 1640480222726730742785479)
          ·
            refine ⟨2460720334090096114178219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640480222726730742785479 2460720334090096114178219)
            ·
              refine ⟨3691080501135144171267329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460720334090096114178219 3691080501135144171267329)
              ·
                refine ⟨2768310375851358128450497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691080501135144171267329 2768310375851358128450497)
                ·
                  refine ⟨2076232781888518596337873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768310375851358128450497 2076232781888518596337873)
                  ·
                    refine ⟨1557174586416388947253405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076232781888518596337873 1557174586416388947253405)
                    ·
                      refine ⟨583940469906145855220027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557174586416388947253405 583940469906145855220027)
                      ·
                        rfl

theorem cell23_1137220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1137220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137220 prefixEnd_1137220 := by exact prefixLift 1137220
  have htrace : WordTrace (prefixWord ++ tailWord_1137220) baseStart_1137220 baseEnd_1137220 := by
    simpa [prefixWord, tailWord_1137220, baseEnd_1137220] using wordTrace_append hprefix tailTrace_1137220
  have hstable : (prefixWord ++ tailWord_1137220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137220).length < 2 ^ (prefixWord ++ tailWord_1137220).sum := by decide
  have hdescent : baseEnd_1137220 < baseStart_1137220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137226 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_1137226 : Nat := 118140960795 + 1137226 * 2 ^ 59
def prefixEnd_1137226 : Nat := 4983230072969 + 3 ^ 40 * 1137226 * 2
def baseEnd_1137226 : Nat := 583943550790072831744999

theorem tailTrace_1137226 : CollatzResearch.WordTrace tailWord_1137226 prefixEnd_1137226 583943550790072831744999 := by
  unfold tailWord_1137226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369509944507974895761883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27652026518687933055365021 10369509944507974895761883)
  ·
    refine ⟨15554264916761962343642825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10369509944507974895761883 15554264916761962343642825)
    ·
      refine ⟨11665698687571471757732119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15554264916761962343642825 11665698687571471757732119)
      ·
        refine ⟨17498548031357207636598179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665698687571471757732119 17498548031357207636598179)
        ·
          refine ⟨26247822047035811454897269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498548031357207636598179 26247822047035811454897269)
          ·
            refine ⟨2460733316909607323896619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26247822047035811454897269 2460733316909607323896619)
            ·
              refine ⟨3691099975364410985844929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460733316909607323896619 3691099975364410985844929)
              ·
                refine ⟨2768324981523308239383697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3691099975364410985844929 2768324981523308239383697)
                ·
                  refine ⟨2076243736142481179537773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768324981523308239383697 2076243736142481179537773)
                  ·
                    refine ⟨778591401053430442326665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076243736142481179537773 778591401053430442326665)
                    ·
                      refine ⟨583943550790072831744999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778591401053430442326665 583943550790072831744999)
                      ·
                        rfl

theorem cell23_1137226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_1137226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137226 prefixEnd_1137226 := by exact prefixLift 1137226
  have htrace : WordTrace (prefixWord ++ tailWord_1137226) baseStart_1137226 baseEnd_1137226 := by
    simpa [prefixWord, tailWord_1137226, baseEnd_1137226] using wordTrace_append hprefix tailTrace_1137226
  have hstable : (prefixWord ++ tailWord_1137226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137226).length < 2 ^ (prefixWord ++ tailWord_1137226).sum := by decide
  have hdescent : baseEnd_1137226 < baseStart_1137226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137242 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1137242 : Nat := 118140960795 + 1137242 * 2 ^ 59
def prefixEnd_1137242 : Nat := 4983230072969 + 3 ^ 40 * 1137242 * 2
def baseEnd_1137242 : Nat := 583951766480544769144925

theorem tailTrace_1137242 : CollatzResearch.WordTrace tailWord_1137242 prefixEnd_1137242 583951766480544769144925 := by
  unfold tailWord_1137242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10369655836493483578907495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27652415563982622877086653 10369655836493483578907495)
  ·
    refine ⟨15554483754740225368361243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10369655836493483578907495 15554483754740225368361243)
    ·
      refine ⟨23331725632110338052541865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15554483754740225368361243 23331725632110338052541865)
      ·
        refine ⟨17498794224082753539406399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23331725632110338052541865 17498794224082753539406399)
        ·
          refine ⟨26248191336124130309109599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17498794224082753539406399 26248191336124130309109599)
          ·
            refine ⟨39372287004186195463664399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26248191336124130309109599 39372287004186195463664399)
            ·
              refine ⟨59058430506279293195496599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39372287004186195463664399 59058430506279293195496599)
              ·
                refine ⟨88587645759418939793244899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59058430506279293195496599 88587645759418939793244899)
                ·
                  refine ⟨132881468639128409689867349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88587645759418939793244899 132881468639128409689867349)
                  ·
                    refine ⟨1557204710614786051053133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 132881468639128409689867349 1557204710614786051053133)
                    ·
                      refine ⟨583951766480544769144925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557204710614786051053133 583951766480544769144925)
                      ·
                        rfl

theorem cell23_1137242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1137242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137242 prefixEnd_1137242 := by exact prefixLift 1137242
  have htrace : WordTrace (prefixWord ++ tailWord_1137242) baseStart_1137242 baseEnd_1137242 := by
    simpa [prefixWord, tailWord_1137242, baseEnd_1137242] using wordTrace_append hprefix tailTrace_1137242
  have hstable : (prefixWord ++ tailWord_1137242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137242).length < 2 ^ (prefixWord ++ tailWord_1137242).sum := by decide
  have hdescent : baseEnd_1137242 < baseStart_1137242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137252 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1137252 : Nat := 118140960795 + 1137252 * 2 ^ 59
def prefixEnd_1137252 : Nat := 4983230072969 + 3 ^ 40 * 1137252 * 2
def baseEnd_1137252 : Nat := 583956901287089730019879

theorem tailTrace_1137252 : CollatzResearch.WordTrace tailWord_1137252 prefixEnd_1137252 583956901287089730019879 := by
  unfold tailWord_1137252
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739494037968853011747005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27652658717291804015662673 20739494037968853011747005)
  ·
    refine ⟨7777310264238319879405127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20739494037968853011747005 7777310264238319879405127)
    ·
      refine ⟨11665965396357479819107691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777310264238319879405127 11665965396357479819107691)
      ·
        refine ⟨17498948094536219728661537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665965396357479819107691 17498948094536219728661537)
        ·
          refine ⟨13124211070902164796496153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17498948094536219728661537 13124211070902164796496153)
          ·
            refine ⟨9843158303176623597372115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13124211070902164796496153 9843158303176623597372115)
            ·
              refine ⟨14764737454764935396058173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9843158303176623597372115 14764737454764935396058173)
              ·
                refine ⟨5536776545536850773521815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14764737454764935396058173 5536776545536850773521815)
                ·
                  refine ⟨8305164818305276160282723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5536776545536850773521815 8305164818305276160282723)
                  ·
                    refine ⟨12457747227457914240424085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8305164818305276160282723 12457747227457914240424085)
                    ·
                      refine ⟨583956901287089730019879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12457747227457914240424085 583956901287089730019879)
                      ·
                        rfl

theorem cell23_1137252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1137252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137252 prefixEnd_1137252 := by exact prefixLift 1137252
  have htrace : WordTrace (prefixWord ++ tailWord_1137252) baseStart_1137252 baseEnd_1137252 := by
    simpa [prefixWord, tailWord_1137252, baseEnd_1137252] using wordTrace_append hprefix tailTrace_1137252
  have hstable : (prefixWord ++ tailWord_1137252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137252).length < 2 ^ (prefixWord ++ tailWord_1137252).sum := by decide
  have hdescent : baseEnd_1137252 < baseStart_1137252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137253 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_1137253 : Nat := 118140960795 + 1137253 * 2 ^ 59
def prefixEnd_1137253 : Nat := 4983230072969 + 3 ^ 40 * 1137253 * 2
def baseEnd_1137253 : Nat := 194652471589248075369125

theorem tailTrace_1137253 : CollatzResearch.WordTrace tailWord_1137253 prefixEnd_1137253 194652471589248075369125 := by
  unfold tailWord_1137253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41479024548934083194280413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27652683032622722129520275 41479024548934083194280413)
  ·
    refine ⟨15554634205850281197855155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41479024548934083194280413 15554634205850281197855155)
    ·
      refine ⟨23331951308775421796782733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15554634205850281197855155 23331951308775421796782733)
      ·
        refine ⟨8749481740790783173793525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23331951308775421796782733 8749481740790783173793525)
        ·
          refine ⟨820263913199135922543143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8749481740790783173793525 820263913199135922543143)
          ·
            refine ⟨1230395869798703883814715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820263913199135922543143 1230395869798703883814715)
            ·
              refine ⟨1845593804698055825722073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230395869798703883814715 1845593804698055825722073)
              ·
                refine ⟨1384195353523541869291555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1845593804698055825722073 1384195353523541869291555)
                ·
                  refine ⟨2076293030285312803937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384195353523541869291555 2076293030285312803937333)
                  ·
                    refine ⟨194652471589248075369125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2076293030285312803937333 194652471589248075369125)
                    ·
                      rfl

theorem cell23_1137253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_1137253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137253 prefixEnd_1137253 := by exact prefixLift 1137253
  have htrace : WordTrace (prefixWord ++ tailWord_1137253) baseStart_1137253 baseEnd_1137253 := by
    simpa [prefixWord, tailWord_1137253, baseEnd_1137253] using wordTrace_append hprefix tailTrace_1137253
  have hstable : (prefixWord ++ tailWord_1137253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137253).length < 2 ^ (prefixWord ++ tailWord_1137253).sum := by decide
  have hdescent : baseEnd_1137253 < baseStart_1137253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137256 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1137256 : Nat := 118140960795 + 1137256 * 2 ^ 59
def prefixEnd_1137256 : Nat := 4983230072969 + 3 ^ 40 * 1137256 * 2
def baseEnd_1137256 : Nat := 583958955209707714369861

theorem tailTrace_1137256 : CollatzResearch.WordTrace tailWord_1137256 prefixEnd_1137256 583958955209707714369861 := by
  unfold tailWord_1137256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739566983961607353319811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27652755978615476471093081 20739566983961607353319811)
  ·
    refine ⟨31109350475942411029979717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20739566983961607353319811 31109350475942411029979717)
    ·
      refine ⟨5833003214239202068121197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31109350475942411029979717 5833003214239202068121197)
      ·
        refine ⟨2187376205339700775545449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5833003214239202068121197 2187376205339700775545449)
        ·
          refine ⟨1640532154004775581659087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2187376205339700775545449 1640532154004775581659087)
          ·
            refine ⟨2460798231007163372488631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640532154004775581659087 2460798231007163372488631)
            ·
              refine ⟨3691197346510745058732947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2460798231007163372488631 3691197346510745058732947)
              ·
                refine ⟨5536796019766117588099421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691197346510745058732947 5536796019766117588099421)
                ·
                  refine ⟨2076298507412294095537283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5536796019766117588099421 2076298507412294095537283)
                  ·
                    refine ⟨3114447761118441143305925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076298507412294095537283 3114447761118441143305925)
                    ·
                      refine ⟨583958955209707714369861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3114447761118441143305925 583958955209707714369861)
                      ·
                        rfl

theorem cell23_1137256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1137256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137256 prefixEnd_1137256 := by exact prefixLift 1137256
  have htrace : WordTrace (prefixWord ++ tailWord_1137256) baseStart_1137256 baseEnd_1137256 := by
    simpa [prefixWord, tailWord_1137256, baseEnd_1137256] using wordTrace_append hprefix tailTrace_1137256
  have hstable : (prefixWord ++ tailWord_1137256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137256).length < 2 ^ (prefixWord ++ tailWord_1137256).sum := by decide
  have hdescent : baseEnd_1137256 < baseStart_1137256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137259 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 3]
def baseStart_1137259 : Nat := 118140960795 + 1137259 * 2 ^ 59
def prefixEnd_1137259 : Nat := 4983230072969 + 3 ^ 40 * 1137259 * 2
def baseEnd_1137259 : Nat := 583960495651671202632347

theorem tailTrace_1137259 : CollatzResearch.WordTrace tailWord_1137259 prefixEnd_1137259 583960495651671202632347 := by
  unfold tailWord_1137259
  simp only [CollatzResearch.WordTrace]
  refine ⟨41479243386912346218998831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27652828924608230812665887 41479243386912346218998831)
  ·
    refine ⟨62218865080368519328498247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41479243386912346218998831 62218865080368519328498247)
    ·
      refine ⟨93328297620552778992747371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62218865080368519328498247 93328297620552778992747371)
      ·
        refine ⟨139992446430829168489121057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93328297620552778992747371 139992446430829168489121057)
        ·
          refine ⟨104994334823121876366840793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139992446430829168489121057 104994334823121876366840793)
          ·
            refine ⟨78745751117341407275130595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104994334823121876366840793 78745751117341407275130595)
            ·
              refine ⟨118118626676012110912695893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78745751117341407275130595 118118626676012110912695893)
              ·
                refine ⟨1384202656359516924758155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 118118626676012110912695893 1384202656359516924758155)
                ·
                  refine ⟨2076303984539275387137233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384202656359516924758155 2076303984539275387137233)
                  ·
                    refine ⟨1557227988404456540352925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076303984539275387137233 1557227988404456540352925)
                    ·
                      refine ⟨583960495651671202632347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557227988404456540352925 583960495651671202632347)
                      ·
                        rfl

theorem cell23_1137259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 3].length) (baseStart_1137259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137259 prefixEnd_1137259 := by exact prefixLift 1137259
  have htrace : WordTrace (prefixWord ++ tailWord_1137259) baseStart_1137259 baseEnd_1137259 := by
    simpa [prefixWord, tailWord_1137259, baseEnd_1137259] using wordTrace_append hprefix tailTrace_1137259
  have hstable : (prefixWord ++ tailWord_1137259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137259).length < 2 ^ (prefixWord ++ tailWord_1137259).sum := by decide
  have hdescent : baseEnd_1137259 < baseStart_1137259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137316 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_1137316 : Nat := 118140960795 + 1137316 * 2 ^ 59
def prefixEnd_1137316 : Nat := 4983230072969 + 3 ^ 40 * 1137316 * 2
def baseEnd_1137316 : Nat := 583989764048977479619585

theorem tailTrace_1137316 : CollatzResearch.WordTrace tailWord_1137316 prefixEnd_1137316 583989764048977479619585 := by
  unfold tailWord_1137316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20740661173852922476911901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27654214898470563302549201 20740661173852922476911901)
  ·
    refine ⟨7777747940194845928841963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20740661173852922476911901 7777747940194845928841963)
    ·
      refine ⟨11666621910292268893262945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777747940194845928841963 11666621910292268893262945)
      ·
        refine ⟨8749966432719201669947209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11666621910292268893262945 8749966432719201669947209)
        ·
          refine ⟨6562474824539401252460407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8749966432719201669947209 6562474824539401252460407)
          ·
            refine ⟨9843712236809101878690611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562474824539401252460407 9843712236809101878690611)
            ·
              refine ⟨14765568355213652818035917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9843712236809101878690611 14765568355213652818035917)
              ·
                refine ⟨5537088133205119806763469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14765568355213652818035917 5537088133205119806763469)
                ·
                  refine ⟨2076408049951919927536301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5537088133205119806763469 2076408049951919927536301)
                  ·
                    refine ⟨778653018731969972826113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076408049951919927536301 778653018731969972826113)
                    ·
                      refine ⟨583989764048977479619585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778653018731969972826113 583989764048977479619585)
                      ·
                        rfl

theorem cell23_1137316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_1137316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137316 prefixEnd_1137316 := by exact prefixLift 1137316
  have htrace : WordTrace (prefixWord ++ tailWord_1137316) baseStart_1137316 baseEnd_1137316 := by
    simpa [prefixWord, tailWord_1137316, baseEnd_1137316] using wordTrace_append hprefix tailTrace_1137316
  have hstable : (prefixWord ++ tailWord_1137316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137316).length < 2 ^ (prefixWord ++ tailWord_1137316).sum := by decide
  have hdescent : baseEnd_1137316 < baseStart_1137316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137357 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1137357 : Nat := 118140960795 + 1137357 * 2 ^ 59
def prefixEnd_1137357 : Nat := 4983230072969 + 3 ^ 40 * 1137357 * 2
def baseEnd_1137357 : Nat := 584010816755811819206897

theorem tailTrace_1137357 : CollatzResearch.WordTrace tailWord_1137357 prefixEnd_1137357 584010816755811819206897 := by
  unfold tailWord_1137357
  simp only [CollatzResearch.WordTrace]
  refine ⟨41482817740557308956066325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27655211827038205970710883 41482817740557308956066325)
  ·
    refine ⟨1944507081588623857315609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41482817740557308956066325 1944507081588623857315609)
    ·
      refine ⟨1458380311191467892986707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1944507081588623857315609 1458380311191467892986707)
      ·
        refine ⟨2187570466787201839480061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458380311191467892986707 2187570466787201839480061)
        ·
          refine ⟨820338925045200689805023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2187570466787201839480061 820338925045200689805023)
          ·
            refine ⟨1230508387567801034707535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820338925045200689805023 1230508387567801034707535)
            ·
              refine ⟨1845762581351701552061303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230508387567801034707535 1845762581351701552061303)
              ·
                refine ⟨2768643872027552328091955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845762581351701552061303 2768643872027552328091955)
                ·
                  refine ⟨4152965808041328492137933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2768643872027552328091955 4152965808041328492137933)
                  ·
                    refine ⟨1557362178015498184551725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4152965808041328492137933 1557362178015498184551725)
                    ·
                      refine ⟨584010816755811819206897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557362178015498184551725 584010816755811819206897)
                      ·
                        rfl

theorem cell23_1137357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1137357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137357 prefixEnd_1137357 := by exact prefixLift 1137357
  have htrace : WordTrace (prefixWord ++ tailWord_1137357) baseStart_1137357 baseEnd_1137357 := by
    simpa [prefixWord, tailWord_1137357, baseEnd_1137357] using wordTrace_append hprefix tailTrace_1137357
  have hstable : (prefixWord ++ tailWord_1137357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137357).length < 2 ^ (prefixWord ++ tailWord_1137357).sum := by decide
  have hdescent : baseEnd_1137357 < baseStart_1137357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137419 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4]
def baseStart_1137419 : Nat := 118140960795 + 1137419 * 2 ^ 59
def prefixEnd_1137419 : Nat := 4983230072969 + 3 ^ 40 * 1137419 * 2
def baseEnd_1137419 : Nat := 584042652556390576631611

theorem tailTrace_1137419 : CollatzResearch.WordTrace tailWord_1137419 prefixEnd_1137419 584042652556390576631611 := by
  unfold tailWord_1137419
  simp only [CollatzResearch.WordTrace]
  refine ⟨41485079066332693544823311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27656719377555129029882207 41485079066332693544823311)
  ·
    refine ⟨62227618599499040317234967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41485079066332693544823311 62227618599499040317234967)
    ·
      refine ⟨93341427899248560475852451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62227618599499040317234967 93341427899248560475852451)
      ·
        refine ⟨140012141848872840713778677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93341427899248560475852451 140012141848872840713778677)
        ·
          refine ⟨13126138298331828816916751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140012141848872840713778677 13126138298331828816916751)
          ·
            refine ⟨19689207447497743225375127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13126138298331828816916751 19689207447497743225375127)
            ·
              refine ⟨29533811171246614838062691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19689207447497743225375127 29533811171246614838062691)
              ·
                refine ⟨44300716756869922257094037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29533811171246614838062691 44300716756869922257094037)
                ·
                  refine ⟨2076596097978277605801283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44300716756869922257094037 2076596097978277605801283)
                  ·
                    refine ⟨3114894146967416408701925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076596097978277605801283 3114894146967416408701925)
                    ·
                      refine ⟨584042652556390576631611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3114894146967416408701925 584042652556390576631611)
                      ·
                        rfl

theorem cell23_1137419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_1137419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137419 prefixEnd_1137419 := by exact prefixLift 1137419
  have htrace : WordTrace (prefixWord ++ tailWord_1137419) baseStart_1137419 baseEnd_1137419 := by
    simpa [prefixWord, tailWord_1137419, baseEnd_1137419] using wordTrace_append hprefix tailTrace_1137419
  have hstable : (prefixWord ++ tailWord_1137419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137419).length < 2 ^ (prefixWord ++ tailWord_1137419).sum := by decide
  have hdescent : baseEnd_1137419 < baseStart_1137419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137436 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1137436 : Nat := 118140960795 + 1137436 * 2 ^ 59
def prefixEnd_1137436 : Nat := 4983230072969 + 3 ^ 40 * 1137436 * 2
def baseEnd_1137436 : Nat := 584051381727517010119033

theorem tailTrace_1137436 : CollatzResearch.WordTrace tailWord_1137436 prefixEnd_1137436 584051381727517010119033 := by
  unfold tailWord_1137436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20742849553635552724096081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27657132738180736965461441 20742849553635552724096081)
  ·
    refine ⟨15557137165226664543072061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20742849553635552724096081 15557137165226664543072061)
    ·
      refine ⟨5833926436959999203652023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15557137165226664543072061 5833926436959999203652023)
      ·
        refine ⟨8750889655439998805478035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833926436959999203652023 8750889655439998805478035)
        ·
          refine ⟨13126334483159998208217053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8750889655439998805478035 13126334483159998208217053)
          ·
            refine ⟨4922375431184999328081395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13126334483159998208217053 4922375431184999328081395)
            ·
              refine ⟨7383563146777498992122093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922375431184999328081395 7383563146777498992122093)
              ·
                refine ⟨2768836180041562122045785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7383563146777498992122093 2768836180041562122045785)
                ·
                  refine ⟨2076627135031171591534339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768836180041562122045785 2076627135031171591534339)
                  ·
                    refine ⟨3114940702546757387301509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076627135031171591534339 3114940702546757387301509)
                    ·
                      refine ⟨584051381727517010119033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3114940702546757387301509 584051381727517010119033)
                      ·
                        rfl

theorem cell23_1137436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1137436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137436 prefixEnd_1137436 := by exact prefixLift 1137436
  have htrace : WordTrace (prefixWord ++ tailWord_1137436) baseStart_1137436 baseEnd_1137436 := by
    simpa [prefixWord, tailWord_1137436, baseEnd_1137436] using wordTrace_append hprefix tailTrace_1137436
  have hstable : (prefixWord ++ tailWord_1137436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137436).length < 2 ^ (prefixWord ++ tailWord_1137436).sum := by decide
  have hdescent : baseEnd_1137436 < baseStart_1137436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137463 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 1, 4]
def baseStart_1137463 : Nat := 118140960795 + 1137463 * 2 ^ 59
def prefixEnd_1137463 : Nat := 4983230072969 + 3 ^ 40 * 1137463 * 2
def baseEnd_1137463 : Nat := 194688415235062801493803

theorem tailTrace_1137463 : CollatzResearch.WordTrace tailWord_1137463 prefixEnd_1137463 194688415235062801493803 := by
  unfold tailWord_1137463
  simp only [CollatzResearch.WordTrace]
  refine ⟨41486683878173289059425043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27657789252115526039616695 41486683878173289059425043)
  ·
    refine ⟨62230025817259933589137565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41486683878173289059425043 62230025817259933589137565)
    ·
      refine ⟨23336259681472475095926587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62230025817259933589137565 23336259681472475095926587)
      ·
        refine ⟨35004389522208712643889881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23336259681472475095926587 35004389522208712643889881)
        ·
          refine ⟨26253292141656534482917411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35004389522208712643889881 26253292141656534482917411)
          ·
            refine ⟨39379938212484801724376117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26253292141656534482917411 39379938212484801724376117)
            ·
              refine ⟨3691869207420450161660261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39379938212484801724376117 3691869207420450161660261)
              ·
                refine ⟨692225476391334405311299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3691869207420450161660261 692225476391334405311299)
                ·
                  refine ⟨1038338214587001607966949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692225476391334405311299 1038338214587001607966949)
                  ·
                    refine ⟨194688415235062801493803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038338214587001607966949 194688415235062801493803)
                    ·
                      rfl

theorem cell23_1137463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_1137463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137463 prefixEnd_1137463 := by exact prefixLift 1137463
  have htrace : WordTrace (prefixWord ++ tailWord_1137463) baseStart_1137463 baseEnd_1137463 := by
    simpa [prefixWord, tailWord_1137463, baseEnd_1137463] using wordTrace_append hprefix tailTrace_1137463
  have hstable : (prefixWord ++ tailWord_1137463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137463).length < 2 ^ (prefixWord ++ tailWord_1137463).sum := by decide
  have hdescent : baseEnd_1137463 < baseStart_1137463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137470 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1137470 : Nat := 118140960795 + 1137470 * 2 ^ 59
def prefixEnd_1137470 : Nat := 4983230072969 + 3 ^ 40 * 1137470 * 2
def baseEnd_1137470 : Nat := 584068840069769877093877

theorem tailTrace_1137470 : CollatzResearch.WordTrace tailWord_1137470 prefixEnd_1137470 584068840069769877093877 := by
  unfold tailWord_1137470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185867398643491156866233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27657959459431952836619909 5185867398643491156866233)
  ·
    refine ⟨3889400548982618367649675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5185867398643491156866233 3889400548982618367649675)
    ·
      refine ⟨5834100823473927551474513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889400548982618367649675 5834100823473927551474513)
      ·
        refine ⟨4375575617605445663605885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5834100823473927551474513 4375575617605445663605885)
        ·
          refine ⟨1640840856602042123852207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4375575617605445663605885 1640840856602042123852207)
          ·
            refine ⟨2461261284903063185778311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640840856602042123852207 2461261284903063185778311)
            ·
              refine ⟨3691891927354594778667467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461261284903063185778311 3691891927354594778667467)
              ·
                refine ⟨5537837891031892168001201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3691891927354594778667467 5537837891031892168001201)
                ·
                  refine ⟨4153378418273919126000901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5537837891031892168001201 4153378418273919126000901)
                  ·
                    refine ⟨778758453426359836125169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153378418273919126000901 778758453426359836125169)
                    ·
                      refine ⟨584068840069769877093877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778758453426359836125169 584068840069769877093877)
                      ·
                        rfl

theorem cell23_1137470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1137470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137470 prefixEnd_1137470 := by exact prefixLift 1137470
  have htrace : WordTrace (prefixWord ++ tailWord_1137470) baseStart_1137470 baseEnd_1137470 := by
    simpa [prefixWord, tailWord_1137470, baseEnd_1137470] using wordTrace_append hprefix tailTrace_1137470
  have hstable : (prefixWord ++ tailWord_1137470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137470).length < 2 ^ (prefixWord ++ tailWord_1137470).sum := by decide
  have hdescent : baseEnd_1137470 < baseStart_1137470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137519 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 6]
def baseStart_1137519 : Nat := 118140960795 + 1137519 * 2 ^ 59
def prefixEnd_1137519 : Nat := 4983230072969 + 3 ^ 40 * 1137519 * 2
def baseEnd_1137519 : Nat := 194698000207280061793717

theorem tailTrace_1137519 : CollatzResearch.WordTrace tailWord_1137519 prefixEnd_1137519 194698000207280061793717 := by
  unfold tailWord_1137519
  simp only [CollatzResearch.WordTrace]
  refine ⟨41488726365970410623463611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27659150910646940415642407 41488726365970410623463611)
  ·
    refine ⟨62233089548955615935195417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41488726365970410623463611 62233089548955615935195417)
    ·
      refine ⟨46674817161716711951396563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62233089548955615935195417 46674817161716711951396563)
      ·
        refine ⟨70012225742575067927094845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46674817161716711951396563 70012225742575067927094845)
        ·
          refine ⟨26254584653465650472660567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70012225742575067927094845 26254584653465650472660567)
          ·
            refine ⟨39381876980198475708990851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26254584653465650472660567 39381876980198475708990851)
            ·
              refine ⟨59072815470297713563486277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39381876980198475708990851 59072815470297713563486277)
              ·
                refine ⟨11076152900680821293153677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59072815470297713563486277 11076152900680821293153677)
                ·
                  refine ⟨4153557337755307984932629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11076152900680821293153677 4153557337755307984932629)
                  ·
                    refine ⟨194698000207280061793717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4153557337755307984932629 194698000207280061793717)
                    ·
                      rfl

theorem cell23_1137519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 6].length) (baseStart_1137519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137519 prefixEnd_1137519 := by exact prefixLift 1137519
  have htrace : WordTrace (prefixWord ++ tailWord_1137519) baseStart_1137519 baseEnd_1137519 := by
    simpa [prefixWord, tailWord_1137519, baseEnd_1137519] using wordTrace_append hprefix tailTrace_1137519
  have hstable : (prefixWord ++ tailWord_1137519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137519).length < 2 ^ (prefixWord ++ tailWord_1137519).sum := by decide
  have hdescent : baseEnd_1137519 < baseStart_1137519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137520 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 1, 1, 3]
def baseStart_1137520 : Nat := 118140960795 + 1137520 * 2 ^ 59
def prefixEnd_1137520 : Nat := 4983230072969 + 3 ^ 40 * 1137520 * 2
def baseEnd_1137520 : Nat := 584094514102494681468647

theorem tailTrace_1137520 : CollatzResearch.WordTrace tailWord_1137520 prefixEnd_1137520 584094514102494681468647 := by
  unfold tailWord_1137520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20744381419483393897125007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27659175225977858529500009 20744381419483393897125007)
  ·
    refine ⟨31116572129225090845687511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20744381419483393897125007 31116572129225090845687511)
    ·
      refine ⟨46674858193837636268531267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31116572129225090845687511 46674858193837636268531267)
      ·
        refine ⟨70012287290756454402796901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46674858193837636268531267 70012287290756454402796901)
        ·
          refine ⟨13127303867016835200524419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70012287290756454402796901 13127303867016835200524419)
          ·
            refine ⟨19690955800525252800786629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13127303867016835200524419 19690955800525252800786629)
            ·
              refine ⟨3692054212598484900147493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19690955800525252800786629 3692054212598484900147493)
              ·
                refine ⟨692260164862215918777655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3692054212598484900147493 692260164862215918777655)
                ·
                  refine ⟨1038390247293323878166483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692260164862215918777655 1038390247293323878166483)
                  ·
                    refine ⟨1557585370939985817249725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038390247293323878166483 1557585370939985817249725)
                    ·
                      refine ⟨584094514102494681468647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557585370939985817249725 584094514102494681468647)
                      ·
                        rfl

theorem cell23_1137520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 1, 3].length) (baseStart_1137520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137520 prefixEnd_1137520 := by exact prefixLift 1137520
  have htrace : WordTrace (prefixWord ++ tailWord_1137520) baseStart_1137520 baseEnd_1137520 := by
    simpa [prefixWord, tailWord_1137520, baseEnd_1137520] using wordTrace_append hprefix tailTrace_1137520
  have hstable : (prefixWord ++ tailWord_1137520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137520).length < 2 ^ (prefixWord ++ tailWord_1137520).sum := by decide
  have hdescent : baseEnd_1137520 < baseStart_1137520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137543 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1137543 : Nat := 118140960795 + 1137543 * 2 ^ 59
def prefixEnd_1137543 : Nat := 4983230072969 + 3 ^ 40 * 1137543 * 2
def baseEnd_1137543 : Nat := 584106324157548091481041

theorem tailTrace_1137543 : CollatzResearch.WordTrace tailWord_1137543 prefixEnd_1137543 584106324157548091481041 := by
  unfold tailWord_1137543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41489601717883462722337283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27659734478588975148224855 41489601717883462722337283)
  ·
    refine ⟨62234402576825194083505925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41489601717883462722337283 62234402576825194083505925)
    ·
      refine ⟨11668950483154723890657361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62234402576825194083505925 11668950483154723890657361)
      ·
        refine ⟨8751712862366042917993021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11668950483154723890657361 8751712862366042917993021)
        ·
          refine ⟨3281892323387266094247383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8751712862366042917993021 3281892323387266094247383)
          ·
            refine ⟨4922838485080899141371075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281892323387266094247383 4922838485080899141371075)
            ·
              refine ⟨7384257727621348712056613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922838485080899141371075 7384257727621348712056613)
              ·
                refine ⟨1384548323929002883510615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7384257727621348712056613 1384548323929002883510615)
                ·
                  refine ⟨2076822485893504325265923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384548323929002883510615 2076822485893504325265923)
                  ·
                    refine ⟨3115233728840256487898885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076822485893504325265923 3115233728840256487898885)
                    ·
                      refine ⟨584106324157548091481041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3115233728840256487898885 584106324157548091481041)
                      ·
                        rfl

theorem cell23_1137543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1137543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137543 prefixEnd_1137543 := by exact prefixLift 1137543
  have htrace : WordTrace (prefixWord ++ tailWord_1137543) baseStart_1137543 baseEnd_1137543 := by
    simpa [prefixWord, tailWord_1137543, baseEnd_1137543] using wordTrace_append hprefix tailTrace_1137543
  have hstable : (prefixWord ++ tailWord_1137543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137543).length < 2 ^ (prefixWord ++ tailWord_1137543).sum := by decide
  have hdescent : baseEnd_1137543 < baseStart_1137543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137579 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 9]
def baseStart_1137579 : Nat := 118140960795 + 1137579 * 2 ^ 59
def prefixEnd_1137579 : Nat := 4983230072969 + 3 ^ 40 * 1137579 * 2
def baseEnd_1137579 : Nat := 194708269820369983543625

theorem tailTrace_1137579 : CollatzResearch.WordTrace tailWord_1137579 prefixEnd_1137579 194708269820369983543625 := by
  unfold tailWord_1137579
  simp only [CollatzResearch.WordTrace]
  refine ⟨41490914745753040870647791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27660609830502027247098527 41490914745753040870647791)
  ·
    refine ⟨62236372118629561305971687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41490914745753040870647791 62236372118629561305971687)
    ·
      refine ⟨93354558177944341958957531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62236372118629561305971687 93354558177944341958957531)
      ·
        refine ⟨140031837266916512938436297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93354558177944341958957531 140031837266916512938436297)
        ·
          refine ⟨105023877950187384703827223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140031837266916512938436297 105023877950187384703827223)
          ·
            refine ⟨157535816925281077055740835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105023877950187384703827223 157535816925281077055740835)
            ·
              refine ⟨236303725387921615583611253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157535816925281077055740835 236303725387921615583611253)
              ·
                refine ⟨22153474255117651460963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236303725387921615583611253 22153474255117651460963555)
                ·
                  refine ⟨33230211382676477191445333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22153474255117651460963555 33230211382676477191445333)
                  ·
                    refine ⟨194708269820369983543625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33230211382676477191445333 194708269820369983543625)
                    ·
                      rfl

theorem cell23_1137579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 9].length) (baseStart_1137579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137579 prefixEnd_1137579 := by exact prefixLift 1137579
  have htrace : WordTrace (prefixWord ++ tailWord_1137579) baseStart_1137579 baseEnd_1137579 := by
    simpa [prefixWord, tailWord_1137579, baseEnd_1137579] using wordTrace_append hprefix tailTrace_1137579
  have hstable : (prefixWord ++ tailWord_1137579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137579).length < 2 ^ (prefixWord ++ tailWord_1137579).sum := by decide
  have hdescent : baseEnd_1137579 < baseStart_1137579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137597 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1137597 : Nat := 118140960795 + 1137597 * 2 ^ 59
def prefixEnd_1137597 : Nat := 4983230072969 + 3 ^ 40 * 1137597 * 2
def baseEnd_1137597 : Nat := 584134052112890880205793

theorem tailTrace_1137597 : CollatzResearch.WordTrace tailWord_1137597 prefixEnd_1137597 584134052112890880205793 := by
  unfold tailWord_1137597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41491571259687829944803045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27661047506458553296535363 41491571259687829944803045)
  ·
    refine ⟨7779669611191468114650571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41491571259687829944803045 7779669611191468114650571)
    ·
      refine ⟨11669504416787202171975857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7779669611191468114650571 11669504416787202171975857)
      ·
        refine ⟨8752128312590401628981893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11669504416787202171975857 8752128312590401628981893)
        ·
          refine ⟨1641024058610700305434105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8752128312590401628981893 1641024058610700305434105)
          ·
            refine ⟨1230768043958025229075579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641024058610700305434105 1230768043958025229075579)
            ·
              refine ⟨1846152065937037843613369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230768043958025229075579 1846152065937037843613369)
              ·
                refine ⟨1384614049452778382710027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846152065937037843613369 1384614049452778382710027)
                ·
                  refine ⟨2076921074179167574065041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384614049452778382710027 2076921074179167574065041)
                  ·
                    refine ⟨1557690805634375680548781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2076921074179167574065041 1557690805634375680548781)
                    ·
                      refine ⟨584134052112890880205793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557690805634375680548781 584134052112890880205793)
                      ·
                        rfl

theorem cell23_1137597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1137597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137597 prefixEnd_1137597 := by exact prefixLift 1137597
  have htrace : WordTrace (prefixWord ++ tailWord_1137597) baseStart_1137597 baseEnd_1137597 := by
    simpa [prefixWord, tailWord_1137597, baseEnd_1137597] using wordTrace_append hprefix tailTrace_1137597
  have hstable : (prefixWord ++ tailWord_1137597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137597).length < 2 ^ (prefixWord ++ tailWord_1137597).sum := by decide
  have hdescent : baseEnd_1137597 < baseStart_1137597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 3, 3, 2]
def baseStart_1137603 : Nat := 118140960795 + 1137603 * 2 ^ 59
def prefixEnd_1137603 : Nat := 4983230072969 + 3 ^ 40 * 1137603 * 2
def baseEnd_1137603 : Nat := 584137132996817856730765

theorem tailTrace_1137603 : CollatzResearch.WordTrace tailWord_1137603 prefixEnd_1137603 584137132996817856730765 := by
  unfold tailWord_1137603
  simp only [CollatzResearch.WordTrace]
  refine ⟨41491790097666092969521463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27661193398444061979680975 41491790097666092969521463)
  ·
    refine ⟨62237685146499139454282195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41491790097666092969521463 62237685146499139454282195)
    ·
      refine ⟨93356527719748709181423293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62237685146499139454282195 93356527719748709181423293)
      ·
        refine ⟨35008697894905765943033735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93356527719748709181423293 35008697894905765943033735)
        ·
          refine ⟨52513046842358648914550603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35008697894905765943033735 52513046842358648914550603)
          ·
            refine ⟨78769570263537973371825905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52513046842358648914550603 78769570263537973371825905)
            ·
              refine ⟨59077177697653480028869429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78769570263537973371825905 59077177697653480028869429)
              ·
                refine ⟨5538485409155013752706509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59077177697653480028869429 5538485409155013752706509)
                ·
                  refine ⟨2076932028433130157264941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5538485409155013752706509 2076932028433130157264941)
                  ·
                    refine ⟨778849510662423808974353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2076932028433130157264941 778849510662423808974353)
                    ·
                      refine ⟨584137132996817856730765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778849510662423808974353 584137132996817856730765)
                      ·
                        rfl

theorem cell23_1137603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_1137603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137603 prefixEnd_1137603 := by exact prefixLift 1137603
  have htrace : WordTrace (prefixWord ++ tailWord_1137603) baseStart_1137603 baseEnd_1137603 := by
    simpa [prefixWord, tailWord_1137603, baseEnd_1137603] using wordTrace_append hprefix tailTrace_1137603
  have hstable : (prefixWord ++ tailWord_1137603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137603).length < 2 ^ (prefixWord ++ tailWord_1137603).sum := by decide
  have hdescent : baseEnd_1137603 < baseStart_1137603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137633 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_1137633 : Nat := 118140960795 + 1137633 * 2 ^ 59
def prefixEnd_1137633 : Nat := 4983230072969 + 3 ^ 40 * 1137633 * 2
def baseEnd_1137633 : Nat := 584152537416452739355627

theorem tailTrace_1137633 : CollatzResearch.WordTrace tailWord_1137633 prefixEnd_1137633 584152537416452739355627 := by
  unfold tailWord_1137633
  simp only [CollatzResearch.WordTrace]
  refine ⟨41492884287557408093113553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27661922858371605395409035 41492884287557408093113553)
  ·
    refine ⟨31119663215668056069835165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41492884287557408093113553 31119663215668056069835165)
    ·
      refine ⟨11669873705875521026188187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31119663215668056069835165 11669873705875521026188187)
      ·
        refine ⟨17504810558813281539282281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11669873705875521026188187 17504810558813281539282281)
        ·
          refine ⟨13128607919109961154461711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17504810558813281539282281 13128607919109961154461711)
          ·
            refine ⟨19692911878664941731692567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13128607919109961154461711 19692911878664941731692567)
            ·
              refine ⟨29539367817997412597538851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19692911878664941731692567 29539367817997412597538851)
              ·
                refine ⟨44309051726996118896308277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29539367817997412597538851 44309051726996118896308277)
                ·
                  refine ⟨4153973599405886146528901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44309051726996118896308277 4153973599405886146528901)
                  ·
                    refine ⟨778870049888603652474169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4153973599405886146528901 778870049888603652474169)
                    ·
                      refine ⟨584152537416452739355627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 778870049888603652474169 584152537416452739355627)
                      ·
                        rfl

theorem cell23_1137633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_1137633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137633 prefixEnd_1137633 := by exact prefixLift 1137633
  have htrace : WordTrace (prefixWord ++ tailWord_1137633) baseStart_1137633 baseEnd_1137633 := by
    simpa [prefixWord, tailWord_1137633, baseEnd_1137633] using wordTrace_append hprefix tailTrace_1137633
  have hstable : (prefixWord ++ tailWord_1137633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137633).length < 2 ^ (prefixWord ++ tailWord_1137633).sum := by decide
  have hdescent : baseEnd_1137633 < baseStart_1137633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137636 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1137636 : Nat := 118140960795 + 1137636 * 2 ^ 59
def prefixEnd_1137636 : Nat := 4983230072969 + 3 ^ 40 * 1137636 * 2
def baseEnd_1137636 : Nat := 584154077858416227618113

theorem tailTrace_1137636 : CollatzResearch.WordTrace tailWord_1137636 prefixEnd_1137636 584154077858416227618113 := by
  unfold tailWord_1137636
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746496853273269802736381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27661995804364359736981841 20746496853273269802736381)
  ·
    refine ⟨7779936319977476176026143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20746496853273269802736381 7779936319977476176026143)
    ·
      refine ⟨11669904479966214264039215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7779936319977476176026143 11669904479966214264039215)
      ·
        refine ⟨17504856719949321396058823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11669904479966214264039215 17504856719949321396058823)
        ·
          refine ⟨26257285079923982094088235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17504856719949321396058823 26257285079923982094088235)
          ·
            refine ⟨39385927619885973141132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26257285079923982094088235 39385927619885973141132353)
            ·
              refine ⟨29539445714914479855849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39385927619885973141132353 29539445714914479855849265)
              ·
                refine ⟨22154584286185859891886949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29539445714914479855849265 22154584286185859891886949)
                ·
                  refine ⟨4153984553659848729728803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22154584286185859891886949 4153984553659848729728803)
                  ·
                    refine ⟨6230976830489773094593205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4153984553659848729728803 6230976830489773094593205)
                    ·
                      refine ⟨584154077858416227618113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6230976830489773094593205 584154077858416227618113)
                      ·
                        rfl

theorem cell23_1137636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1137636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137636 prefixEnd_1137636 := by exact prefixLift 1137636
  have htrace : WordTrace (prefixWord ++ tailWord_1137636) baseStart_1137636 baseEnd_1137636 := by
    simpa [prefixWord, tailWord_1137636, baseEnd_1137636] using wordTrace_append hprefix tailTrace_1137636
  have hstable : (prefixWord ++ tailWord_1137636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137636).length < 2 ^ (prefixWord ++ tailWord_1137636).sum := by decide
  have hdescent : baseEnd_1137636 < baseStart_1137636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137700 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1137700 : Nat := 118140960795 + 1137700 * 2 ^ 59
def prefixEnd_1137700 : Nat := 4983230072969 + 3 ^ 40 * 1137700 * 2
def baseEnd_1137700 : Nat := 584186940620303977217819

theorem tailTrace_1137700 : CollatzResearch.WordTrace tailWord_1137700 prefixEnd_1137700 584186940620303977217819 := by
  unfold tailWord_1137700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747663989157339267901277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27663551985543119023868369 20747663989157339267901277)
  ·
    refine ⟨7780373995934002225462979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20747663989157339267901277 7780373995934002225462979)
    ·
      refine ⟨11670560993901003338194469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7780373995934002225462979 11670560993901003338194469)
      ·
        refine ⟨2188230186356438125911463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11670560993901003338194469 2188230186356438125911463)
        ·
          refine ⟨3282345279534657188867195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188230186356438125911463 3282345279534657188867195)
          ·
            refine ⟨4923517919301985783300793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282345279534657188867195 4923517919301985783300793)
            ·
              refine ⟨3692638439476489337475595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4923517919301985783300793 3692638439476489337475595)
              ·
                refine ⟨5538957659214734006213393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3692638439476489337475595 5538957659214734006213393)
                ·
                  refine ⟨4154218244411050504660045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538957659214734006213393 4154218244411050504660045)
                  ·
                    refine ⟨1557831841654143939247517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4154218244411050504660045 1557831841654143939247517)
                    ·
                      refine ⟨584186940620303977217819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1557831841654143939247517 584186940620303977217819)
                      ·
                        rfl

theorem cell23_1137700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1137700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137700 prefixEnd_1137700 := by exact prefixLift 1137700
  have htrace : WordTrace (prefixWord ++ tailWord_1137700) baseStart_1137700 baseEnd_1137700 := by
    simpa [prefixWord, tailWord_1137700, baseEnd_1137700] using wordTrace_append hprefix tailTrace_1137700
  have hstable : (prefixWord ++ tailWord_1137700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137700).length < 2 ^ (prefixWord ++ tailWord_1137700).sum := by decide
  have hdescent : baseEnd_1137700 < baseStart_1137700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137733 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1137733 : Nat := 118140960795 + 1137733 * 2 ^ 59
def prefixEnd_1137733 : Nat := 4983230072969 + 3 ^ 40 * 1137733 * 2
def baseEnd_1137733 : Nat := 194734628493967449368389

theorem tailTrace_1137733 : CollatzResearch.WordTrace tailWord_1137733 prefixEnd_1137733 194734628493967449368389 := by
  unfold tailWord_1137733
  simp only [CollatzResearch.WordTrace]
  refine ⟨41496531587195125171753853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27664354391463416781169235 41496531587195125171753853)
  ·
    refine ⟨15561199345198171939407695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41496531587195125171753853 15561199345198171939407695)
    ·
      refine ⟨23341799017797257909111543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15561199345198171939407695 23341799017797257909111543)
      ·
        refine ⟨35012698526695886863667315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23341799017797257909111543 35012698526695886863667315)
        ·
          refine ⟨52519047790043830295500973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35012698526695886863667315 52519047790043830295500973)
          ·
            refine ⟨19694642921266436360812865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52519047790043830295500973 19694642921266436360812865)
            ·
              refine ⟨14770982190949827270609649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19694642921266436360812865 14770982190949827270609649)
              ·
                refine ⟨11078236643212370452957237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14770982190949827270609649 11078236643212370452957237)
                ·
                  refine ⟨1038584685301159729964741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11078236643212370452957237 1038584685301159729964741)
                  ·
                    refine ⟨194734628493967449368389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038584685301159729964741 194734628493967449368389)
                    ·
                      rfl

theorem cell23_1137733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1137733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137733 prefixEnd_1137733 := by exact prefixLift 1137733
  have htrace : WordTrace (prefixWord ++ tailWord_1137733) baseStart_1137733 baseEnd_1137733 := by
    simpa [prefixWord, tailWord_1137733, baseEnd_1137733] using wordTrace_append hprefix tailTrace_1137733
  have hstable : (prefixWord ++ tailWord_1137733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137733).length < 2 ^ (prefixWord ++ tailWord_1137733).sum := by decide
  have hdescent : baseEnd_1137733 < baseStart_1137733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137810 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1137810 : Nat := 118140960795 + 1137810 * 2 ^ 59
def prefixEnd_1137810 : Nat := 4983230072969 + 3 ^ 40 * 1137810 * 2
def baseEnd_1137810 : Nat := 194747807830766182280771

theorem tailTrace_1137810 : CollatzResearch.WordTrace tailWord_1137810 prefixEnd_1137810 194747807830766182280771 := by
  unfold tailWord_1137810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374835001979041830576721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27666226671944111548204589 10374835001979041830576721)
  ·
    refine ⟨7781126251484281372932541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10374835001979041830576721 7781126251484281372932541)
    ·
      refine ⟨2917922344306605514849703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7781126251484281372932541 2917922344306605514849703)
      ·
        refine ⟨4376883516459908272274555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917922344306605514849703 4376883516459908272274555)
        ·
          refine ⟨6565325274689862408411833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376883516459908272274555 6565325274689862408411833)
          ·
            refine ⟨4923993956017396806308875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6565325274689862408411833 4923993956017396806308875)
            ·
              refine ⟨7385990934026095209463313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923993956017396806308875 7385990934026095209463313)
              ·
                refine ⟨5539493200519571407097485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385990934026095209463313 5539493200519571407097485)
                ·
                  refine ⟨2077309950194839277661557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5539493200519571407097485 2077309950194839277661557)
                  ·
                    refine ⟨194747807830766182280771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2077309950194839277661557 194747807830766182280771)
                    ·
                      rfl

theorem cell23_1137810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1137810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137810 prefixEnd_1137810 := by exact prefixLift 1137810
  have htrace : WordTrace (prefixWord ++ tailWord_1137810) baseStart_1137810 baseEnd_1137810 := by
    simpa [prefixWord, tailWord_1137810, baseEnd_1137810] using wordTrace_append hprefix tailTrace_1137810
  have hstable : (prefixWord ++ tailWord_1137810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137810).length < 2 ^ (prefixWord ++ tailWord_1137810).sum := by decide
  have hdescent : baseEnd_1137810 < baseStart_1137810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137833 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_1137833 : Nat := 118140960795 + 1137833 * 2 ^ 59
def prefixEnd_1137833 : Nat := 4983230072969 + 3 ^ 40 * 1137833 * 2
def baseEnd_1137833 : Nat := 584255233547351956854707

theorem tailTrace_1137833 : CollatzResearch.WordTrace tailWord_1137833 prefixEnd_1137833 584255233547351956854707 := by
  unfold tailWord_1137833
  simp only [CollatzResearch.WordTrace]
  refine ⟨41500178886832842250394153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27666785924555228166929435 41500178886832842250394153)
  ·
    refine ⟨31125134165124631687795615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41500178886832842250394153 31125134165124631687795615)
    ·
      refine ⟨46687701247686947531693423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31125134165124631687795615 46687701247686947531693423)
      ·
        refine ⟨70031551871530421297540135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46687701247686947531693423 70031551871530421297540135)
        ·
          refine ⟨105047327807295631946310203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70031551871530421297540135 105047327807295631946310203)
          ·
            refine ⟨157570991710943447919465305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105047327807295631946310203 157570991710943447919465305)
            ·
              refine ⟨118178243783207585939598979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157570991710943447919465305 118178243783207585939598979)
              ·
                refine ⟨177267365674811378909398469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118178243783207585939598979 177267365674811378909398469)
                ·
                  refine ⟨33237631064027133545512213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177267365674811378909398469 33237631064027133545512213)
                  ·
                    refine ⟨1558013956126271884945885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33237631064027133545512213 1558013956126271884945885)
                    ·
                      refine ⟨584255233547351956854707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558013956126271884945885 584255233547351956854707)
                      ·
                        rfl

theorem cell23_1137833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_1137833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137833 prefixEnd_1137833 := by exact prefixLift 1137833
  have htrace : WordTrace (prefixWord ++ tailWord_1137833) baseStart_1137833 baseEnd_1137833 := by
    simpa [prefixWord, tailWord_1137833, baseEnd_1137833] using wordTrace_append hprefix tailTrace_1137833
  have hstable : (prefixWord ++ tailWord_1137833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137833).length < 2 ^ (prefixWord ++ tailWord_1137833).sum := by decide
  have hdescent : baseEnd_1137833 < baseStart_1137833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137834 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1137834 : Nat := 118140960795 + 1137834 * 2 ^ 59
def prefixEnd_1137834 : Nat := 4983230072969 + 3 ^ 40 * 1137834 * 2
def baseEnd_1137834 : Nat := 584255747028006452942203

theorem tailTrace_1137834 : CollatzResearch.WordTrace tailWord_1137834 prefixEnd_1137834 584255747028006452942203 := by
  unfold tailWord_1137834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375053839957304855295139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27666810239886146280787037 10375053839957304855295139)
  ·
    refine ⟨15562580759935957282942709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10375053839957304855295139 15562580759935957282942709)
    ·
      refine ⟨1458991946243995995275879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15562580759935957282942709 1458991946243995995275879)
      ·
        refine ⟨2188487919365993992913819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458991946243995995275879 2188487919365993992913819)
        ·
          refine ⟨3282731879048990989370729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188487919365993992913819 3282731879048990989370729)
          ·
            refine ⟨2462048909286743242028047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3282731879048990989370729 2462048909286743242028047)
            ·
              refine ⟨3693073363930114863042071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462048909286743242028047 3693073363930114863042071)
              ·
                refine ⟨5539610045895172294563107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693073363930114863042071 5539610045895172294563107)
                ·
                  refine ⟨8309415068842758441844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5539610045895172294563107 8309415068842758441844661)
                  ·
                    refine ⟨779007662704008603922937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8309415068842758441844661 779007662704008603922937)
                    ·
                      refine ⟨584255747028006452942203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779007662704008603922937 584255747028006452942203)
                      ·
                        rfl

theorem cell23_1137834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1137834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137834 prefixEnd_1137834 := by exact prefixLift 1137834
  have htrace : WordTrace (prefixWord ++ tailWord_1137834) baseStart_1137834 baseEnd_1137834 := by
    simpa [prefixWord, tailWord_1137834, baseEnd_1137834] using wordTrace_append hprefix tailTrace_1137834
  have hstable : (prefixWord ++ tailWord_1137834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137834).length < 2 ^ (prefixWord ++ tailWord_1137834).sum := by decide
  have hdescent : baseEnd_1137834 < baseStart_1137834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137841 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1137841 : Nat := 118140960795 + 1137841 * 2 ^ 59
def prefixEnd_1137841 : Nat := 4983230072969 + 3 ^ 40 * 1137841 * 2
def baseEnd_1137841 : Nat := 584259341392587925554671

theorem tailTrace_1137841 : CollatzResearch.WordTrace tailWord_1137841 prefixEnd_1137841 584259341392587925554671 := by
  unfold tailWord_1137841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41500470670803859616685377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27666980447202573077790251 41500470670803859616685377)
  ·
    refine ⟨31125353003102894712514033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41500470670803859616685377 31125353003102894712514033)
    ·
      refine ⟨23344014752327171034385525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31125353003102894712514033 23344014752327171034385525)
      ·
        refine ⟨2188501383030672284473643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23344014752327171034385525 2188501383030672284473643)
        ·
          refine ⟨3282752074546008426710465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188501383030672284473643 3282752074546008426710465)
          ·
            refine ⟨2462064055909506320032849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3282752074546008426710465 2462064055909506320032849)
            ·
              refine ⟨1846548041932129740024637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462064055909506320032849 1846548041932129740024637)
              ·
                refine ⟨692455515724548652509239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846548041932129740024637 692455515724548652509239)
                ·
                  refine ⟨1038683273586822978763859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692455515724548652509239 1038683273586822978763859)
                  ·
                    refine ⟨1558024910380234468145789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038683273586822978763859 1558024910380234468145789)
                    ·
                      refine ⟨584259341392587925554671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558024910380234468145789 584259341392587925554671)
                      ·
                        rfl

theorem cell23_1137841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1137841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137841 prefixEnd_1137841 := by exact prefixLift 1137841
  have htrace : WordTrace (prefixWord ++ tailWord_1137841) baseStart_1137841 baseEnd_1137841 := by
    simpa [prefixWord, tailWord_1137841, baseEnd_1137841] using wordTrace_append hprefix tailTrace_1137841
  have hstable : (prefixWord ++ tailWord_1137841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137841).length < 2 ^ (prefixWord ++ tailWord_1137841).sum := by decide
  have hdescent : baseEnd_1137841 < baseStart_1137841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137847 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 5, 2, 2]
def baseStart_1137847 : Nat := 118140960795 + 1137847 * 2 ^ 59
def prefixEnd_1137847 : Nat := 4983230072969 + 3 ^ 40 * 1137847 * 2
def baseEnd_1137847 : Nat := 584262422276514902079643

theorem tailTrace_1137847 : CollatzResearch.WordTrace tailWord_1137847 prefixEnd_1137847 584262422276514902079643 := by
  unfold tailWord_1137847
  simp only [CollatzResearch.WordTrace]
  refine ⟨41500689508782122641403795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27667126339188081760935863 41500689508782122641403795)
  ·
    refine ⟨62251034263173183962105693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41500689508782122641403795 62251034263173183962105693)
    ·
      refine ⟨23344137848689943985789635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62251034263173183962105693 23344137848689943985789635)
      ·
        refine ⟨35016206773034915978684453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23344137848689943985789635 35016206773034915978684453)
        ·
          refine ⟨6565538769944046746003335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35016206773034915978684453 6565538769944046746003335)
          ·
            refine ⟨9848308154916070119005003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565538769944046746003335 9848308154916070119005003)
            ·
              refine ⟨14772462232374105178507505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9848308154916070119005003 14772462232374105178507505)
              ·
                refine ⟨11079346674280578883880629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14772462232374105178507505 11079346674280578883880629)
                ·
                  refine ⟨1038688750713804270363809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11079346674280578883880629 1038688750713804270363809)
                  ·
                    refine ⟨779016563035353202772857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038688750713804270363809 779016563035353202772857)
                    ·
                      refine ⟨584262422276514902079643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779016563035353202772857 584262422276514902079643)
                      ·
                        rfl

theorem cell23_1137847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_1137847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137847 prefixEnd_1137847 := by exact prefixLift 1137847
  have htrace : WordTrace (prefixWord ++ tailWord_1137847) baseStart_1137847 baseEnd_1137847 := by
    simpa [prefixWord, tailWord_1137847, baseEnd_1137847] using wordTrace_append hprefix tailTrace_1137847
  have hstable : (prefixWord ++ tailWord_1137847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137847).length < 2 ^ (prefixWord ++ tailWord_1137847).sum := by decide
  have hdescent : baseEnd_1137847 < baseStart_1137847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137858 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1137858 : Nat := 118140960795 + 1137858 * 2 ^ 59
def prefixEnd_1137858 : Nat := 4983230072969 + 3 ^ 40 * 1137858 * 2
def baseEnd_1137858 : Nat := 584268070563714359042093

theorem tailTrace_1137858 : CollatzResearch.WordTrace tailWord_1137858 prefixEnd_1137858 584268070563714359042093 := by
  unfold tailWord_1137858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375272677935567880013557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27667393807828181013369485 10375272677935567880013557)
  ·
    refine ⟨972681813556459488751271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10375272677935567880013557 972681813556459488751271)
    ·
      refine ⟨1459022720334689233126907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972681813556459488751271 1459022720334689233126907)
      ·
        refine ⟨2188534080502033849690361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459022720334689233126907 2188534080502033849690361)
        ·
          refine ⟨1641400560376525387267771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188534080502033849690361 1641400560376525387267771)
          ·
            refine ⟨2462100840564788080901657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641400560376525387267771 2462100840564788080901657)
            ·
              refine ⟨1846575630423591060676243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462100840564788080901657 1846575630423591060676243)
              ·
                refine ⟨2769863445635386591014365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846575630423591060676243 2769863445635386591014365)
                ·
                  refine ⟨1038698792113269971630387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2769863445635386591014365 1038698792113269971630387)
                  ·
                    refine ⟨1558048188169904957445581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038698792113269971630387 1558048188169904957445581)
                    ·
                      refine ⟨584268070563714359042093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558048188169904957445581 584268070563714359042093)
                      ·
                        rfl

theorem cell23_1137858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1137858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137858 prefixEnd_1137858 := by exact prefixLift 1137858
  have htrace : WordTrace (prefixWord ++ tailWord_1137858) baseStart_1137858 baseEnd_1137858 := by
    simpa [prefixWord, tailWord_1137858, baseEnd_1137858] using wordTrace_append hprefix tailTrace_1137858
  have hstable : (prefixWord ++ tailWord_1137858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137858).length < 2 ^ (prefixWord ++ tailWord_1137858).sum := by decide
  have hdescent : baseEnd_1137858 < baseStart_1137858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137874 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_1137874 : Nat := 118140960795 + 1137874 * 2 ^ 59
def prefixEnd_1137874 : Nat := 4983230072969 + 3 ^ 40 * 1137874 * 2
def baseEnd_1137874 : Nat := 194758762084728765480673

theorem tailTrace_1137874 : CollatzResearch.WordTrace tailWord_1137874 prefixEnd_1137874 194758762084728765480673 := by
  unfold tailWord_1137874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375418569921076563159169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27667782853122870835091117 10375418569921076563159169)
  ·
    refine ⟨7781563927440807422369377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10375418569921076563159169 7781563927440807422369377)
    ·
      refine ⟨5836172945580605566777033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7781563927440807422369377 5836172945580605566777033)
      ·
        refine ⟨4377129709185454175082775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5836172945580605566777033 4377129709185454175082775)
        ·
          refine ⟨6565694563778181262624163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377129709185454175082775 6565694563778181262624163)
          ·
            refine ⟨9848541845667271893936245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565694563778181262624163 9848541845667271893936245)
            ·
              refine ⟨923300798031306740056523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9848541845667271893936245 923300798031306740056523)
              ·
                refine ⟨1384951197046960110084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923300798031306740056523 1384951197046960110084785)
                ·
                  refine ⟨1038713397785220082563589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1384951197046960110084785 1038713397785220082563589)
                  ·
                    refine ⟨194758762084728765480673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038713397785220082563589 194758762084728765480673)
                    ·
                      rfl

theorem cell23_1137874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_1137874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137874 prefixEnd_1137874 := by exact prefixLift 1137874
  have htrace : WordTrace (prefixWord ++ tailWord_1137874) baseStart_1137874 baseEnd_1137874 := by
    simpa [prefixWord, tailWord_1137874, baseEnd_1137874] using wordTrace_append hprefix tailTrace_1137874
  have hstable : (prefixWord ++ tailWord_1137874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137874).length < 2 ^ (prefixWord ++ tailWord_1137874).sum := by decide
  have hdescent : baseEnd_1137874 < baseStart_1137874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137877 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1137877 : Nat := 118140960795 + 1137877 * 2 ^ 59
def prefixEnd_1137877 : Nat := 4983230072969 + 3 ^ 40 * 1137877 * 2
def baseEnd_1137877 : Nat := 584277826696149784704505

theorem tailTrace_1137877 : CollatzResearch.WordTrace tailWord_1137877 prefixEnd_1137877 584277826696149784704505 := by
  unfold tailWord_1137877
  simp only [CollatzResearch.WordTrace]
  refine ⟨41501783698673437764995885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27667855799115625176663923 41501783698673437764995885)
  ·
    refine ⟨15563168887002539161873457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41501783698673437764995885 15563168887002539161873457)
    ·
      refine ⟨11672376665251904371405093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15563168887002539161873457 11672376665251904371405093)
      ·
        refine ⟨2188570624734732069638455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11672376665251904371405093 2188570624734732069638455)
        ·
          refine ⟨3282855937102098104457683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188570624734732069638455 3282855937102098104457683)
          ·
            refine ⟨4924283905653147156686525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282855937102098104457683 4924283905653147156686525)
            ·
              refine ⟨1846606464619930183757447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4924283905653147156686525 1846606464619930183757447)
              ·
                refine ⟨2769909696929895275636171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846606464619930183757447 2769909696929895275636171)
                ·
                  refine ⟨4154864545394842913454257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769909696929895275636171 4154864545394842913454257)
                  ·
                    refine ⟨3116148409046132185090693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4154864545394842913454257 3116148409046132185090693)
                    ·
                      refine ⟨584277826696149784704505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3116148409046132185090693 584277826696149784704505)
                      ·
                        rfl

theorem cell23_1137877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1137877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137877 prefixEnd_1137877 := by exact prefixLift 1137877
  have htrace : WordTrace (prefixWord ++ tailWord_1137877) baseStart_1137877 baseEnd_1137877 := by
    simpa [prefixWord, tailWord_1137877, baseEnd_1137877] using wordTrace_append hprefix tailTrace_1137877
  have hstable : (prefixWord ++ tailWord_1137877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137877).length < 2 ^ (prefixWord ++ tailWord_1137877).sum := by decide
  have hdescent : baseEnd_1137877 < baseStart_1137877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137898 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_1137898 : Nat := 118140960795 + 1137898 * 2 ^ 59
def prefixEnd_1137898 : Nat := 4983230072969 + 3 ^ 40 * 1137898 * 2
def baseEnd_1137898 : Nat := 584288609789894202541909

theorem tailTrace_1137898 : CollatzResearch.WordTrace tailWord_1137898 prefixEnd_1137898 584288609789894202541909 := by
  unfold tailWord_1137898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375637407899339587877587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27668366421064905567673565 10375637407899339587877587)
  ·
    refine ⟨15563456111849009381816381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10375637407899339587877587 15563456111849009381816381)
    ·
      refine ⟨5836296041943378518181143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15563456111849009381816381 5836296041943378518181143)
      ·
        refine ⟨8754444062915067777271715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836296041943378518181143 8754444062915067777271715)
        ·
          refine ⟨13131666094372601665907573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8754444062915067777271715 13131666094372601665907573)
          ·
            refine ⟨1231093696347431406178835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13131666094372601665907573 1231093696347431406178835)
            ·
              refine ⟨1846640544521147109268253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231093696347431406178835 1846640544521147109268253)
              ·
                refine ⟨692490204195430165975595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846640544521147109268253 692490204195430165975595)
                ·
                  refine ⟨1038735306293145248963393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692490204195430165975595 1038735306293145248963393)
                  ·
                    refine ⟨779051479719858936722545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038735306293145248963393 779051479719858936722545)
                    ·
                      refine ⟨584288609789894202541909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779051479719858936722545 584288609789894202541909)
                      ·
                        rfl

theorem cell23_1137898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_1137898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137898 prefixEnd_1137898 := by exact prefixLift 1137898
  have htrace : WordTrace (prefixWord ++ tailWord_1137898) baseStart_1137898 baseEnd_1137898 := by
    simpa [prefixWord, tailWord_1137898, baseEnd_1137898] using wordTrace_append hprefix tailTrace_1137898
  have hstable : (prefixWord ++ tailWord_1137898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137898).length < 2 ^ (prefixWord ++ tailWord_1137898).sum := by decide
  have hdescent : baseEnd_1137898 < baseStart_1137898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137910 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1137910 : Nat := 118140960795 + 1137910 * 2 ^ 59
def prefixEnd_1137910 : Nat := 4983230072969 + 3 ^ 40 * 1137910 * 2
def baseEnd_1137910 : Nat := 584294771557748155591853

theorem tailTrace_1137910 : CollatzResearch.WordTrace tailWord_1137910 prefixEnd_1137910 584294771557748155591853 := by
  unfold tailWord_1137910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593936706722117775059199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27668658205035922933964789 2593936706722117775059199)
  ·
    refine ⟨3890905060083176662588799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593936706722117775059199 3890905060083176662588799)
    ·
      refine ⟨5836357590124764993883199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890905060083176662588799 5836357590124764993883199)
      ·
        refine ⟨8754536385187147490824799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836357590124764993883199 8754536385187147490824799)
        ·
          refine ⟨13131804577780721236237199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8754536385187147490824799 13131804577780721236237199)
          ·
            refine ⟨19697706866671081854355799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13131804577780721236237199 19697706866671081854355799)
            ·
              refine ⟨29546560300006622781533699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19697706866671081854355799 29546560300006622781533699)
              ·
                refine ⟨44319840450009934172300549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29546560300006622781533699 44319840450009934172300549)
                ·
                  refine ⟨8309970084376862657306353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44319840450009934172300549 8309970084376862657306353)
                  ·
                    refine ⟨6232477563282646992979765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8309970084376862657306353 6232477563282646992979765)
                    ·
                      refine ⟨584294771557748155591853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6232477563282646992979765 584294771557748155591853)
                      ·
                        rfl

theorem cell23_1137910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1137910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137910 prefixEnd_1137910 := by exact prefixLift 1137910
  have htrace : WordTrace (prefixWord ++ tailWord_1137910) baseStart_1137910 baseEnd_1137910 := by
    simpa [prefixWord, tailWord_1137910, baseEnd_1137910] using wordTrace_append hprefix tailTrace_1137910
  have hstable : (prefixWord ++ tailWord_1137910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137910).length < 2 ^ (prefixWord ++ tailWord_1137910).sum := by decide
  have hdescent : baseEnd_1137910 < baseStart_1137910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137931 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 2, 1, 3]
def baseStart_1137931 : Nat := 118140960795 + 1137931 * 2 ^ 59
def prefixEnd_1137931 : Nat := 4983230072969 + 3 ^ 40 * 1137931 * 2
def baseEnd_1137931 : Nat := 584305554651492573429257

theorem tailTrace_1137931 : CollatzResearch.WordTrace tailWord_1137931 prefixEnd_1137931 584305554651492573429257 := by
  unfold tailWord_1137931
  simp only [CollatzResearch.WordTrace]
  refine ⟨41503753240477804987461647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27669168826985203324974431 41503753240477804987461647)
  ·
    refine ⟨62255629860716707481192471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41503753240477804987461647 62255629860716707481192471)
    ·
      refine ⟨93383444791075061221788707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62255629860716707481192471 93383444791075061221788707)
      ·
        refine ⟨140075167186612591832683061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93383444791075061221788707 140075167186612591832683061)
        ·
          refine ⟨13132046923744930484314037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140075167186612591832683061 13132046923744930484314037)
          ·
            refine ⟨1231129399101087232904441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13132046923744930484314037 1231129399101087232904441)
            ·
              refine ⟨923347049325815424678331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231129399101087232904441 923347049325815424678331)
              ·
                refine ⟨1385020573988723137017497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923347049325815424678331 1385020573988723137017497)
                ·
                  refine ⟨1038765430491542352763123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385020573988723137017497 1038765430491542352763123)
                  ·
                    refine ⟨1558148145737313529144685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038765430491542352763123 1558148145737313529144685)
                    ·
                      refine ⟨584305554651492573429257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558148145737313529144685 584305554651492573429257)
                      ·
                        rfl

theorem cell23_1137931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 1, 3].length) (baseStart_1137931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137931 prefixEnd_1137931 := by exact prefixLift 1137931
  have htrace : WordTrace (prefixWord ++ tailWord_1137931) baseStart_1137931 baseEnd_1137931 := by
    simpa [prefixWord, tailWord_1137931, baseEnd_1137931] using wordTrace_append hprefix tailTrace_1137931
  have hstable : (prefixWord ++ tailWord_1137931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137931).length < 2 ^ (prefixWord ++ tailWord_1137931).sum := by decide
  have hdescent : baseEnd_1137931 < baseStart_1137931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137937 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_1137937 : Nat := 118140960795 + 1137937 * 2 ^ 59
def prefixEnd_1137937 : Nat := 4983230072969 + 3 ^ 40 * 1137937 * 2
def baseEnd_1137937 : Nat := 584308635535419549954229

theorem tailTrace_1137937 : CollatzResearch.WordTrace tailWord_1137937 prefixEnd_1137937 584308635535419549954229 := by
  unfold tailWord_1137937
  simp only [CollatzResearch.WordTrace]
  refine ⟨41503972078456068012180065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27669314718970712008120043 41503972078456068012180065)
  ·
    refine ⟨31127979058842051009135049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41503972078456068012180065 31127979058842051009135049)
    ·
      refine ⟨23345984294131538256851287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31127979058842051009135049 23345984294131538256851287)
      ·
        refine ⟨35018976441197307385276931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23345984294131538256851287 35018976441197307385276931)
        ·
          refine ⟨52528464661795961077915397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35018976441197307385276931 52528464661795961077915397)
          ·
            refine ⟨9849087124086742702109137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52528464661795961077915397 9849087124086742702109137)
            ·
              refine ⟨7386815343065057026581853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9849087124086742702109137 7386815343065057026581853)
              ·
                refine ⟨2770055753649396384968195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7386815343065057026581853 2770055753649396384968195)
                ·
                  refine ⟨4155083630474094577452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770055753649396384968195 4155083630474094577452293)
                  ·
                    refine ⟨779078180713892733272305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155083630474094577452293 779078180713892733272305)
                    ·
                      refine ⟨584308635535419549954229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779078180713892733272305 584308635535419549954229)
                      ·
                        rfl

theorem cell23_1137937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_1137937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137937 prefixEnd_1137937 := by exact prefixLift 1137937
  have htrace : WordTrace (prefixWord ++ tailWord_1137937) baseStart_1137937 baseEnd_1137937 := by
    simpa [prefixWord, tailWord_1137937, baseEnd_1137937] using wordTrace_append hprefix tailTrace_1137937
  have hstable : (prefixWord ++ tailWord_1137937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137937).length < 2 ^ (prefixWord ++ tailWord_1137937).sum := by decide
  have hdescent : baseEnd_1137937 < baseStart_1137937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137971 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 2, 2, 2]
def baseStart_1137971 : Nat := 118140960795 + 1137971 * 2 ^ 59
def prefixEnd_1137971 : Nat := 4983230072969 + 3 ^ 40 * 1137971 * 2
def baseEnd_1137971 : Nat := 584326093877672416929073

theorem tailTrace_1137971 : CollatzResearch.WordTrace tailWord_1137971 prefixEnd_1137971 584326093877672416929073 := by
  unfold tailWord_1137971
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505212160332891818917767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27670141440221927879278511 41505212160332891818917767)
  ·
    refine ⟨62257818240499337728376651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41505212160332891818917767 62257818240499337728376651)
    ·
      refine ⟨93386727360749006592564977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62257818240499337728376651 93386727360749006592564977)
      ·
        refine ⟨70040045520561754944423733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93386727360749006592564977 70040045520561754944423733)
        ·
          refine ⟨6566254267552664526039725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70040045520561754944423733 6566254267552664526039725)
          ·
            refine ⟨2462345350332249197264897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6566254267552664526039725 2462345350332249197264897)
            ·
              refine ⟨1846759012749186897948673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462345350332249197264897 1846759012749186897948673)
              ·
                refine ⟨1385069259561890173461505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846759012749186897948673 1385069259561890173461505)
                ·
                  refine ⟨1038801944671417630096129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385069259561890173461505 1038801944671417630096129)
                  ·
                    refine ⟨779101458503563222572097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038801944671417630096129 779101458503563222572097)
                    ·
                      refine ⟨584326093877672416929073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779101458503563222572097 584326093877672416929073)
                      ·
                        rfl

theorem cell23_1137971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2, 2].length) (baseStart_1137971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137971 prefixEnd_1137971 := by exact prefixLift 1137971
  have htrace : WordTrace (prefixWord ++ tailWord_1137971) baseStart_1137971 baseEnd_1137971 := by
    simpa [prefixWord, tailWord_1137971, baseEnd_1137971] using wordTrace_append hprefix tailTrace_1137971
  have hstable : (prefixWord ++ tailWord_1137971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137971).length < 2 ^ (prefixWord ++ tailWord_1137971).sum := by decide
  have hdescent : baseEnd_1137971 < baseStart_1137971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137988 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1137988 : Nat := 118140960795 + 1137988 * 2 ^ 59
def prefixEnd_1137988 : Nat := 4983230072969 + 3 ^ 40 * 1137988 * 2
def baseEnd_1137988 : Nat := 584334823048798850416495

theorem tailTrace_1137988 : CollatzResearch.WordTrace tailWord_1137988 prefixEnd_1137988 584334823048798850416495 := by
  unfold tailWord_1137988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20752916100635651861143309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27670554800847535814857745 20752916100635651861143309)
  ·
    refine ⟨7782343537738369447928741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20752916100635651861143309 7782343537738369447928741)
    ·
      refine ⟨1459189413325944271486639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7782343537738369447928741 1459189413325944271486639)
      ·
        refine ⟨2188784119988916407229959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459189413325944271486639 2188784119988916407229959)
        ·
          refine ⟨3283176179983374610844939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188784119988916407229959 3283176179983374610844939)
          ·
            refine ⟨4924764269975061916267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3283176179983374610844939 4924764269975061916267409)
            ·
              refine ⟨3693573202481296437200557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924764269975061916267409 3693573202481296437200557)
              ·
                refine ⟨1385089950930486163950209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3693573202481296437200557 1385089950930486163950209)
                ·
                  refine ⟨1038817463197864622962657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385089950930486163950209 1038817463197864622962657)
                  ·
                    refine ⟨779113097398398467221993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038817463197864622962657 779113097398398467221993)
                    ·
                      refine ⟨584334823048798850416495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779113097398398467221993 584334823048798850416495)
                      ·
                        rfl

theorem cell23_1137988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1137988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1137988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1137988 prefixEnd_1137988 := by exact prefixLift 1137988
  have htrace : WordTrace (prefixWord ++ tailWord_1137988) baseStart_1137988 baseEnd_1137988 := by
    simpa [prefixWord, tailWord_1137988, baseEnd_1137988] using wordTrace_append hprefix tailTrace_1137988
  have hstable : (prefixWord ++ tailWord_1137988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137988).length < 2 ^ (prefixWord ++ tailWord_1137988).sum := by decide
  have hdescent : baseEnd_1137988 < baseStart_1137988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138007 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 2, 5]
def baseStart_1138007 : Nat := 118140960795 + 1138007 * 2 ^ 59
def prefixEnd_1138007 : Nat := 4983230072969 + 3 ^ 40 * 1138007 * 2
def baseEnd_1138007 : Nat := 194781526393744758692969

theorem tailTrace_1138007 : CollatzResearch.WordTrace tailWord_1138007 prefixEnd_1138007 194781526393744758692969 := by
  unfold tailWord_1138007
  simp only [CollatzResearch.WordTrace]
  refine ⟨41506525188202469967228275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27671016792134979978152183 41506525188202469967228275)
  ·
    refine ⟨62259787782303704950842413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41506525188202469967228275 62259787782303704950842413)
    ·
      refine ⟨23347420418363889356565905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62259787782303704950842413 23347420418363889356565905)
      ·
        refine ⟨17510565313772917017424429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23347420418363889356565905 17510565313772917017424429)
        ·
          refine ⟨6566461992664843881534161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17510565313772917017424429 6566461992664843881534161)
          ·
            refine ⟨4924846494498632911150621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6566461992664843881534161 4924846494498632911150621)
            ·
              refine ⟨1846817435436987341681483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4924846494498632911150621 1846817435436987341681483)
              ·
                refine ⟨2770226153155481012522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846817435436987341681483 2770226153155481012522225)
                ·
                  refine ⟨2077669614866610759391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770226153155481012522225 2077669614866610759391669)
                  ·
                    refine ⟨194781526393744758692969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2077669614866610759391669 194781526393744758692969)
                    ·
                      rfl

theorem cell23_1138007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_1138007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138007 prefixEnd_1138007 := by exact prefixLift 1138007
  have htrace : WordTrace (prefixWord ++ tailWord_1138007) baseStart_1138007 baseEnd_1138007 := by
    simpa [prefixWord, tailWord_1138007, baseEnd_1138007] using wordTrace_append hprefix tailTrace_1138007
  have hstable : (prefixWord ++ tailWord_1138007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138007).length < 2 ^ (prefixWord ++ tailWord_1138007).sum := by decide
  have hdescent : baseEnd_1138007 < baseStart_1138007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138088 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1138088 : Nat := 118140960795 + 1138088 * 2 ^ 59
def prefixEnd_1138088 : Nat := 4983230072969 + 3 ^ 40 * 1138088 * 2
def baseEnd_1138088 : Nat := 194795390371416153055345

theorem tailTrace_1138088 : CollatzResearch.WordTrace tailWord_1138088 prefixEnd_1138088 194795390371416153055345 := by
  unfold tailWord_1138088
  simp only [CollatzResearch.WordTrace]
  refine ⟨20754739750454510400463459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27672986333939347200617945 20754739750454510400463459)
  ·
    refine ⟨31132109625681765600695189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20754739750454510400463459 31132109625681765600695189)
    ·
      refine ⟨1459317638703832762532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31132109625681765600695189 1459317638703832762532587)
      ·
        refine ⟨2188976458055749143798881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459317638703832762532587 2188976458055749143798881)
        ·
          refine ⟨1641732343541811857849161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188976458055749143798881 1641732343541811857849161)
          ·
            refine ⟨1231299257656358893386871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641732343541811857849161 1231299257656358893386871)
            ·
              refine ⟨1846948886484538340080307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231299257656358893386871 1846948886484538340080307)
              ·
                refine ⟨2770423329726807510120461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846948886484538340080307 2770423329726807510120461)
                ·
                  refine ⟨1038908748647552816295173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2770423329726807510120461 1038908748647552816295173)
                  ·
                    refine ⟨194795390371416153055345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038908748647552816295173 194795390371416153055345)
                    ·
                      rfl

theorem cell23_1138088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1138088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138088 prefixEnd_1138088 := by exact prefixLift 1138088
  have htrace : WordTrace (prefixWord ++ tailWord_1138088) baseStart_1138088 baseEnd_1138088 := by
    simpa [prefixWord, tailWord_1138088, baseEnd_1138088] using wordTrace_append hprefix tailTrace_1138088
  have hstable : (prefixWord ++ tailWord_1138088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138088).length < 2 ^ (prefixWord ++ tailWord_1138088).sum := by decide
  have hdescent : baseEnd_1138088 < baseStart_1138088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138097 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1138097 : Nat := 118140960795 + 1138097 * 2 ^ 59
def prefixEnd_1138097 : Nat := 4983230072969 + 3 ^ 40 * 1138097 * 2
def baseEnd_1138097 : Nat := 194796930813379641317831

theorem tailTrace_1138097 : CollatzResearch.WordTrace tailWord_1138097 prefixEnd_1138097 194796930813379641317831 := by
  unfold tailWord_1138097
  simp only [CollatzResearch.WordTrace]
  refine ⟨41509807757876415338004545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27673205171917610225336363 41509807757876415338004545)
  ·
    refine ⟨31132355818407311503503409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41509807757876415338004545 31132355818407311503503409)
    ·
      refine ⟨23349266863805483627627557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31132355818407311503503409 23349266863805483627627557)
      ·
        refine ⟨4377987536963528180180167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23349266863805483627627557 4377987536963528180180167)
        ·
          refine ⟨6566981305445292270270251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4377987536963528180180167 6566981305445292270270251)
          ·
            refine ⟨9850471958167938405405377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6566981305445292270270251 9850471958167938405405377)
            ·
              refine ⟨7387853968625953804054033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9850471958167938405405377 7387853968625953804054033)
              ·
                refine ⟨5540890476469465353040525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7387853968625953804054033 5540890476469465353040525)
                ·
                  refine ⟨2077833928676049507390197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5540890476469465353040525 2077833928676049507390197)
                  ·
                    refine ⟨194796930813379641317831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2077833928676049507390197 194796930813379641317831)
                    ·
                      rfl

theorem cell23_1138097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1138097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138097 prefixEnd_1138097 := by exact prefixLift 1138097
  have htrace : WordTrace (prefixWord ++ tailWord_1138097) baseStart_1138097 baseEnd_1138097 := by
    simpa [prefixWord, tailWord_1138097, baseEnd_1138097] using wordTrace_append hprefix tailTrace_1138097
  have hstable : (prefixWord ++ tailWord_1138097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138097).length < 2 ^ (prefixWord ++ tailWord_1138097).sum := by decide
  have hdescent : baseEnd_1138097 < baseStart_1138097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138101 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 6]
def baseStart_1138101 : Nat := 118140960795 + 1138101 * 2 ^ 59
def prefixEnd_1138101 : Nat := 4983230072969 + 3 ^ 40 * 1138101 * 2
def baseEnd_1138101 : Nat := 64932538484750767589275

theorem tailTrace_1138101 : CollatzResearch.WordTrace tailWord_1138101 prefixEnd_1138101 64932538484750767589275 := by
  unfold tailWord_1138101
  simp only [CollatzResearch.WordTrace]
  refine ⟨41509953649861924021150157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27673302433241282680766771 41509953649861924021150157)
  ·
    refine ⟨15566232618698221507931309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41509953649861924021150157 15566232618698221507931309)
    ·
      refine ⟨5837337232011833065474241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15566232618698221507931309 5837337232011833065474241)
      ·
        refine ⟨4378002924008874799105681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5837337232011833065474241 4378002924008874799105681)
        ·
          refine ⟨3283502193006656099329261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4378002924008874799105681 3283502193006656099329261)
          ·
            refine ⟨1231313322377496037248473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3283502193006656099329261 1231313322377496037248473)
            ·
              refine ⟨923484991783122027936355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231313322377496037248473 923484991783122027936355)
              ·
                refine ⟨1385227487674683041904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923484991783122027936355 1385227487674683041904533)
                ·
                  refine ⟨64932538484750767589275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1385227487674683041904533 64932538484750767589275)
                  ·
                    rfl

theorem cell23_1138101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_1138101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138101 prefixEnd_1138101 := by exact prefixLift 1138101
  have htrace : WordTrace (prefixWord ++ tailWord_1138101) baseStart_1138101 baseEnd_1138101 := by
    simpa [prefixWord, tailWord_1138101, baseEnd_1138101] using wordTrace_append hprefix tailTrace_1138101
  have hstable : (prefixWord ++ tailWord_1138101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138101).length < 2 ^ (prefixWord ++ tailWord_1138101).sum := by decide
  have hdescent : baseEnd_1138101 < baseStart_1138101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138127 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 6, 4]
def baseStart_1138127 : Nat := 118140960795 + 1138127 * 2 ^ 59
def prefixEnd_1138127 : Nat := 4983230072969 + 3 ^ 40 * 1138127 * 2
def baseEnd_1138127 : Nat := 194802065619924602192785

theorem tailTrace_1138127 : CollatzResearch.WordTrace tailWord_1138127 prefixEnd_1138127 194802065619924602192785 := by
  unfold tailWord_1138127
  simp only [CollatzResearch.WordTrace]
  refine ⟨41510901947767730461596635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27673934631845153641064423 41510901947767730461596635)
  ·
    refine ⟨62266352921651595692394953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41510901947767730461596635 62266352921651595692394953)
    ·
      refine ⟨46699764691238696769296215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62266352921651595692394953 46699764691238696769296215)
      ·
        refine ⟨70049647036858045153944323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46699764691238696769296215 70049647036858045153944323)
        ·
          refine ⟨105074470555287067730916485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70049647036858045153944323 105074470555287067730916485)
          ·
            refine ⟨19701463229116325199546841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105074470555287067730916485 19701463229116325199546841)
            ·
              refine ⟨14776097421837243899660131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19701463229116325199546841 14776097421837243899660131)
              ·
                refine ⟨22164146132755865849490197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14776097421837243899660131 22164146132755865849490197)
                ·
                  refine ⟨1038944349972931211694853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22164146132755865849490197 1038944349972931211694853)
                  ·
                    refine ⟨194802065619924602192785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1038944349972931211694853 194802065619924602192785)
                    ·
                      rfl

theorem cell23_1138127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 4].length) (baseStart_1138127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138127 prefixEnd_1138127 := by exact prefixLift 1138127
  have htrace : WordTrace (prefixWord ++ tailWord_1138127) baseStart_1138127 baseEnd_1138127 := by
    simpa [prefixWord, tailWord_1138127, baseEnd_1138127] using wordTrace_append hprefix tailTrace_1138127
  have hstable : (prefixWord ++ tailWord_1138127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138127).length < 2 ^ (prefixWord ++ tailWord_1138127).sum := by decide
  have hdescent : baseEnd_1138127 < baseStart_1138127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138140 : List Nat := [2, 2, 19]
def baseStart_1138140 : Nat := 118140960795 + 1138140 * 2 ^ 59
def prefixEnd_1138140 : Nat := 4983230072969 + 3 ^ 40 * 1138140 * 2
def baseEnd_1138140 : Nat := 89073749749776292595

theorem tailTrace_1138140 : CollatzResearch.WordTrace tailWord_1138140 prefixEnd_1138140 89073749749776292595 := by
  unfold tailWord_1138140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20755688048360316840909937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27674250731147089121213249 20755688048360316840909937)
  ·
    refine ⟨15566766036270237630682453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20755688048360316840909937 15566766036270237630682453)
    ·
      refine ⟨89073749749776292595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 15566766036270237630682453 89073749749776292595)
      ·
        rfl

theorem cell23_1138140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 19].length) (baseStart_1138140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138140 prefixEnd_1138140 := by exact prefixLift 1138140
  have htrace : WordTrace (prefixWord ++ tailWord_1138140) baseStart_1138140 baseEnd_1138140 := by
    simpa [prefixWord, tailWord_1138140, baseEnd_1138140] using wordTrace_append hprefix tailTrace_1138140
  have hstable : (prefixWord ++ tailWord_1138140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138140).length < 2 ^ (prefixWord ++ tailWord_1138140).sum := by decide
  have hdescent : baseEnd_1138140 < baseStart_1138140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138145 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_1138145 : Nat := 118140960795 + 1138145 * 2 ^ 59
def prefixEnd_1138145 : Nat := 4983230072969 + 3 ^ 40 * 1138145 * 2
def baseEnd_1138145 : Nat := 584415439511554736153273

theorem tailTrace_1138145 : CollatzResearch.WordTrace tailWord_1138145 prefixEnd_1138145 584415439511554736153273 := by
  unfold tailWord_1138145
  simp only [CollatzResearch.WordTrace]
  refine ⟨41511558461702519535751889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27674372307801679690501259 41511558461702519535751889)
  ·
    refine ⟨31133668846276889651813917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41511558461702519535751889 31133668846276889651813917)
    ·
      refine ⟨11675125817353833619430219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31133668846276889651813917 11675125817353833619430219)
      ·
        refine ⟨17512688726030750429145329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11675125817353833619430219 17512688726030750429145329)
        ·
          refine ⟨13134516544523062821858997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17512688726030750429145329 13134516544523062821858997)
          ·
            refine ⟨1231360926049037139549281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13134516544523062821858997 1231360926049037139549281)
            ·
              refine ⟨923520694536777854661961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231360926049037139549281 923520694536777854661961)
              ·
                refine ⟨692640520902583390996471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923520694536777854661961 692640520902583390996471)
                ·
                  refine ⟨1038960781353875086494707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692640520902583390996471 1038960781353875086494707)
                  ·
                    refine ⟨1558441172030812629742061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038960781353875086494707 1558441172030812629742061)
                    ·
                      refine ⟨584415439511554736153273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558441172030812629742061 584415439511554736153273)
                      ·
                        rfl

theorem cell23_1138145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_1138145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138145 prefixEnd_1138145 := by exact prefixLift 1138145
  have htrace : WordTrace (prefixWord ++ tailWord_1138145) baseStart_1138145 baseEnd_1138145 := by
    simpa [prefixWord, tailWord_1138145, baseEnd_1138145] using wordTrace_append hprefix tailTrace_1138145
  have hstable : (prefixWord ++ tailWord_1138145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138145).length < 2 ^ (prefixWord ++ tailWord_1138145).sum := by decide
  have hdescent : baseEnd_1138145 < baseStart_1138145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138184 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_1138184 : Nat := 118140960795 + 1138184 * 2 ^ 59
def prefixEnd_1138184 : Nat := 4983230072969 + 3 ^ 40 * 1138184 * 2
def baseEnd_1138184 : Nat := 584435465257080083565593

theorem tailTrace_1138184 : CollatzResearch.WordTrace tailWord_1138184 prefixEnd_1138184 584435465257080083565593 := by
  unfold tailWord_1138184
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756490454280614598210803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27675320605707486130947737 20756490454280614598210803)
  ·
    refine ⟨31134735681420921897316205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20756490454280614598210803 31134735681420921897316205)
    ·
      refine ⟨11675525880532845711493577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31134735681420921897316205 11675525880532845711493577)
      ·
        refine ⟨8756644410399634283620183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11675525880532845711493577 8756644410399634283620183)
        ·
          refine ⟨13134966615599451425430275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756644410399634283620183 13134966615599451425430275)
          ·
            refine ⟨19702449923399177138145413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13134966615599451425430275 19702449923399177138145413)
            ·
              refine ⟨3694209360637345713402265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19702449923399177138145413 3694209360637345713402265)
              ·
                refine ⟨2770657020478009285051699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694209360637345713402265 2770657020478009285051699)
                ·
                  refine ⟨4155985530717013927577549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2770657020478009285051699 4155985530717013927577549)
                  ·
                    refine ⟨1558494574018880222841581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4155985530717013927577549 1558494574018880222841581)
                    ·
                      refine ⟨584435465257080083565593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558494574018880222841581 584435465257080083565593)
                      ·
                        rfl

theorem cell23_1138184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_1138184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138184 prefixEnd_1138184 := by exact prefixLift 1138184
  have htrace : WordTrace (prefixWord ++ tailWord_1138184) baseStart_1138184 baseEnd_1138184 := by
    simpa [prefixWord, tailWord_1138184, baseEnd_1138184] using wordTrace_append hprefix tailTrace_1138184
  have hstable : (prefixWord ++ tailWord_1138184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138184).length < 2 ^ (prefixWord ++ tailWord_1138184).sum := by decide
  have hdescent : baseEnd_1138184 < baseStart_1138184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138207 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1138207 : Nat := 118140960795 + 1138207 * 2 ^ 59
def prefixEnd_1138207 : Nat := 4983230072969 + 3 ^ 40 * 1138207 * 2
def baseEnd_1138207 : Nat := 584447275312133493577987

theorem tailTrace_1138207 : CollatzResearch.WordTrace tailWord_1138207 prefixEnd_1138207 584447275312133493577987 := by
  unfold tailWord_1138207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41513819787477904124508875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27675879858318602749672583 41513819787477904124508875)
  ·
    refine ⟨62270729681216856186763313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41513819787477904124508875 62270729681216856186763313)
    ·
      refine ⟨46703047260912642140072485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62270729681216856186763313 46703047260912642140072485)
      ·
        refine ⟨8756821361421120401263591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46703047260912642140072485 8756821361421120401263591)
        ·
          refine ⟨13135232042131680601895387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756821361421120401263591 13135232042131680601895387)
          ·
            refine ⟨19702848063197520902843081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13135232042131680601895387 19702848063197520902843081)
            ·
              refine ⟨14777136047398140677132311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19702848063197520902843081 14777136047398140677132311)
              ·
                refine ⟨22165704071097211015698467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14777136047398140677132311 22165704071097211015698467)
                ·
                  refine ⟨33248556106645816523547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22165704071097211015698467 33248556106645816523547701)
                  ·
                    refine ⟨3117052134998045299082597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33248556106645816523547701 3117052134998045299082597)
                    ·
                      refine ⟨584447275312133493577987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3117052134998045299082597 584447275312133493577987)
                      ·
                        rfl

theorem cell23_1138207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1138207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138207 prefixEnd_1138207 := by exact prefixLift 1138207
  have htrace : WordTrace (prefixWord ++ tailWord_1138207) baseStart_1138207 baseEnd_1138207 := by
    simpa [prefixWord, tailWord_1138207, baseEnd_1138207] using wordTrace_append hprefix tailTrace_1138207
  have hstable : (prefixWord ++ tailWord_1138207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138207).length < 2 ^ (prefixWord ++ tailWord_1138207).sum := by decide
  have hdescent : baseEnd_1138207 < baseStart_1138207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138241 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1138241 : Nat := 118140960795 + 1138241 * 2 ^ 59
def prefixEnd_1138241 : Nat := 4983230072969 + 3 ^ 40 * 1138241 * 2
def baseEnd_1138241 : Nat := 584464733654386360552831

theorem tailTrace_1138241 : CollatzResearch.WordTrace tailWord_1138241 prefixEnd_1138241 584464733654386360552831 := by
  unfold tailWord_1138241
  simp only [CollatzResearch.WordTrace]
  refine ⟨41515059869354727931246577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27676706579569818620831051 41515059869354727931246577)
  ·
    refine ⟨31136294902016045948434933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41515059869354727931246577 31136294902016045948434933)
    ·
      refine ⟨2919027647064004307665775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31136294902016045948434933 2919027647064004307665775)
      ·
        refine ⟨4378541470596006461498663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919027647064004307665775 4378541470596006461498663)
        ·
          refine ⟨6567812205894009692247995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378541470596006461498663 6567812205894009692247995)
          ·
            refine ⟨9851718308841014538371993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567812205894009692247995 9851718308841014538371993)
            ·
              refine ⟨7388788731630760903778995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851718308841014538371993 7388788731630760903778995)
              ·
                refine ⟨11083183097446141355668493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388788731630760903778995 11083183097446141355668493)
                ·
                  refine ⟨4156193661542303008375685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11083183097446141355668493 4156193661542303008375685)
                  ·
                    refine ⟨779286311539181814070441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4156193661542303008375685 779286311539181814070441)
                    ·
                      refine ⟨584464733654386360552831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779286311539181814070441 584464733654386360552831)
                      ·
                        rfl

theorem cell23_1138241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1138241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138241 prefixEnd_1138241 := by exact prefixLift 1138241
  have htrace : WordTrace (prefixWord ++ tailWord_1138241) baseStart_1138241 baseEnd_1138241 := by
    simpa [prefixWord, tailWord_1138241, baseEnd_1138241] using wordTrace_append hprefix tailTrace_1138241
  have hstable : (prefixWord ++ tailWord_1138241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138241).length < 2 ^ (prefixWord ++ tailWord_1138241).sum := by decide
  have hdescent : baseEnd_1138241 < baseStart_1138241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138257 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1138257 : Nat := 118140960795 + 1138257 * 2 ^ 59
def prefixEnd_1138257 : Nat := 4983230072969 + 3 ^ 40 * 1138257 * 2
def baseEnd_1138257 : Nat := 584472949344858297952757

theorem tailTrace_1138257 : CollatzResearch.WordTrace tailWord_1138257 prefixEnd_1138257 584472949344858297952757 := by
  unfold tailWord_1138257
  simp only [CollatzResearch.WordTrace]
  refine ⟨41515643437296762663829025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27677095624864508442552683 41515643437296762663829025)
  ·
    refine ⟨31136732577972571997871769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41515643437296762663829025 31136732577972571997871769)
    ·
      refine ⟨23352549433479428998403827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31136732577972571997871769 23352549433479428998403827)
      ·
        refine ⟨35028824150219143497605741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23352549433479428998403827 35028824150219143497605741)
        ·
          refine ⟨13135809056332178811602153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35028824150219143497605741 13135809056332178811602153)
          ·
            refine ⟨9851856792249134108701615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13135809056332178811602153 9851856792249134108701615)
            ·
              refine ⟨14777785188373701163052423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9851856792249134108701615 14777785188373701163052423)
              ·
                refine ⟨22166677782560551744578635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14777785188373701163052423 22166677782560551744578635)
                ·
                  refine ⟨33250016673840827616867953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22166677782560551744578635 33250016673840827616867953)
                  ·
                    refine ⟨24937512505380620712650965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33250016673840827616867953 24937512505380620712650965)
                    ·
                      refine ⟨584472949344858297952757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24937512505380620712650965 584472949344858297952757)
                      ·
                        rfl

theorem cell23_1138257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1138257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138257 prefixEnd_1138257 := by exact prefixLift 1138257
  have htrace : WordTrace (prefixWord ++ tailWord_1138257) baseStart_1138257 baseEnd_1138257 := by
    simpa [prefixWord, tailWord_1138257, baseEnd_1138257] using wordTrace_append hprefix tailTrace_1138257
  have hstable : (prefixWord ++ tailWord_1138257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138257).length < 2 ^ (prefixWord ++ tailWord_1138257).sum := by decide
  have hdescent : baseEnd_1138257 < baseStart_1138257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138258 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_1138258 : Nat := 118140960795 + 1138258 * 2 ^ 59
def prefixEnd_1138258 : Nat := 4983230072969 + 3 ^ 40 * 1138258 * 2
def baseEnd_1138258 : Nat := 584473462825512794040253

theorem tailTrace_1138258 : CollatzResearch.WordTrace tailWord_1138258 prefixEnd_1138258 584473462825512794040253 := by
  unfold tailWord_1138258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378919977573284958653857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27677119940195426556410285 10378919977573284958653857)
  ·
    refine ⟨7784189983179963718990393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10378919977573284958653857 7784189983179963718990393)
    ·
      refine ⟨5838142487384972789242795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7784189983179963718990393 5838142487384972789242795)
      ·
        refine ⟨8757213731077459183864193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838142487384972789242795 8757213731077459183864193)
        ·
          refine ⟨6567910298308094387898145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8757213731077459183864193 6567910298308094387898145)
          ·
            refine ⟨4925932723731070790923609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6567910298308094387898145 4925932723731070790923609)
            ·
              refine ⟨3694449542798303093192707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4925932723731070790923609 3694449542798303093192707)
              ·
                refine ⟨5541674314197454639789061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694449542798303093192707 5541674314197454639789061)
                ·
                  refine ⟨1039063933912022744960449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5541674314197454639789061 1039063933912022744960449)
                  ·
                    refine ⟨779297950434017058720337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1039063933912022744960449 779297950434017058720337)
                    ·
                      refine ⟨584473462825512794040253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779297950434017058720337 584473462825512794040253)
                      ·
                        rfl

theorem cell23_1138258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_1138258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138258 prefixEnd_1138258 := by exact prefixLift 1138258
  have htrace : WordTrace (prefixWord ++ tailWord_1138258) baseStart_1138258 baseEnd_1138258 := by
    simpa [prefixWord, tailWord_1138258, baseEnd_1138258] using wordTrace_append hprefix tailTrace_1138258
  have hstable : (prefixWord ++ tailWord_1138258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138258).length < 2 ^ (prefixWord ++ tailWord_1138258).sum := by decide
  have hdescent : baseEnd_1138258 < baseStart_1138258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138269 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1138269 : Nat := 118140960795 + 1138269 * 2 ^ 59
def prefixEnd_1138269 : Nat := 4983230072969 + 3 ^ 40 * 1138269 * 2
def baseEnd_1138269 : Nat := 584479111112712251002703

theorem tailTrace_1138269 : CollatzResearch.WordTrace tailWord_1138269 prefixEnd_1138269 584479111112712251002703 := by
  unfold tailWord_1138269
  simp only [CollatzResearch.WordTrace]
  refine ⟨41516081113253288713265861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27677387408835525808843907 41516081113253288713265861)
  ·
    refine ⟨7784265208734991633737349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41516081113253288713265861 7784265208734991633737349)
    ·
      refine ⟨1459549726637810931325753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7784265208734991633737349 1459549726637810931325753)
      ·
        refine ⟨1094662294978358198494315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1459549726637810931325753 1094662294978358198494315)
        ·
          refine ⟨1641993442467537297741473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094662294978358198494315 1641993442467537297741473)
          ·
            refine ⟨1231495081850652973306105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641993442467537297741473 1231495081850652973306105)
            ·
              refine ⟨923621311387989729979579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231495081850652973306105 923621311387989729979579)
              ·
                refine ⟨1385431967081984594969369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923621311387989729979579 1385431967081984594969369)
                ·
                  refine ⟨1039073975311488446227027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385431967081984594969369 1039073975311488446227027)
                  ·
                    refine ⟨1558610962967232669340541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039073975311488446227027 1558610962967232669340541)
                    ·
                      refine ⟨584479111112712251002703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558610962967232669340541 584479111112712251002703)
                      ·
                        rfl

theorem cell23_1138269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1138269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138269 prefixEnd_1138269 := by exact prefixLift 1138269
  have htrace : WordTrace (prefixWord ++ tailWord_1138269) baseStart_1138269 baseEnd_1138269 := by
    simpa [prefixWord, tailWord_1138269, baseEnd_1138269] using wordTrace_append hprefix tailTrace_1138269
  have hstable : (prefixWord ++ tailWord_1138269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138269).length < 2 ^ (prefixWord ++ tailWord_1138269).sum := by decide
  have hdescent : baseEnd_1138269 < baseStart_1138269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138275 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 2, 2, 2]
def baseStart_1138275 : Nat := 118140960795 + 1138275 * 2 ^ 59
def prefixEnd_1138275 : Nat := 4983230072969 + 3 ^ 40 * 1138275 * 2
def baseEnd_1138275 : Nat := 584482191996639227527675

theorem tailTrace_1138275 : CollatzResearch.WordTrace tailWord_1138275 prefixEnd_1138275 584482191996639227527675 := by
  unfold tailWord_1138275
  simp only [CollatzResearch.WordTrace]
  refine ⟨41516299951231551737984279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27677533300821034491989519 41516299951231551737984279)
  ·
    refine ⟨62274449926847327606976419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41516299951231551737984279 62274449926847327606976419)
    ·
      refine ⟨93411674890270991410464629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62274449926847327606976419 93411674890270991410464629)
      ·
        refine ⟨8757344520962905444731059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93411674890270991410464629 8757344520962905444731059)
        ·
          refine ⟨13136016781444358167096589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757344520962905444731059 13136016781444358167096589)
          ·
            refine ⟨4926006293041634312661221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13136016781444358167096589 4926006293041634312661221)
            ·
              refine ⟨923626179945306433623979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4926006293041634312661221 923626179945306433623979)
              ·
                refine ⟨1385439269917959650435969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923626179945306433623979 1385439269917959650435969)
                ·
                  refine ⟨1039079452438469737826977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385439269917959650435969 1039079452438469737826977)
                  ·
                    refine ⟨779309589328852303370233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1039079452438469737826977 779309589328852303370233)
                    ·
                      refine ⟨584482191996639227527675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779309589328852303370233 584482191996639227527675)
                      ·
                        rfl

theorem cell23_1138275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_1138275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138275 prefixEnd_1138275 := by exact prefixLift 1138275
  have htrace : WordTrace (prefixWord ++ tailWord_1138275) baseStart_1138275 baseEnd_1138275 := by
    simpa [prefixWord, tailWord_1138275, baseEnd_1138275] using wordTrace_append hprefix tailTrace_1138275
  have hstable : (prefixWord ++ tailWord_1138275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138275).length < 2 ^ (prefixWord ++ tailWord_1138275).sum := by decide
  have hdescent : baseEnd_1138275 < baseStart_1138275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138287 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7]
def baseStart_1138287 : Nat := 118140960795 + 1138287 * 2 ^ 59
def prefixEnd_1138287 : Nat := 4983230072969 + 3 ^ 40 * 1138287 * 2
def baseEnd_1138287 : Nat := 584488353764493180577619

theorem tailTrace_1138287 : CollatzResearch.WordTrace tailWord_1138287 prefixEnd_1138287 584488353764493180577619 := by
  unfold tailWord_1138287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41516737627188077787421115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27677825084792051858280743 41516737627188077787421115)
  ·
    refine ⟨62275106440782116681131673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41516737627188077787421115 62275106440782116681131673)
    ·
      refine ⟨46706329830586587510848755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62275106440782116681131673 46706329830586587510848755)
      ·
        refine ⟨70059494745879881266273133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46706329830586587510848755 70059494745879881266273133)
        ·
          refine ⟨26272310529704955474852425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70059494745879881266273133 26272310529704955474852425)
          ·
            refine ⟨19704232897278716606139319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26272310529704955474852425 19704232897278716606139319)
            ·
              refine ⟨29556349345918074909208979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19704232897278716606139319 29556349345918074909208979)
              ·
                refine ⟨44334524018877112363813469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29556349345918074909208979 44334524018877112363813469)
                ·
                  refine ⟨16625446507078917136430051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44334524018877112363813469 16625446507078917136430051)
                  ·
                    refine ⟨24938169760618375704645077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16625446507078917136430051 24938169760618375704645077)
                    ·
                      refine ⟨584488353764493180577619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24938169760618375704645077 584488353764493180577619)
                      ·
                        rfl

theorem cell23_1138287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_1138287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138287 prefixEnd_1138287 := by exact prefixLift 1138287
  have htrace : WordTrace (prefixWord ++ tailWord_1138287) baseStart_1138287 baseEnd_1138287 := by
    simpa [prefixWord, tailWord_1138287, baseEnd_1138287] using wordTrace_append hprefix tailTrace_1138287
  have hstable : (prefixWord ++ tailWord_1138287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138287).length < 2 ^ (prefixWord ++ tailWord_1138287).sum := by decide
  have hdescent : baseEnd_1138287 < baseStart_1138287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138384 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_1138384 : Nat := 118140960795 + 1138384 * 2 ^ 59
def prefixEnd_1138384 : Nat := 4983230072969 + 3 ^ 40 * 1138384 * 2
def baseEnd_1138384 : Nat := 194846053795993100354891

theorem tailTrace_1138384 : CollatzResearch.WordTrace tailWord_1138384 prefixEnd_1138384 194846053795993100354891 := by
  unfold tailWord_1138384
  simp only [CollatzResearch.WordTrace]
  refine ⟨20760137753918331676851103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27680183671891108902468137 20760137753918331676851103)
  ·
    refine ⟨31140206630877497515276655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20760137753918331676851103 31140206630877497515276655)
    ·
      refine ⟨46710309946316246272914983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31140206630877497515276655 46710309946316246272914983)
      ·
        refine ⟨70065464919474369409372475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46710309946316246272914983 70065464919474369409372475)
        ·
          refine ⟨105098197379211554114058713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70065464919474369409372475 105098197379211554114058713)
          ·
            refine ⟨78823648034408665585544035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105098197379211554114058713 78823648034408665585544035)
            ·
              refine ⟨118235472051612998378316053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78823648034408665585544035 118235472051612998378316053)
              ·
                refine ⟨5542287752419359298983565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118235472051612998378316053 5542287752419359298983565)
                ·
                  refine ⟨2078357907157259737118837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542287752419359298983565 2078357907157259737118837)
                  ·
                    refine ⟨194846053795993100354891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2078357907157259737118837 194846053795993100354891)
                    ·
                      rfl

theorem cell23_1138384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_1138384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138384 prefixEnd_1138384 := by exact prefixLift 1138384
  have htrace : WordTrace (prefixWord ++ tailWord_1138384) baseStart_1138384 baseEnd_1138384 := by
    simpa [prefixWord, tailWord_1138384, baseEnd_1138384] using wordTrace_append hprefix tailTrace_1138384
  have hstable : (prefixWord ++ tailWord_1138384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138384).length < 2 ^ (prefixWord ++ tailWord_1138384).sum := by decide
  have hdescent : baseEnd_1138384 < baseStart_1138384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138391 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 5, 2]
def baseStart_1138391 : Nat := 118140960795 + 1138391 * 2 ^ 59
def prefixEnd_1138391 : Nat := 4983230072969 + 3 ^ 40 * 1138391 * 2
def baseEnd_1138391 : Nat := 584541755752560773677141

theorem tailTrace_1138391 : CollatzResearch.WordTrace tailWord_1138391 prefixEnd_1138391 584541755752560773677141 := by
  unfold tailWord_1138391
  simp only [CollatzResearch.WordTrace]
  refine ⟨41520530818811303549207027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27680353879207535699471351 41520530818811303549207027)
  ·
    refine ⟨62280796228216955323810541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41520530818811303549207027 62280796228216955323810541)
    ·
      refine ⟨23355298585581358246428953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62280796228216955323810541 23355298585581358246428953)
      ·
        refine ⟨17516473939186018684821715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23355298585581358246428953 17516473939186018684821715)
        ·
          refine ⟨26274710908779028027232573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17516473939186018684821715 26274710908779028027232573)
          ·
            refine ⟨9853016590792135510212215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26274710908779028027232573 9853016590792135510212215)
            ·
              refine ⟨14779524886188203265318323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9853016590792135510212215 14779524886188203265318323)
              ·
                refine ⟨22169287329282304897977485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14779524886188203265318323 22169287329282304897977485)
                ·
                  refine ⟨8313482748480864336741557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22169287329282304897977485 8313482748480864336741557)
                  ·
                    refine ⟨779389007670081031569521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8313482748480864336741557 779389007670081031569521)
                    ·
                      refine ⟨584541755752560773677141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779389007670081031569521 584541755752560773677141)
                      ·
                        rfl

theorem cell23_1138391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_1138391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138391 prefixEnd_1138391 := by exact prefixLift 1138391
  have htrace : WordTrace (prefixWord ++ tailWord_1138391) baseStart_1138391 baseEnd_1138391 := by
    simpa [prefixWord, tailWord_1138391, baseEnd_1138391] using wordTrace_append hprefix tailTrace_1138391
  have hstable : (prefixWord ++ tailWord_1138391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138391).length < 2 ^ (prefixWord ++ tailWord_1138391).sum := by decide
  have hdescent : baseEnd_1138391 < baseStart_1138391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138408 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1138408 : Nat := 118140960795 + 1138408 * 2 ^ 59
def prefixEnd_1138408 : Nat := 4983230072969 + 3 ^ 40 * 1138408 * 2
def baseEnd_1138408 : Nat := 584550484923687207164563

theorem tailTrace_1138408 : CollatzResearch.WordTrace tailWord_1138408 prefixEnd_1138408 584550484923687207164563 := by
  unfold tailWord_1138408
  simp only [CollatzResearch.WordTrace]
  refine ⟨20760575429874857726287939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27680767239833143635050585 20760575429874857726287939)
  ·
    refine ⟨31140863144812286589431909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20760575429874857726287939 31140863144812286589431909)
    ·
      refine ⟨5838911839652303735518483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31140863144812286589431909 5838911839652303735518483)
      ·
        refine ⟨8758367759478455603277725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838911839652303735518483 8758367759478455603277725)
        ·
          refine ⟨3284387909804420851229147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8758367759478455603277725 3284387909804420851229147)
          ·
            refine ⟨4926581864706631276843721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284387909804420851229147 4926581864706631276843721)
            ·
              refine ⟨3694936398529973457632791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4926581864706631276843721 3694936398529973457632791)
              ·
                refine ⟨5542404597794960186449187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3694936398529973457632791 5542404597794960186449187)
                ·
                  refine ⟨8313606896692440279673781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5542404597794960186449187 8313606896692440279673781)
                  ·
                    refine ⟨779400646564916276219417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8313606896692440279673781 779400646564916276219417)
                    ·
                      refine ⟨584550484923687207164563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779400646564916276219417 584550484923687207164563)
                      ·
                        rfl

theorem cell23_1138408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1138408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138408 prefixEnd_1138408 := by exact prefixLift 1138408
  have htrace : WordTrace (prefixWord ++ tailWord_1138408) baseStart_1138408 baseEnd_1138408 := by
    simpa [prefixWord, tailWord_1138408, baseEnd_1138408] using wordTrace_append hprefix tailTrace_1138408
  have hstable : (prefixWord ++ tailWord_1138408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138408).length < 2 ^ (prefixWord ++ tailWord_1138408).sum := by decide
  have hdescent : baseEnd_1138408 < baseStart_1138408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138431 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 4, 4]
def baseStart_1138431 : Nat := 118140960795 + 1138431 * 2 ^ 59
def prefixEnd_1138431 : Nat := 4983230072969 + 3 ^ 40 * 1138431 * 2
def baseEnd_1138431 : Nat := 194854098326246872392319

theorem tailTrace_1138431 : CollatzResearch.WordTrace tailWord_1138431 prefixEnd_1138431 194854098326246872392319 := by
  unfold tailWord_1138431
  simp only [CollatzResearch.WordTrace]
  refine ⟨41521989738666390380663147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27681326492444260253775431 41521989738666390380663147)
  ·
    refine ⟨62282984607999585570994721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41521989738666390380663147 62282984607999585570994721)
    ·
      refine ⟨46712238455999689178246041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62282984607999585570994721 46712238455999689178246041)
      ·
        refine ⟨35034178841999766883684531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46712238455999689178246041 35034178841999766883684531)
        ·
          refine ⟨52551268262999650325526797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35034178841999766883684531 52551268262999650325526797)
          ·
            refine ⟨19706725598624868872072549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52551268262999650325526797 19706725598624868872072549)
            ·
              refine ⟨3695011049742162913513603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19706725598624868872072549 3695011049742162913513603)
              ·
                refine ⟨5542516574613244370270405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695011049742162913513603 5542516574613244370270405)
                ·
                  refine ⟨1039221857739983319425701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5542516574613244370270405 1039221857739983319425701)
                  ·
                    refine ⟨194854098326246872392319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039221857739983319425701 194854098326246872392319)
                    ·
                      rfl

theorem cell23_1138431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 4, 4].length) (baseStart_1138431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138431 prefixEnd_1138431 := by exact prefixLift 1138431
  have htrace : WordTrace (prefixWord ++ tailWord_1138431) baseStart_1138431 baseEnd_1138431 := by
    simpa [prefixWord, tailWord_1138431, baseEnd_1138431] using wordTrace_append hprefix tailTrace_1138431
  have hstable : (prefixWord ++ tailWord_1138431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138431).length < 2 ^ (prefixWord ++ tailWord_1138431).sum := by decide
  have hdescent : baseEnd_1138431 < baseStart_1138431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138441 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_1138441 : Nat := 118140960795 + 1138441 * 2 ^ 59
def prefixEnd_1138441 : Nat := 4983230072969 + 3 ^ 40 * 1138441 * 2
def baseEnd_1138441 : Nat := 584567429785285578051911

theorem tailTrace_1138441 : CollatzResearch.WordTrace tailWord_1138441 prefixEnd_1138441 584567429785285578051911 := by
  unfold tailWord_1138441
  simp only [CollatzResearch.WordTrace]
  refine ⟨41522354468630162088527177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27681569645753441392351451 41522354468630162088527177)
  ·
    refine ⟨31141765851472621566395383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41522354468630162088527177 31141765851472621566395383)
    ·
      refine ⟨46712648777208932349593075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31141765851472621566395383 46712648777208932349593075)
      ·
        refine ⟨70068973165813398524389613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46712648777208932349593075 70068973165813398524389613)
        ·
          refine ⟨26275864937180024446646105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70068973165813398524389613 26275864937180024446646105)
          ·
            refine ⟨19706898702885018334984579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26275864937180024446646105 19706898702885018334984579)
            ·
              refine ⟨29560348054327527502476869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19706898702885018334984579 29560348054327527502476869)
              ·
                refine ⟨5542565260186411406714413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29560348054327527502476869 5542565260186411406714413)
                ·
                  refine ⟨2078461972569904277517905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542565260186411406714413 2078461972569904277517905)
                  ·
                    refine ⟨1558846479427428208138429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078461972569904277517905 1558846479427428208138429)
                    ·
                      refine ⟨584567429785285578051911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558846479427428208138429 584567429785285578051911)
                      ·
                        rfl

theorem cell23_1138441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_1138441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138441 prefixEnd_1138441 := by exact prefixLift 1138441
  have htrace : WordTrace (prefixWord ++ tailWord_1138441) baseStart_1138441 baseEnd_1138441 := by
    simpa [prefixWord, tailWord_1138441, baseEnd_1138441] using wordTrace_append hprefix tailTrace_1138441
  have hstable : (prefixWord ++ tailWord_1138441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138441).length < 2 ^ (prefixWord ++ tailWord_1138441).sum := by decide
  have hdescent : baseEnd_1138441 < baseStart_1138441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138444 : List Nat := [2, 2, 1, 2, 2, 1, 3, 10]
def baseStart_1138444 : Nat := 118140960795 + 1138444 * 2 ^ 59
def prefixEnd_1138444 : Nat := 4983230072969 + 3 ^ 40 * 1138444 * 2
def baseEnd_1138444 : Nat := 21650702601009224678311

theorem tailTrace_1138444 : CollatzResearch.WordTrace tailWord_1138444 prefixEnd_1138444 21650702601009224678311 := by
  unfold tailWord_1138444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761231943809646800443193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27681642591746195733924257 20761231943809646800443193)
  ·
    refine ⟨15570923957857235100332395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20761231943809646800443193 15570923957857235100332395)
    ·
      refine ⟨23356385936785852650498593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15570923957857235100332395 23356385936785852650498593)
      ·
        refine ⟨17517289452589389487873945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23356385936785852650498593 17517289452589389487873945)
        ·
          refine ⟨13137967089442042115905459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17517289452589389487873945 13137967089442042115905459)
          ·
            refine ⟨19706950634163063173858189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13137967089442042115905459 19706950634163063173858189)
            ·
              refine ⟨7390106487811148690196821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19706950634163063173858189 7390106487811148690196821)
              ·
                refine ⟨21650702601009224678311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7390106487811148690196821 21650702601009224678311)
                ·
                  rfl

theorem cell23_1138444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 10].length) (baseStart_1138444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138444 prefixEnd_1138444 := by exact prefixLift 1138444
  have htrace : WordTrace (prefixWord ++ tailWord_1138444) baseStart_1138444 baseEnd_1138444 := by
    simpa [prefixWord, tailWord_1138444, baseEnd_1138444] using wordTrace_append hprefix tailTrace_1138444
  have hstable : (prefixWord ++ tailWord_1138444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138444).length < 2 ^ (prefixWord ++ tailWord_1138444).sum := by decide
  have hdescent : baseEnd_1138444 < baseStart_1138444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138452 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1138452 : Nat := 118140960795 + 1138452 * 2 ^ 59
def prefixEnd_1138452 : Nat := 4983230072969 + 3 ^ 40 * 1138452 * 2
def baseEnd_1138452 : Nat := 194857692690828345004787

theorem tailTrace_1138452 : CollatzResearch.WordTrace tailWord_1138452 prefixEnd_1138452 194857692690828345004787 := by
  unfold tailWord_1138452
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761377835795155483588805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27681837114393540644785073 20761377835795155483588805)
  ·
    refine ⟨3892758344211591653172901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20761377835795155483588805 3892758344211591653172901)
    ·
      refine ⟨729892189539673434969919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3892758344211591653172901 729892189539673434969919)
      ·
        refine ⟨1094838284309510152454879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729892189539673434969919 1094838284309510152454879)
        ·
          refine ⟨1642257426464265228682319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094838284309510152454879 1642257426464265228682319)
          ·
            refine ⟨2463386139696397843023479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642257426464265228682319 2463386139696397843023479)
            ·
              refine ⟨3695079209544596764535219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463386139696397843023479 3695079209544596764535219)
              ·
                refine ⟨5542618814316895146802829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695079209544596764535219 5542618814316895146802829)
                ·
                  refine ⟨2078482055368835680051061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542618814316895146802829 2078482055368835680051061)
                  ·
                    refine ⟨194857692690828345004787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2078482055368835680051061 194857692690828345004787)
                    ·
                      rfl

theorem cell23_1138452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1138452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138452 prefixEnd_1138452 := by exact prefixLift 1138452
  have htrace : WordTrace (prefixWord ++ tailWord_1138452) baseStart_1138452 baseEnd_1138452 := by
    simpa [prefixWord, tailWord_1138452, baseEnd_1138452] using wordTrace_append hprefix tailTrace_1138452
  have hstable : (prefixWord ++ tailWord_1138452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138452).length < 2 ^ (prefixWord ++ tailWord_1138452).sum := by decide
  have hdescent : baseEnd_1138452 < baseStart_1138452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138455 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1138455 : Nat := 118140960795 + 1138455 * 2 ^ 59
def prefixEnd_1138455 : Nat := 4983230072969 + 3 ^ 40 * 1138455 * 2
def baseEnd_1138455 : Nat := 584574618514448523276847

theorem tailTrace_1138455 : CollatzResearch.WordTrace tailWord_1138455 prefixEnd_1138455 584574618514448523276847 := by
  unfold tailWord_1138455
  simp only [CollatzResearch.WordTrace]
  refine ⟨41522865090579442479536819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27681910060386294986357879 41522865090579442479536819)
  ·
    refine ⟨62284297635869163719305229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41522865090579442479536819 62284297635869163719305229)
    ·
      refine ⟨23356611613450936394739461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62284297635869163719305229 23356611613450936394739461)
      ·
        refine ⟨4379364677522050574013649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23356611613450936394739461 4379364677522050574013649)
        ·
          refine ⟨3284523508141537930510237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4379364677522050574013649 3284523508141537930510237)
          ·
            refine ⟨1231696315553076723941339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3284523508141537930510237 1231696315553076723941339)
            ·
              refine ⟨1847544473329615085912009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231696315553076723941339 1847544473329615085912009)
              ·
                refine ⟨1385658354997211314434007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847544473329615085912009 1385658354997211314434007)
                ·
                  refine ⟨2078487532495816971651011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385658354997211314434007 2078487532495816971651011)
                  ·
                    refine ⟨3117731298743725457476517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2078487532495816971651011 3117731298743725457476517)
                    ·
                      refine ⟨584574618514448523276847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3117731298743725457476517 584574618514448523276847)
                      ·
                        rfl

theorem cell23_1138455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1138455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138455 prefixEnd_1138455 := by exact prefixLift 1138455
  have htrace : WordTrace (prefixWord ++ tailWord_1138455) baseStart_1138455 baseEnd_1138455 := by
    simpa [prefixWord, tailWord_1138455, baseEnd_1138455] using wordTrace_append hprefix tailTrace_1138455
  have hstable : (prefixWord ++ tailWord_1138455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138455).length < 2 ^ (prefixWord ++ tailWord_1138455).sum := by decide
  have hdescent : baseEnd_1138455 < baseStart_1138455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138458 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1138458 : Nat := 118140960795 + 1138458 * 2 ^ 59
def prefixEnd_1138458 : Nat := 4983230072969 + 3 ^ 40 * 1138458 * 2
def baseEnd_1138458 : Nat := 584576158956412011539333

theorem tailTrace_1138458 : CollatzResearch.WordTrace tailWord_1138458 prefixEnd_1138458 584576158956412011539333 := by
  unfold tailWord_1138458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380743627392143497974007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27681983006379049327930685 10380743627392143497974007)
  ·
    refine ⟨15571115441088215246961011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10380743627392143497974007 15571115441088215246961011)
    ·
      refine ⟨23356673161632322870441517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15571115441088215246961011 23356673161632322870441517)
      ·
        refine ⟨8758752435612121076415569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23356673161632322870441517 8758752435612121076415569)
        ·
          refine ⟨6569064326709090807311677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8758752435612121076415569 6569064326709090807311677)
          ·
            refine ⟨2463399122515909052741879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6569064326709090807311677 2463399122515909052741879)
            ·
              refine ⟨3695098683773863579112819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463399122515909052741879 3695098683773863579112819)
              ·
                refine ⟨5542648025660795368669229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695098683773863579112819 5542648025660795368669229)
                ·
                  refine ⟨2078493009622798263250961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5542648025660795368669229 2078493009622798263250961)
                  ·
                    refine ⟨1558869757217098697438221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078493009622798263250961 1558869757217098697438221)
                    ·
                      refine ⟨584576158956412011539333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1558869757217098697438221 584576158956412011539333)
                      ·
                        rfl

theorem cell23_1138458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1138458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138458 prefixEnd_1138458 := by exact prefixLift 1138458
  have htrace : WordTrace (prefixWord ++ tailWord_1138458) baseStart_1138458 baseEnd_1138458 := by
    simpa [prefixWord, tailWord_1138458, baseEnd_1138458] using wordTrace_append hprefix tailTrace_1138458
  have hstable : (prefixWord ++ tailWord_1138458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138458).length < 2 ^ (prefixWord ++ tailWord_1138458).sum := by decide
  have hdescent : baseEnd_1138458 < baseStart_1138458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138468 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1138468 : Nat := 118140960795 + 1138468 * 2 ^ 59
def prefixEnd_1138468 : Nat := 4983230072969 + 3 ^ 40 * 1138468 * 2
def baseEnd_1138468 : Nat := 584581293762956972414287

theorem tailTrace_1138468 : CollatzResearch.WordTrace tailWord_1138468 prefixEnd_1138468 584581293762956972414287 := by
  unfold tailWord_1138468
  simp only [CollatzResearch.WordTrace]
  refine ⟨20761669619766172849880029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27682226159688230466506705 20761669619766172849880029)
  ·
    refine ⟨7785626107412314818705011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20761669619766172849880029 7785626107412314818705011)
    ·
      refine ⟨11678439161118472228057517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7785626107412314818705011 11678439161118472228057517)
      ·
        refine ⟨4379414685419427085521569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11678439161118472228057517 4379414685419427085521569)
        ·
          refine ⟨3284561014064570314141177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4379414685419427085521569 3284561014064570314141177)
          ·
            refine ⟨2463420760548427735605883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284561014064570314141177 2463420760548427735605883)
            ·
              refine ⟨3695131140822641603408825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463420760548427735605883 3695131140822641603408825)
              ·
                refine ⟨2771348355616981202556619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695131140822641603408825 2771348355616981202556619)
                ·
                  refine ⟨4157022533425471803834929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771348355616981202556619 4157022533425471803834929)
                  ·
                    refine ⟨3117766900069103852876197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4157022533425471803834929 3117766900069103852876197)
                    ·
                      refine ⟨584581293762956972414287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3117766900069103852876197 584581293762956972414287)
                      ·
                        rfl

theorem cell23_1138468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1138468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138468 prefixEnd_1138468 := by exact prefixLift 1138468
  have htrace : WordTrace (prefixWord ++ tailWord_1138468) baseStart_1138468 baseEnd_1138468 := by
    simpa [prefixWord, tailWord_1138468, baseEnd_1138468] using wordTrace_append hprefix tailTrace_1138468
  have hstable : (prefixWord ++ tailWord_1138468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138468).length < 2 ^ (prefixWord ++ tailWord_1138468).sum := by decide
  have hdescent : baseEnd_1138468 < baseStart_1138468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138478 : List Nat := [4, 1, 3, 2, 3, 10]
def baseStart_1138478 : Nat := 118140960795 + 1138478 * 2 ^ 59
def prefixEnd_1138478 : Nat := 4983230072969 + 3 ^ 40 * 1138478 * 2
def baseEnd_1138478 : Nat := 2405705467364205486787

theorem tailTrace_1138478 : CollatzResearch.WordTrace tailWord_1138478 prefixEnd_1138478 2405705467364205486787 := by
  unfold tailWord_1138478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190462996187014675953011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27682469312997411605082725 5190462996187014675953011)
  ·
    refine ⟨7785694494280522013929517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190462996187014675953011 7785694494280522013929517)
    ·
      refine ⟨2919635435355195755223569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7785694494280522013929517 2919635435355195755223569)
      ·
        refine ⟨2189726576516396816417677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2919635435355195755223569 2189726576516396816417677)
        ·
          refine ⟨821147466193648806156629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2189726576516396816417677 821147466193648806156629)
          ·
            refine ⟨2405705467364205486787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 821147466193648806156629 2405705467364205486787)
            ·
              rfl

theorem cell23_1138478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 10].length) (baseStart_1138478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138478 prefixEnd_1138478 := by exact prefixLift 1138478
  have htrace : WordTrace (prefixWord ++ tailWord_1138478) baseStart_1138478 baseEnd_1138478 := by
    simpa [prefixWord, tailWord_1138478, baseEnd_1138478] using wordTrace_append hprefix tailTrace_1138478
  have hstable : (prefixWord ++ tailWord_1138478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138478).length < 2 ^ (prefixWord ++ tailWord_1138478).sum := by decide
  have hdescent : baseEnd_1138478 < baseStart_1138478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138502 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1138502 : Nat := 118140960795 + 1138502 * 2 ^ 59
def prefixEnd_1138502 : Nat := 4983230072969 + 3 ^ 40 * 1138502 * 2
def baseEnd_1138502 : Nat := 584598752105209839389131

theorem tailTrace_1138502 : CollatzResearch.WordTrace tailWord_1138502 prefixEnd_1138502 584598752105209839389131 := by
  unfold tailWord_1138502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297643103794036547078055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27683052880939446337665173 1297643103794036547078055)
  ·
    refine ⟨1946464655691054820617083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297643103794036547078055 1946464655691054820617083)
    ·
      refine ⟨2919696983536582230925625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946464655691054820617083 2919696983536582230925625)
      ·
        refine ⟨2189772737652436673194219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2919696983536582230925625 2189772737652436673194219)
        ·
          refine ⟨3284659106478655009791329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2189772737652436673194219 3284659106478655009791329)
          ·
            refine ⟨2463494329858991257343497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284659106478655009791329 2463494329858991257343497)
            ·
              refine ⟨1847620747394243443007623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2463494329858991257343497 1847620747394243443007623)
              ·
                refine ⟨2771431121091365164511435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847620747394243443007623 2771431121091365164511435)
                ·
                  refine ⟨4157146681637047746767153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771431121091365164511435 4157146681637047746767153)
                  ·
                    refine ⟨3117860011227785810075365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4157146681637047746767153 3117860011227785810075365)
                    ·
                      refine ⟨584598752105209839389131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3117860011227785810075365 584598752105209839389131)
                      ·
                        rfl

theorem cell23_1138502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1138502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138502 prefixEnd_1138502 := by exact prefixLift 1138502
  have htrace : WordTrace (prefixWord ++ tailWord_1138502) baseStart_1138502 baseEnd_1138502 := by
    simpa [prefixWord, tailWord_1138502, baseEnd_1138502] using wordTrace_append hprefix tailTrace_1138502
  have hstable : (prefixWord ++ tailWord_1138502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138502).length < 2 ^ (prefixWord ++ tailWord_1138502).sum := by decide
  have hdescent : baseEnd_1138502 < baseStart_1138502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138532 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_1138532 : Nat := 118140960795 + 1138532 * 2 ^ 59
def prefixEnd_1138532 : Nat := 4983230072969 + 3 ^ 40 * 1138532 * 2
def baseEnd_1138532 : Nat := 584614156524844722013993

theorem tailTrace_1138532 : CollatzResearch.WordTrace tailWord_1138532 prefixEnd_1138532 584614156524844722013993 := by
  unfold tailWord_1138532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762836755650242315044925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27683782340866989753393233 20762836755650242315044925)
  ·
    refine ⟨7786063783368840868141847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20762836755650242315044925 7786063783368840868141847)
    ·
      refine ⟨11679095675053261302212771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7786063783368840868141847 11679095675053261302212771)
      ·
        refine ⟨17518643512579891953319157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11679095675053261302212771 17518643512579891953319157)
        ·
          refine ⟨1642372829304364870623671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17518643512579891953319157 1642372829304364870623671)
          ·
            refine ⟨2463559243956547305935507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642372829304364870623671 2463559243956547305935507)
            ·
              refine ⟨3695338865934820958903261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463559243956547305935507 3695338865934820958903261)
              ·
                refine ⟨1385752074725557859588723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3695338865934820958903261 1385752074725557859588723)
                ·
                  refine ⟨2078628112088336789383085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385752074725557859588723 2078628112088336789383085)
                  ·
                    refine ⟨779485542033126296018657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078628112088336789383085 779485542033126296018657)
                    ·
                      refine ⟨584614156524844722013993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779485542033126296018657 584614156524844722013993)
                      ·
                        rfl

theorem cell23_1138532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_1138532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138532 prefixEnd_1138532 := by exact prefixLift 1138532
  have htrace : WordTrace (prefixWord ++ tailWord_1138532) baseStart_1138532 baseEnd_1138532 := by
    simpa [prefixWord, tailWord_1138532, baseEnd_1138532] using wordTrace_append hprefix tailTrace_1138532
  have hstable : (prefixWord ++ tailWord_1138532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138532).length < 2 ^ (prefixWord ++ tailWord_1138532).sum := by decide
  have hdescent : baseEnd_1138532 < baseStart_1138532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138545 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_1138545 : Nat := 118140960795 + 1138545 * 2 ^ 59
def prefixEnd_1138545 : Nat := 4983230072969 + 3 ^ 40 * 1138545 * 2
def baseEnd_1138545 : Nat := 584620831773353171151433

theorem tailTrace_1138545 : CollatzResearch.WordTrace tailWord_1138545 prefixEnd_1138545 584620831773353171151433 := by
  unfold tailWord_1138545
  simp only [CollatzResearch.WordTrace]
  refine ⟨41526147660253387850313089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27684098440168925233542059 41526147660253387850313089)
  ·
    refine ⟨31144610745190040887734817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41526147660253387850313089 31144610745190040887734817)
    ·
      refine ⟨23358458058892530665801113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31144610745190040887734817 23358458058892530665801113)
      ·
        refine ⟨17518843544169397999350835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23358458058892530665801113 17518843544169397999350835)
        ·
          refine ⟨26278265316254096999026253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17518843544169397999350835 26278265316254096999026253)
          ·
            refine ⟨9854349493595286374634845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26278265316254096999026253 9854349493595286374634845)
            ·
              refine ⟨3695381060098232390488067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9854349493595286374634845 3695381060098232390488067)
              ·
                refine ⟨5543071590147348585732101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695381060098232390488067 5543071590147348585732101)
                ·
                  refine ⟨1039325923152627859824769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5543071590147348585732101 1039325923152627859824769)
                  ·
                    refine ⟨779494442364470894868577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1039325923152627859824769 779494442364470894868577)
                    ·
                      refine ⟨584620831773353171151433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779494442364470894868577 584620831773353171151433)
                      ·
                        rfl

theorem cell23_1138545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_1138545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138545 prefixEnd_1138545 := by exact prefixLift 1138545
  have htrace : WordTrace (prefixWord ++ tailWord_1138545) baseStart_1138545 baseEnd_1138545 := by
    simpa [prefixWord, tailWord_1138545, baseEnd_1138545] using wordTrace_append hprefix tailTrace_1138545
  have hstable : (prefixWord ++ tailWord_1138545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138545).length < 2 ^ (prefixWord ++ tailWord_1138545).sum := by decide
  have hdescent : baseEnd_1138545 < baseStart_1138545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138581 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1138581 : Nat := 118140960795 + 1138581 * 2 ^ 59
def prefixEnd_1138581 : Nat := 4983230072969 + 3 ^ 40 * 1138581 * 2
def baseEnd_1138581 : Nat := 194879772358971676767089

theorem tailTrace_1138581 : CollatzResearch.WordTrace tailWord_1138581 prefixEnd_1138581 194879772358971676767089 := by
  unfold tailWord_1138581
  simp only [CollatzResearch.WordTrace]
  refine ⟨41527460688122965998623597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27684973792081977332415731 41527460688122965998623597)
  ·
    refine ⟨15572797758046112249483849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41527460688122965998623597 15572797758046112249483849)
    ·
      refine ⟨11679598318534584187112887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15572797758046112249483849 11679598318534584187112887)
      ·
        refine ⟨17519397477801876280669331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11679598318534584187112887 17519397477801876280669331)
        ·
          refine ⟨26279096216702814421003997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17519397477801876280669331 26279096216702814421003997)
          ·
            refine ⟨9854661081263555407876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26279096216702814421003997 9854661081263555407876499)
            ·
              refine ⟨14781991621895333111814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9854661081263555407876499 14781991621895333111814749)
              ·
                refine ⟨5543246858210749916930531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14781991621895333111814749 5543246858210749916930531)
                ·
                  refine ⟨8314870287316124875395797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5543246858210749916930531 8314870287316124875395797)
                  ·
                    refine ⟨194879772358971676767089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8314870287316124875395797 194879772358971676767089)
                    ·
                      rfl

theorem cell23_1138581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1138581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138581 prefixEnd_1138581 := by exact prefixLift 1138581
  have htrace : WordTrace (prefixWord ++ tailWord_1138581) baseStart_1138581 baseEnd_1138581 := by
    simpa [prefixWord, tailWord_1138581, baseEnd_1138581] using wordTrace_append hprefix tailTrace_1138581
  have hstable : (prefixWord ++ tailWord_1138581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138581).length < 2 ^ (prefixWord ++ tailWord_1138581).sum := by decide
  have hdescent : baseEnd_1138581 < baseStart_1138581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138601 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_1138601 : Nat := 118140960795 + 1138601 * 2 ^ 59
def prefixEnd_1138601 : Nat := 4983230072969 + 3 ^ 40 * 1138601 * 2
def baseEnd_1138601 : Nat := 584649586690004952051175

theorem tailTrace_1138601 : CollatzResearch.WordTrace tailWord_1138601 prefixEnd_1138601 584649586690004952051175 := by
  unfold tailWord_1138601
  simp only [CollatzResearch.WordTrace]
  refine ⟨41528190148050509414351657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27685460098700339609567771 41528190148050509414351657)
  ·
    refine ⟨31146142611037882060763743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41528190148050509414351657 31146142611037882060763743)
    ·
      refine ⟨46719213916556823091145615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31146142611037882060763743 46719213916556823091145615)
      ·
        refine ⟨70078820874835234636718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46719213916556823091145615 70078820874835234636718423)
        ·
          refine ⟨105118231312252851955077635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70078820874835234636718423 105118231312252851955077635)
          ·
            refine ⟨157677346968379277932616453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105118231312252851955077635 157677346968379277932616453)
            ·
              refine ⟨29564502556571114612365585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157677346968379277932616453 29564502556571114612365585)
              ·
                refine ⟨22173376917428335959274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29564502556571114612365585 22173376917428335959274189)
                ·
                  refine ⟨8315016344035625984727821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22173376917428335959274189 8315016344035625984727821)
                  ·
                    refine ⟨3118131129013359744272933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8315016344035625984727821 3118131129013359744272933)
                    ·
                      refine ⟨584649586690004952051175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3118131129013359744272933 584649586690004952051175)
                      ·
                        rfl

theorem cell23_1138601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_1138601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138601 prefixEnd_1138601 := by exact prefixLift 1138601
  have htrace : WordTrace (prefixWord ++ tailWord_1138601) baseStart_1138601 baseEnd_1138601 := by
    simpa [prefixWord, tailWord_1138601, baseEnd_1138601] using wordTrace_append hprefix tailTrace_1138601
  have hstable : (prefixWord ++ tailWord_1138601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138601).length < 2 ^ (prefixWord ++ tailWord_1138601).sum := by decide
  have hdescent : baseEnd_1138601 < baseStart_1138601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138631 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1138631 : Nat := 118140960795 + 1138631 * 2 ^ 59
def prefixEnd_1138631 : Nat := 4983230072969 + 3 ^ 40 * 1138631 * 2
def baseEnd_1138631 : Nat := 584664991109639834676037

theorem tailTrace_1138631 : CollatzResearch.WordTrace tailWord_1138631 prefixEnd_1138631 584664991109639834676037 := by
  unfold tailWord_1138631
  simp only [CollatzResearch.WordTrace]
  refine ⟨41529284337941824537943747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27686189558627883025295831 41529284337941824537943747)
  ·
    refine ⟨62293926506912736806915621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41529284337941824537943747 62293926506912736806915621)
    ·
      refine ⟨11680111220046138151296679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62293926506912736806915621 11680111220046138151296679)
      ·
        refine ⟨17520166830069207226945019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11680111220046138151296679 17520166830069207226945019)
        ·
          refine ⟨26280250245103810840417529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520166830069207226945019 26280250245103810840417529)
          ·
            refine ⟨19710187683827858130313147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26280250245103810840417529 19710187683827858130313147)
            ·
              refine ⟨29565281525741787195469721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19710187683827858130313147 29565281525741787195469721)
              ·
                refine ⟨22173961144306340396602291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29565281525741787195469721 22173961144306340396602291)
                ·
                  refine ⟨33260941716459510594903437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22173961144306340396602291 33260941716459510594903437)
                  ·
                    refine ⟨12472853143672316473088789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33260941716459510594903437 12472853143672316473088789)
                    ·
                      refine ⟨584664991109639834676037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12472853143672316473088789 584664991109639834676037)
                      ·
                        rfl

theorem cell23_1138631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1138631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138631 prefixEnd_1138631 := by exact prefixLift 1138631
  have htrace : WordTrace (prefixWord ++ tailWord_1138631) baseStart_1138631 baseEnd_1138631 := by
    simpa [prefixWord, tailWord_1138631, baseEnd_1138631] using wordTrace_append hprefix tailTrace_1138631
  have hstable : (prefixWord ++ tailWord_1138631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138631).length < 2 ^ (prefixWord ++ tailWord_1138631).sum := by decide
  have hdescent : baseEnd_1138631 < baseStart_1138631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138641 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 8]
def baseStart_1138641 : Nat := 118140960795 + 1138641 * 2 ^ 59
def prefixEnd_1138641 : Nat := 4983230072969 + 3 ^ 40 * 1138641 * 2
def baseEnd_1138641 : Nat := 64963347324020532838999

theorem tailTrace_1138641 : CollatzResearch.WordTrace tailWord_1138641 prefixEnd_1138641 64963347324020532838999 := by
  unfold tailWord_1138641
  simp only [CollatzResearch.WordTrace]
  refine ⟨41529649067905596245807777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27686432711937064163871851 41529649067905596245807777)
  ·
    refine ⟨31147236800929197184355833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41529649067905596245807777 31147236800929197184355833)
    ·
      refine ⟨23360427600696897888266875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31147236800929197184355833 23360427600696897888266875)
      ·
        refine ⟨35040641401045346832400313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23360427600696897888266875 35040641401045346832400313)
        ·
          refine ⟨26280481050784010124300235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35040641401045346832400313 26280481050784010124300235)
          ·
            refine ⟨39420721576176015186450353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26280481050784010124300235 39420721576176015186450353)
            ·
              refine ⟨29565541182132011389837765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39420721576176015186450353 29565541182132011389837765)
              ·
                refine ⟨5543538971649752135594581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29565541182132011389837765 5543538971649752135594581)
                ·
                  refine ⟨64963347324020532838999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5543538971649752135594581 64963347324020532838999)
                  ·
                    rfl

theorem cell23_1138641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_1138641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138641 prefixEnd_1138641 := by exact prefixLift 1138641
  have htrace : WordTrace (prefixWord ++ tailWord_1138641) baseStart_1138641 baseEnd_1138641 := by
    simpa [prefixWord, tailWord_1138641, baseEnd_1138641] using wordTrace_append hprefix tailTrace_1138641
  have hstable : (prefixWord ++ tailWord_1138641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138641).length < 2 ^ (prefixWord ++ tailWord_1138641).sum := by decide
  have hdescent : baseEnd_1138641 < baseStart_1138641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138655 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1138655 : Nat := 118140960795 + 1138655 * 2 ^ 59
def prefixEnd_1138655 : Nat := 4983230072969 + 3 ^ 40 * 1138655 * 2
def baseEnd_1138655 : Nat := 584677314645347740775927

theorem tailTrace_1138655 : CollatzResearch.WordTrace tailWord_1138655 prefixEnd_1138655 584677314645347740775927 := by
  unfold tailWord_1138655
  simp only [CollatzResearch.WordTrace]
  refine ⟨41530159689854876636817419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27686773126569917757878279 41530159689854876636817419)
  ·
    refine ⟨62295239534782314955226129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41530159689854876636817419 62295239534782314955226129)
    ·
      refine ⟨46721429651086736216419597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62295239534782314955226129 46721429651086736216419597)
      ·
        refine ⟨17520536119157526081157349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46721429651086736216419597 17520536119157526081157349)
        ·
          refine ⟨3285100522342036140217003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17520536119157526081157349 3285100522342036140217003)
          ·
            refine ⟨4927650783513054210325505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285100522342036140217003 4927650783513054210325505)
            ·
              refine ⟨3695738087634790657744129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4927650783513054210325505 3695738087634790657744129)
              ·
                refine ⟨2771803565726092993308097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695738087634790657744129 2771803565726092993308097)
                ·
                  refine ⟨2078852674294569744981073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2771803565726092993308097 2078852674294569744981073)
                  ·
                    refine ⟨1559139505720927308735805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2078852674294569744981073 1559139505720927308735805)
                    ·
                      refine ⟨584677314645347740775927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1559139505720927308735805 584677314645347740775927)
                      ·
                        rfl

theorem cell23_1138655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1138655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138655 prefixEnd_1138655 := by exact prefixLift 1138655
  have htrace : WordTrace (prefixWord ++ tailWord_1138655) baseStart_1138655 baseEnd_1138655 := by
    simpa [prefixWord, tailWord_1138655, baseEnd_1138655] using wordTrace_append hprefix tailTrace_1138655
  have hstable : (prefixWord ++ tailWord_1138655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138655).length < 2 ^ (prefixWord ++ tailWord_1138655).sum := by decide
  have hdescent : baseEnd_1138655 < baseStart_1138655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138669 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1138669 : Nat := 118140960795 + 1138669 * 2 ^ 59
def prefixEnd_1138669 : Nat := 4983230072969 + 3 ^ 40 * 1138669 * 2
def baseEnd_1138669 : Nat := 584684503374510686000863

theorem tailTrace_1138669 : CollatzResearch.WordTrace tailWord_1138669 prefixEnd_1138669 584684503374510686000863 := by
  unfold tailWord_1138669
  simp only [CollatzResearch.WordTrace]
  refine ⟨41530670311804157027827061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27687113541202771351884707 41530670311804157027827061)
  ·
    refine ⟨3893500341731639721358787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41530670311804157027827061 3893500341731639721358787)
    ·
      refine ⟨5840250512597459582038181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893500341731639721358787 5840250512597459582038181)
      ·
        refine ⟨1095046971112023671632159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5840250512597459582038181 1095046971112023671632159)
        ·
          refine ⟨1642570456668035507448239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095046971112023671632159 1642570456668035507448239)
          ·
            refine ⟨2463855685002053261172359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642570456668035507448239 2463855685002053261172359)
            ·
              refine ⟨3695783527503079891758539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463855685002053261172359 3695783527503079891758539)
              ·
                refine ⟨5543675291254619837637809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695783527503079891758539 5543675291254619837637809)
                ·
                  refine ⟨4157756468440964878228357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5543675291254619837637809 4157756468440964878228357)
                  ·
                    refine ⟨779579337832680914667817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4157756468440964878228357 779579337832680914667817)
                    ·
                      refine ⟨584684503374510686000863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779579337832680914667817 584684503374510686000863)
                      ·
                        rfl

theorem cell23_1138669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1138669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138669 prefixEnd_1138669 := by exact prefixLift 1138669
  have htrace : WordTrace (prefixWord ++ tailWord_1138669) baseStart_1138669 baseEnd_1138669 := by
    simpa [prefixWord, tailWord_1138669, baseEnd_1138669] using wordTrace_append hprefix tailTrace_1138669
  have hstable : (prefixWord ++ tailWord_1138669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138669).length < 2 ^ (prefixWord ++ tailWord_1138669).sum := by decide
  have hdescent : baseEnd_1138669 < baseStart_1138669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138685 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1138685 : Nat := 118140960795 + 1138685 * 2 ^ 59
def prefixEnd_1138685 : Nat := 4983230072969 + 3 ^ 40 * 1138685 * 2
def baseEnd_1138685 : Nat := 584692719064982623400789

theorem tailTrace_1138685 : CollatzResearch.WordTrace tailWord_1138685 prefixEnd_1138685 584692719064982623400789 := by
  unfold tailWord_1138685
  simp only [CollatzResearch.WordTrace]
  refine ⟨41531253879746191760409509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27687502586497461173606339 41531253879746191760409509)
  ·
    refine ⟨7787110102452410955076783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41531253879746191760409509 7787110102452410955076783)
    ·
      refine ⟨11680665153678616432615175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7787110102452410955076783 11680665153678616432615175)
      ·
        refine ⟨17520997730517924648922763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11680665153678616432615175 17520997730517924648922763)
        ·
          refine ⟨26281496595776886973384145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17520997730517924648922763 26281496595776886973384145)
          ·
            refine ⟨19711122446832665230038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26281496595776886973384145 19711122446832665230038109)
            ·
              refine ⟨7391670917562249461264291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19711122446832665230038109 7391670917562249461264291)
              ·
                refine ⟨11087506376343374191896437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7391670917562249461264291 11087506376343374191896437)
                ·
                  refine ⟨1039453722782191330490291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11087506376343374191896437 1039453722782191330490291)
                  ·
                    refine ⟨1559180584173286995735437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039453722782191330490291 1559180584173286995735437)
                    ·
                      refine ⟨584692719064982623400789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1559180584173286995735437 584692719064982623400789)
                      ·
                        rfl

theorem cell23_1138685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1138685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138685 prefixEnd_1138685 := by exact prefixLift 1138685
  have htrace : WordTrace (prefixWord ++ tailWord_1138685) baseStart_1138685 baseEnd_1138685 := by
    simpa [prefixWord, tailWord_1138685, baseEnd_1138685] using wordTrace_append hprefix tailTrace_1138685
  have hstable : (prefixWord ++ tailWord_1138685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138685).length < 2 ^ (prefixWord ++ tailWord_1138685).sum := by decide
  have hdescent : baseEnd_1138685 < baseStart_1138685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138742 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1138742 : Nat := 118140960795 + 1138742 * 2 ^ 59
def prefixEnd_1138742 : Nat := 4983230072969 + 3 ^ 40 * 1138742 * 2
def baseEnd_1138742 : Nat := 584721987462288900388027

theorem tailTrace_1138742 : CollatzResearch.WordTrace tailWord_1138742 prefixEnd_1138742 584721987462288900388027 := by
  unfold tailWord_1138742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595833302533730655952155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27688888560359793663489653 2595833302533730655952155)
  ·
    refine ⟨3893749953800595983928233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2595833302533730655952155 3893749953800595983928233)
    ·
      refine ⟨2920312465350446987946175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3893749953800595983928233 2920312465350446987946175)
      ·
        refine ⟨4380468698025670481919263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920312465350446987946175 4380468698025670481919263)
        ·
          refine ⟨6570703047038505722878895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380468698025670481919263 6570703047038505722878895)
          ·
            refine ⟨9856054570557758584318343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570703047038505722878895 9856054570557758584318343)
            ·
              refine ⟨14784081855836637876477515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9856054570557758584318343 14784081855836637876477515)
              ·
                refine ⟨22176122783754956814716273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14784081855836637876477515 22176122783754956814716273)
                ·
                  refine ⟨16632092087816217611037205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22176122783754956814716273 16632092087816217611037205)
                  ·
                    refine ⟨779629316616385200517369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16632092087816217611037205 779629316616385200517369)
                    ·
                      refine ⟨584721987462288900388027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779629316616385200517369 584721987462288900388027)
                      ·
                        rfl

theorem cell23_1138742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1138742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138742 prefixEnd_1138742 := by exact prefixLift 1138742
  have htrace : WordTrace (prefixWord ++ tailWord_1138742) baseStart_1138742 baseEnd_1138742 := by
    simpa [prefixWord, tailWord_1138742, baseEnd_1138742] using wordTrace_append hprefix tailTrace_1138742
  have hstable : (prefixWord ++ tailWord_1138742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138742).length < 2 ^ (prefixWord ++ tailWord_1138742).sum := by decide
  have hdescent : baseEnd_1138742 < baseStart_1138742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138748 : List Nat := [2, 2, 2, 2, 2, 1, 3, 9]
def baseStart_1138748 : Nat := 118140960795 + 1138748 * 2 ^ 59
def prefixEnd_1138748 : Nat := 4983230072969 + 3 ^ 40 * 1138748 * 2
def baseEnd_1138748 : Nat := 21656484012822810256037

theorem tailTrace_1138748 : CollatzResearch.WordTrace tailWord_1138748 prefixEnd_1138748 21656484012822810256037 := by
  unfold tailWord_1138748
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766775839258976759976449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27689034452345302346635265 20766775839258976759976449)
  ·
    refine ⟨15575081879444232569982337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20766775839258976759976449 15575081879444232569982337)
    ·
      refine ⟨11681311409583174427486753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15575081879444232569982337 11681311409583174427486753)
      ·
        refine ⟨8760983557187380820615065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11681311409583174427486753 8760983557187380820615065)
        ·
          refine ⟨6570737667890535615461299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8760983557187380820615065 6570737667890535615461299)
          ·
            refine ⟨9856106501835803423191949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6570737667890535615461299 9856106501835803423191949)
            ·
              refine ⟨3696039938188426283696981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9856106501835803423191949 3696039938188426283696981)
              ·
                refine ⟨21656484012822810256037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3696039938188426283696981 21656484012822810256037)
                ·
                  rfl

theorem cell23_1138748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 9].length) (baseStart_1138748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138748 prefixEnd_1138748 := by exact prefixLift 1138748
  have htrace : WordTrace (prefixWord ++ tailWord_1138748) baseStart_1138748 baseEnd_1138748 := by
    simpa [prefixWord, tailWord_1138748, baseEnd_1138748] using wordTrace_append hprefix tailTrace_1138748
  have hstable : (prefixWord ++ tailWord_1138748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138748).length < 2 ^ (prefixWord ++ tailWord_1138748).sum := by decide
  have hdescent : baseEnd_1138748 < baseStart_1138748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138778 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_1138778 : Nat := 118140960795 + 1138778 * 2 ^ 59
def prefixEnd_1138778 : Nat := 4983230072969 + 3 ^ 40 * 1138778 * 2
def baseEnd_1138778 : Nat := 194913490921950253179287

theorem tailTrace_1138778 : CollatzResearch.WordTrace tailWord_1138778 prefixEnd_1138778 194913490921950253179287 := by
  unfold tailWord_1138778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383661467102317160886247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27689763912272845762363325 10383661467102317160886247)
  ·
    refine ⟨15575492200653475741329371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10383661467102317160886247 15575492200653475741329371)
    ·
      refine ⟨23363238300980213611994057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15575492200653475741329371 23363238300980213611994057)
      ·
        refine ⟨17522428725735160208995543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23363238300980213611994057 17522428725735160208995543)
        ·
          refine ⟨26283643088602740313493315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17522428725735160208995543 26283643088602740313493315)
          ·
            refine ⟨39425464632904110470239973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26283643088602740313493315 39425464632904110470239973)
            ·
              refine ⟨7392274618669520713169995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39425464632904110470239973 7392274618669520713169995)
              ·
                refine ⟨11088411928004281069754993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7392274618669520713169995 11088411928004281069754993)
                ·
                  refine ⟨8316308946003210802316245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11088411928004281069754993 8316308946003210802316245)
                  ·
                    refine ⟨194913490921950253179287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8316308946003210802316245 194913490921950253179287)
                    ·
                      rfl

theorem cell23_1138778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_1138778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138778 prefixEnd_1138778 := by exact prefixLift 1138778
  have htrace : WordTrace (prefixWord ++ tailWord_1138778) baseStart_1138778 baseEnd_1138778 := by
    simpa [prefixWord, tailWord_1138778, baseEnd_1138778] using wordTrace_append hprefix tailTrace_1138778
  have hstable : (prefixWord ++ tailWord_1138778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138778).length < 2 ^ (prefixWord ++ tailWord_1138778).sum := by decide
  have hdescent : baseEnd_1138778 < baseStart_1138778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138785 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_1138785 : Nat := 118140960795 + 1138785 * 2 ^ 59
def prefixEnd_1138785 : Nat := 4983230072969 + 3 ^ 40 * 1138785 * 2
def baseEnd_1138785 : Nat := 584744067130432232150329

theorem tailTrace_1138785 : CollatzResearch.WordTrace tailWord_1138785 prefixEnd_1138785 584744067130432232150329 := by
  unfold tailWord_1138785
  simp only [CollatzResearch.WordTrace]
  refine ⟨41534901179383908839049809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27689934119589272559366539 41534901179383908839049809)
  ·
    refine ⟨31151175884537931629287357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41534901179383908839049809 31151175884537931629287357)
    ·
      refine ⟨11681690956701724360982759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31151175884537931629287357 11681690956701724360982759)
      ·
        refine ⟨17522536435052586541474139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681690956701724360982759 17522536435052586541474139)
        ·
          refine ⟨26283804652578879812211209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17522536435052586541474139 26283804652578879812211209)
          ·
            refine ⟨19712853489434159859158407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26283804652578879812211209 19712853489434159859158407)
            ·
              refine ⟨29569280234151239788737611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19712853489434159859158407 29569280234151239788737611)
              ·
                refine ⟨44353920351226859683106417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29569280234151239788737611 44353920351226859683106417)
                ·
                  refine ⟨33265440263420144762329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44353920351226859683106417 33265440263420144762329813)
                  ·
                    refine ⟨779658756173909642867105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33265440263420144762329813 779658756173909642867105)
                    ·
                      refine ⟨584744067130432232150329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779658756173909642867105 584744067130432232150329)
                      ·
                        rfl

theorem cell23_1138785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_1138785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138785 prefixEnd_1138785 := by exact prefixLift 1138785
  have htrace : WordTrace (prefixWord ++ tailWord_1138785) baseStart_1138785 baseEnd_1138785 := by
    simpa [prefixWord, tailWord_1138785, baseEnd_1138785] using wordTrace_append hprefix tailTrace_1138785
  have hstable : (prefixWord ++ tailWord_1138785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138785).length < 2 ^ (prefixWord ++ tailWord_1138785).sum := by decide
  have hdescent : baseEnd_1138785 < baseStart_1138785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138808 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1138808 : Nat := 118140960795 + 1138808 * 2 ^ 59
def prefixEnd_1138808 : Nat := 4983230072969 + 3 ^ 40 * 1138808 * 2
def baseEnd_1138808 : Nat := 194918625728495214054241

theorem tailTrace_1138808 : CollatzResearch.WordTrace tailWord_1138808 prefixEnd_1138808 194918625728495214054241 := by
  unfold tailWord_1138808
  simp only [CollatzResearch.WordTrace]
  refine ⟨20767870029150291883568539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27690493372200389178091385 20767870029150291883568539)
  ·
    refine ⟨31151805043725437825352809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20767870029150291883568539 31151805043725437825352809)
    ·
      refine ⟨23363853782794078369014607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31151805043725437825352809 23363853782794078369014607)
      ·
        refine ⟨35045780674191117553521911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23363853782794078369014607 35045780674191117553521911)
        ·
          refine ⟨52568671011286676330282867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35045780674191117553521911 52568671011286676330282867)
          ·
            refine ⟨78853006516930014495424301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52568671011286676330282867 78853006516930014495424301)
            ·
              refine ⟨29569877443848755435784113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78853006516930014495424301 29569877443848755435784113)
              ·
                refine ⟨22177408082886566576838085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29569877443848755435784113 22177408082886566576838085)
                ·
                  refine ⟨4158264015541231233157141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22177408082886566576838085 4158264015541231233157141)
                  ·
                    refine ⟨194918625728495214054241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4158264015541231233157141 194918625728495214054241)
                    ·
                      rfl

theorem cell23_1138808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1138808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138808 prefixEnd_1138808 := by exact prefixLift 1138808
  have htrace : WordTrace (prefixWord ++ tailWord_1138808) baseStart_1138808 baseEnd_1138808 := by
    simpa [prefixWord, tailWord_1138808, baseEnd_1138808] using wordTrace_append hprefix tailTrace_1138808
  have hstable : (prefixWord ++ tailWord_1138808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138808).length < 2 ^ (prefixWord ++ tailWord_1138808).sum := by decide
  have hdescent : baseEnd_1138808 < baseStart_1138808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138828 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1138828 : Nat := 118140960795 + 1138828 * 2 ^ 59
def prefixEnd_1138828 : Nat := 4983230072969 + 3 ^ 40 * 1138828 * 2
def baseEnd_1138828 : Nat := 584766146798575563912631

theorem tailTrace_1138828 : CollatzResearch.WordTrace tailWord_1138828 prefixEnd_1138828 584766146798575563912631 := by
  unfold tailWord_1138828
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768234759114063591432569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27690979678818751455243425 20768234759114063591432569)
  ·
    refine ⟨15576176069335547693574427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20768234759114063591432569 15576176069335547693574427)
    ·
      refine ⟨23364264104003321540361641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15576176069335547693574427 23364264104003321540361641)
      ·
        refine ⟨17523198078002491155271231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23364264104003321540361641 17523198078002491155271231)
        ·
          refine ⟨26284797117003736732906847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17523198078002491155271231 26284797117003736732906847)
          ·
            refine ⟨39427195675505605099360271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26284797117003736732906847 39427195675505605099360271)
            ·
              refine ⟨59140793513258407649040407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39427195675505605099360271 59140793513258407649040407)
              ·
                refine ⟨88711190269887611473560611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59140793513258407649040407 88711190269887611473560611)
                ·
                  refine ⟨133066785404831417210340917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88711190269887611473560611 133066785404831417210340917)
                  ·
                    refine ⟨12475011131702945363469461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133066785404831417210340917 12475011131702945363469461)
                    ·
                      refine ⟨584766146798575563912631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12475011131702945363469461 584766146798575563912631)
                      ·
                        rfl

theorem cell23_1138828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1138828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138828 prefixEnd_1138828 := by exact prefixLift 1138828
  have htrace : WordTrace (prefixWord ++ tailWord_1138828) baseStart_1138828 baseEnd_1138828 := by
    simpa [prefixWord, tailWord_1138828, baseEnd_1138828] using wordTrace_append hprefix tailTrace_1138828
  have hstable : (prefixWord ++ tailWord_1138828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138828).length < 2 ^ (prefixWord ++ tailWord_1138828).sum := by decide
  have hdescent : baseEnd_1138828 < baseStart_1138828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138842 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_1138842 : Nat := 118140960795 + 1138842 * 2 ^ 59
def prefixEnd_1138842 : Nat := 4983230072969 + 3 ^ 40 * 1138842 * 2
def baseEnd_1138842 : Nat := 194924445175912836379189

theorem tailTrace_1138842 : CollatzResearch.WordTrace tailWord_1138842 prefixEnd_1138842 194924445175912836379189 := by
  unfold tailWord_1138842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384245035044351893468695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27691320093451605049249853 10384245035044351893468695)
  ·
    refine ⟨15576367552566527840203043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10384245035044351893468695 15576367552566527840203043)
    ·
      refine ⟨23364551328849791760304565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15576367552566527840203043 23364551328849791760304565)
      ·
        refine ⟨2190426687079667977528553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23364551328849791760304565 2190426687079667977528553)
        ·
          refine ⟨1642820015309750983146415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190426687079667977528553 1642820015309750983146415)
          ·
            refine ⟨2464230022964626474719623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642820015309750983146415 2464230022964626474719623)
            ·
              refine ⟨3696345034446939712079435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464230022964626474719623 3696345034446939712079435)
              ·
                refine ⟨5544517551670409568119153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696345034446939712079435 5544517551670409568119153)
                ·
                  refine ⟨4158388163752807176089365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5544517551670409568119153 4158388163752807176089365)
                  ·
                    refine ⟨194924445175912836379189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4158388163752807176089365 194924445175912836379189)
                    ·
                      rfl

theorem cell23_1138842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_1138842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138842 prefixEnd_1138842 := by exact prefixLift 1138842
  have htrace : WordTrace (prefixWord ++ tailWord_1138842) baseStart_1138842 baseEnd_1138842 := by
    simpa [prefixWord, tailWord_1138842, baseEnd_1138842] using wordTrace_append hprefix tailTrace_1138842
  have hstable : (prefixWord ++ tailWord_1138842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138842).length < 2 ^ (prefixWord ++ tailWord_1138842).sum := by decide
  have hdescent : baseEnd_1138842 < baseStart_1138842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138845 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1138845 : Nat := 118140960795 + 1138845 * 2 ^ 59
def prefixEnd_1138845 : Nat := 4983230072969 + 3 ^ 40 * 1138845 * 2
def baseEnd_1138845 : Nat := 584774875969701997400053

theorem tailTrace_1138845 : CollatzResearch.WordTrace tailWord_1138845 prefixEnd_1138845 584774875969701997400053 := by
  unfold tailWord_1138845
  simp only [CollatzResearch.WordTrace]
  refine ⟨41537089559166539086233989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27691393039444359390822659 41537089559166539086233989)
  ·
    refine ⟨7788204292343726078668873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41537089559166539086233989 7788204292343726078668873)
    ·
      refine ⟨5841153219257794559001655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7788204292343726078668873 5841153219257794559001655)
      ·
        refine ⟨8761729828886691838502483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841153219257794559001655 8761729828886691838502483)
        ·
          refine ⟨13142594743330037757753725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8761729828886691838502483 13142594743330037757753725)
          ·
            refine ⟨4928473028748764159157647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13142594743330037757753725 4928473028748764159157647)
            ·
              refine ⟨7392709543123146238736471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4928473028748764159157647 7392709543123146238736471)
              ·
                refine ⟨11089064314684719358104707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7392709543123146238736471 11089064314684719358104707)
                ·
                  refine ⟨16633596472027079037157061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11089064314684719358104707 16633596472027079037157061)
                  ·
                    refine ⟨3118799338505077319466949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16633596472027079037157061 3118799338505077319466949)
                    ·
                      refine ⟨584774875969701997400053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3118799338505077319466949 584774875969701997400053)
                      ·
                        rfl

theorem cell23_1138845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1138845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138845 prefixEnd_1138845 := by exact prefixLift 1138845
  have htrace : WordTrace (prefixWord ++ tailWord_1138845) baseStart_1138845 baseEnd_1138845 := by
    simpa [prefixWord, tailWord_1138845, baseEnd_1138845] using wordTrace_append hprefix tailTrace_1138845
  have hstable : (prefixWord ++ tailWord_1138845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138845).length < 2 ^ (prefixWord ++ tailWord_1138845).sum := by decide
  have hdescent : baseEnd_1138845 < baseStart_1138845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138849 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1138849 : Nat := 118140960795 + 1138849 * 2 ^ 59
def prefixEnd_1138849 : Nat := 4983230072969 + 3 ^ 40 * 1138849 * 2
def baseEnd_1138849 : Nat := 584776929892319981750035

theorem tailTrace_1138849 : CollatzResearch.WordTrace tailWord_1138849 prefixEnd_1138849 584776929892319981750035 := by
  unfold tailWord_1138849
  simp only [CollatzResearch.WordTrace]
  refine ⟨41537235451152047769379601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27691490300768031846253067 41537235451152047769379601)
  ·
    refine ⟨31152926588364035827034701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41537235451152047769379601 31152926588364035827034701)
    ·
      refine ⟨11682347470636513435138013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31152926588364035827034701 11682347470636513435138013)
      ·
        refine ⟨4380880301488692538176755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11682347470636513435138013 4380880301488692538176755)
        ·
          refine ⟨6571320452233038807265133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380880301488692538176755 6571320452233038807265133)
          ·
            refine ⟨2464245169587389552724425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6571320452233038807265133 2464245169587389552724425)
            ·
              refine ⟨1848183877190542164543319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464245169587389552724425 1848183877190542164543319)
              ·
                refine ⟨2772275815785813246814979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848183877190542164543319 2772275815785813246814979)
                ·
                  refine ⟨4158413723678719870222469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772275815785813246814979 4158413723678719870222469)
                  ·
                    refine ⟨779702573189759975666713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4158413723678719870222469 779702573189759975666713)
                    ·
                      refine ⟨584776929892319981750035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779702573189759975666713 584776929892319981750035)
                      ·
                        rfl

theorem cell23_1138849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1138849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138849 prefixEnd_1138849 := by exact prefixLift 1138849
  have htrace : WordTrace (prefixWord ++ tailWord_1138849) baseStart_1138849 baseEnd_1138849 := by
    simpa [prefixWord, tailWord_1138849, baseEnd_1138849] using wordTrace_append hprefix tailTrace_1138849
  have hstable : (prefixWord ++ tailWord_1138849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138849).length < 2 ^ (prefixWord ++ tailWord_1138849).sum := by decide
  have hdescent : baseEnd_1138849 < baseStart_1138849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138872 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 5]
def baseStart_1138872 : Nat := 118140960795 + 1138872 * 2 ^ 59
def prefixEnd_1138872 : Nat := 4983230072969 + 3 ^ 40 * 1138872 * 2
def baseEnd_1138872 : Nat := 64976526660819265751381

theorem tailTrace_1138872 : CollatzResearch.WordTrace tailWord_1138872 prefixEnd_1138872 64976526660819265751381 := by
  unfold tailWord_1138872
  simp only [CollatzResearch.WordTrace]
  refine ⟨20769037165034361348733435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27692049553379148464977913 20769037165034361348733435)
  ·
    refine ⟨31153555747551542023100153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20769037165034361348733435 31153555747551542023100153)
    ·
      refine ⟨23365166810663656517325115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31153555747551542023100153 23365166810663656517325115)
      ·
        refine ⟨35047750215995484775987673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23365166810663656517325115 35047750215995484775987673)
        ·
          refine ⟨26285812661996613581990755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35047750215995484775987673 26285812661996613581990755)
          ·
            refine ⟨39428718992994920372986133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26285812661996613581990755 39428718992994920372986133)
            ·
              refine ⟨1848221202796636892483725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39428718992994920372986133 1848221202796636892483725)
              ·
                refine ⟨693082951048738834681397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848221202796636892483725 693082951048738834681397)
                ·
                  refine ⟨64976526660819265751381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 693082951048738834681397 64976526660819265751381)
                  ·
                    rfl

theorem cell23_1138872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 5].length) (baseStart_1138872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138872 prefixEnd_1138872 := by exact prefixLift 1138872
  have htrace : WordTrace (prefixWord ++ tailWord_1138872) baseStart_1138872 baseEnd_1138872 := by
    simpa [prefixWord, tailWord_1138872, baseEnd_1138872] using wordTrace_append hprefix tailTrace_1138872
  have hstable : (prefixWord ++ tailWord_1138872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138872).length < 2 ^ (prefixWord ++ tailWord_1138872).sum := by decide
  have hdescent : baseEnd_1138872 < baseStart_1138872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138885 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1138885 : Nat := 118140960795 + 1138885 * 2 ^ 59
def prefixEnd_1138885 : Nat := 4983230072969 + 3 ^ 40 * 1138885 * 2
def baseEnd_1138885 : Nat := 194931805065293946966623

theorem tailTrace_1138885 : CollatzResearch.WordTrace tailWord_1138885 prefixEnd_1138885 194931805065293946966623 := by
  unfold tailWord_1138885
  simp only [CollatzResearch.WordTrace]
  refine ⟨41538548479021625917690109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27692365652681083945126739 41538548479021625917690109)
  ·
    refine ⟨15576955679633109719133791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41538548479021625917690109 15576955679633109719133791)
    ·
      refine ⟨23365433519449664578700687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15576955679633109719133791 23365433519449664578700687)
      ·
        refine ⟨35048150279174496868051031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23365433519449664578700687 35048150279174496868051031)
        ·
          refine ⟨52572225418761745302076547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35048150279174496868051031 52572225418761745302076547)
          ·
            refine ⟨78858338128142617953114821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52572225418761745302076547 78858338128142617953114821)
            ·
              refine ⟨14785938399026740866209029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78858338128142617953114821 14785938399026740866209029)
              ·
                refine ⟨2772363449817513912414193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14785938399026740866209029 2772363449817513912414193)
                ·
                  refine ⟨2079272587363135434310645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772363449817513912414193 2079272587363135434310645)
                  ·
                    refine ⟨194931805065293946966623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2079272587363135434310645 194931805065293946966623)
                    ·
                      rfl

theorem cell23_1138885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1138885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138885 prefixEnd_1138885 := by exact prefixLift 1138885
  have htrace : WordTrace (prefixWord ++ tailWord_1138885) baseStart_1138885 baseEnd_1138885 := by
    simpa [prefixWord, tailWord_1138885, baseEnd_1138885] using wordTrace_append hprefix tailTrace_1138885
  have hstable : (prefixWord ++ tailWord_1138885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138885).length < 2 ^ (prefixWord ++ tailWord_1138885).sum := by decide
  have hdescent : baseEnd_1138885 < baseStart_1138885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138905 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_1138905 : Nat := 118140960795 + 1138905 * 2 ^ 59
def prefixEnd_1138905 : Nat := 4983230072969 + 3 ^ 40 * 1138905 * 2
def baseEnd_1138905 : Nat := 584805684808971762649777

theorem tailTrace_1138905 : CollatzResearch.WordTrace tailWord_1138905 prefixEnd_1138905 584805684808971762649777 := by
  unfold tailWord_1138905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41539277938949169333418169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27692851959299446222278779 41539277938949169333418169)
  ·
    refine ⟨31154458454211877000063627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41539277938949169333418169 31154458454211877000063627)
    ·
      refine ⟨46731687681317815500095441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31154458454211877000063627 46731687681317815500095441)
      ·
        refine ⟨35048765760988361625071581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46731687681317815500095441 35048765760988361625071581)
        ·
          refine ⟨13143287160370635609401843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35048765760988361625071581 13143287160370635609401843)
          ·
            refine ⟨19714930740555953414102765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143287160370635609401843 19714930740555953414102765)
            ·
              refine ⟨7393099027708482530288537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19714930740555953414102765 7393099027708482530288537)
              ·
                refine ⟨5544824270781361897716403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7393099027708482530288537 5544824270781361897716403)
                ·
                  refine ⟨8317236406172042846574605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5544824270781361897716403 8317236406172042846574605)
                  ·
                    refine ⟨3118963652314516067465477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8317236406172042846574605 3118963652314516067465477)
                    ·
                      refine ⟨584805684808971762649777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3118963652314516067465477 584805684808971762649777)
                      ·
                        rfl

theorem cell23_1138905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_1138905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138905 prefixEnd_1138905 := by exact prefixLift 1138905
  have htrace : WordTrace (prefixWord ++ tailWord_1138905) baseStart_1138905 baseEnd_1138905 := by
    simpa [prefixWord, tailWord_1138905, baseEnd_1138905] using wordTrace_append hprefix tailTrace_1138905
  have hstable : (prefixWord ++ tailWord_1138905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138905).length < 2 ^ (prefixWord ++ tailWord_1138905).sum := by decide
  have hdescent : baseEnd_1138905 < baseStart_1138905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138922 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1138922 : Nat := 118140960795 + 1138922 * 2 ^ 59
def prefixEnd_1138922 : Nat := 4983230072969 + 3 ^ 40 * 1138922 * 2
def baseEnd_1138922 : Nat := 584814413980098196137199

theorem tailTrace_1138922 : CollatzResearch.WordTrace tailWord_1138922 prefixEnd_1138922 584814413980098196137199 := by
  unfold tailWord_1138922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384974494971895309196755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27693265319925054157858013 10384974494971895309196755)
  ·
    refine ⟨15577461742457842963795133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10384974494971895309196755 15577461742457842963795133)
    ·
      refine ⟨5841548153421691111423175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15577461742457842963795133 5841548153421691111423175)
      ·
        refine ⟨8762322230132536667134763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841548153421691111423175 8762322230132536667134763)
        ·
          refine ⟨13143483345198805000702145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762322230132536667134763 13143483345198805000702145)
          ·
            refine ⟨9857612508899103750526609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13143483345198805000702145 9857612508899103750526609)
            ·
              refine ⟨7393209381674327812894957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9857612508899103750526609 7393209381674327812894957)
              ·
                refine ⟨2772453518127872929835609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7393209381674327812894957 2772453518127872929835609)
                ·
                  refine ⟨2079340138595904697376707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2772453518127872929835609 2079340138595904697376707)
                  ·
                    refine ⟨3119010207893857046065061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2079340138595904697376707 3119010207893857046065061)
                    ·
                      refine ⟨584814413980098196137199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3119010207893857046065061 584814413980098196137199)
                      ·
                        rfl

theorem cell23_1138922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1138922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138922 prefixEnd_1138922 := by exact prefixLift 1138922
  have htrace : WordTrace (prefixWord ++ tailWord_1138922) baseStart_1138922 baseEnd_1138922 := by
    simpa [prefixWord, tailWord_1138922, baseEnd_1138922] using wordTrace_append hprefix tailTrace_1138922
  have hstable : (prefixWord ++ tailWord_1138922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138922).length < 2 ^ (prefixWord ++ tailWord_1138922).sum := by decide
  have hdescent : baseEnd_1138922 < baseStart_1138922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138945 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 8]
def baseStart_1138945 : Nat := 118140960795 + 1138945 * 2 ^ 59
def prefixEnd_1138945 : Nat := 4983230072969 + 3 ^ 40 * 1138945 * 2
def baseEnd_1138945 : Nat := 64980691559461289572177

theorem tailTrace_1138945 : CollatzResearch.WordTrace tailWord_1138945 prefixEnd_1138945 64980691559461289572177 := by
  unfold tailWord_1138945
  simp only [CollatzResearch.WordTrace]
  refine ⟨41540736858804256164874289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27693824572536170776582859 41540736858804256164874289)
  ·
    refine ⟨31155552644103192123655717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41540736858804256164874289 31155552644103192123655717)
    ·
      refine ⟨5841666120769348523185447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31155552644103192123655717 5841666120769348523185447)
      ·
        refine ⟨8762499181154022784778171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5841666120769348523185447 8762499181154022784778171)
        ·
          refine ⟨13143748771731034177167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8762499181154022784778171 13143748771731034177167257)
          ·
            refine ⟨9857811578798275632875443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13143748771731034177167257 9857811578798275632875443)
            ·
              refine ⟨14786717368197413449313165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9857811578798275632875443 14786717368197413449313165)
              ·
                refine ⟨5545019013074030043492437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14786717368197413449313165 5545019013074030043492437)
                ·
                  refine ⟨64980691559461289572177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5545019013074030043492437 64980691559461289572177)
                  ·
                    rfl

theorem cell23_1138945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_1138945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138945 prefixEnd_1138945 := by exact prefixLift 1138945
  have htrace : WordTrace (prefixWord ++ tailWord_1138945) baseStart_1138945 baseEnd_1138945 := by
    simpa [prefixWord, tailWord_1138945, baseEnd_1138945] using wordTrace_append hprefix tailTrace_1138945
  have hstable : (prefixWord ++ tailWord_1138945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138945).length < 2 ^ (prefixWord ++ tailWord_1138945).sum := by decide
  have hdescent : baseEnd_1138945 < baseStart_1138945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138965 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1138965 : Nat := 118140960795 + 1138965 * 2 ^ 59
def prefixEnd_1138965 : Nat := 4983230072969 + 3 ^ 40 * 1138965 * 2
def baseEnd_1138965 : Nat := 584836493648241527899501

theorem tailTrace_1138965 : CollatzResearch.WordTrace tailWord_1138965 prefixEnd_1138965 584836493648241527899501 := by
  unfold tailWord_1138965
  simp only [CollatzResearch.WordTrace]
  refine ⟨41541466318731799580602349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27694310879154533053734899 41541466318731799580602349)
  ·
    refine ⟨15578049869524424842725881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41541466318731799580602349 15578049869524424842725881)
    ·
      refine ⟨11683537402143318632044411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15578049869524424842725881 11683537402143318632044411)
      ·
        refine ⟨17525306103214977948066617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683537402143318632044411 17525306103214977948066617)
        ·
          refine ⟨13143979577411233461049963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17525306103214977948066617 13143979577411233461049963)
          ·
            refine ⟨19715969366116850191574945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13143979577411233461049963 19715969366116850191574945)
            ·
              refine ⟨14786977024587637643681209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19715969366116850191574945 14786977024587637643681209)
              ·
                refine ⟨11090232768440728232760907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14786977024587637643681209 11090232768440728232760907)
                ·
                  refine ⟨16635349152661092349141361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11090232768440728232760907 16635349152661092349141361)
                  ·
                    refine ⟨12476511864495819261856021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16635349152661092349141361 12476511864495819261856021)
                    ·
                      refine ⟨584836493648241527899501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12476511864495819261856021 584836493648241527899501)
                      ·
                        rfl

theorem cell23_1138965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1138965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1138965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1138965 prefixEnd_1138965 := by exact prefixLift 1138965
  have htrace : WordTrace (prefixWord ++ tailWord_1138965) baseStart_1138965 baseEnd_1138965 := by
    simpa [prefixWord, tailWord_1138965, baseEnd_1138965] using wordTrace_append hprefix tailTrace_1138965
  have hstable : (prefixWord ++ tailWord_1138965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138965).length < 2 ^ (prefixWord ++ tailWord_1138965).sum := by decide
  have hdescent : baseEnd_1138965 < baseStart_1138965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139049 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_1139049 : Nat := 118140960795 + 1139049 * 2 ^ 59
def prefixEnd_1139049 : Nat := 4983230072969 + 3 ^ 40 * 1139049 * 2
def baseEnd_1139049 : Nat := 584879626023219199249115

theorem tailTrace_1139049 : CollatzResearch.WordTrace tailWord_1139049 prefixEnd_1139049 584879626023219199249115 := by
  unfold tailWord_1139049
  simp only [CollatzResearch.WordTrace]
  refine ⟨41544530050427481926660201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27696353366951654617773467 41544530050427481926660201)
  ·
    refine ⟨31158397537820611444995151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41544530050427481926660201 31158397537820611444995151)
    ·
      refine ⟨46737596306730917167492727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31158397537820611444995151 46737596306730917167492727)
      ·
        refine ⟨70106394460096375751239091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46737596306730917167492727 70106394460096375751239091)
        ·
          refine ⟨105159591690144563626858637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70106394460096375751239091 105159591690144563626858637)
          ·
            refine ⟨39434846883804211360071989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105159591690144563626858637 39434846883804211360071989)
            ·
              refine ⟨3697016895356644815006749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39434846883804211360071989 3697016895356644815006749)
              ·
                refine ⟨1386381335758741805627531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3697016895356644815006749 1386381335758741805627531)
                ·
                  refine ⟨2079572003638112708441297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386381335758741805627531 2079572003638112708441297)
                  ·
                    refine ⟨1559679002728584531330973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2079572003638112708441297 1559679002728584531330973)
                    ·
                      refine ⟨584879626023219199249115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1559679002728584531330973 584879626023219199249115)
                      ·
                        rfl

theorem cell23_1139049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_1139049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139049 prefixEnd_1139049 := by exact prefixLift 1139049
  have htrace : WordTrace (prefixWord ++ tailWord_1139049) baseStart_1139049 baseEnd_1139049 := by
    simpa [prefixWord, tailWord_1139049, baseEnd_1139049] using wordTrace_append hprefix tailTrace_1139049
  have hstable : (prefixWord ++ tailWord_1139049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139049).length < 2 ^ (prefixWord ++ tailWord_1139049).sum := by decide
  have hdescent : baseEnd_1139049 < baseStart_1139049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139052 : List Nat := [2, 2, 1, 1, 6, 1, 10]
def baseStart_1139052 : Nat := 118140960795 + 1139052 * 2 ^ 59
def prefixEnd_1139052 : Nat := 4983230072969 + 3 ^ 40 * 1139052 * 2
def baseEnd_1139052 : Nat := 7220755141545465277921

theorem tailTrace_1139052 : CollatzResearch.WordTrace tailWord_1139052 prefixEnd_1139052 7220755141545465277921 := by
  unfold tailWord_1139052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772319734708306719509705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27696426312944408959346273 20772319734708306719509705)
  ·
    refine ⟨15579239801031230039632279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20772319734708306719509705 15579239801031230039632279)
    ·
      refine ⟨23368859701546845059448419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15579239801031230039632279 23368859701546845059448419)
      ·
        refine ⟨35053289552320267589172629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23368859701546845059448419 35053289552320267589172629)
        ·
          refine ⟨1643122947765012543242467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35053289552320267589172629 1643122947765012543242467)
          ·
            refine ⟨2464684421647518814863701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1643122947765012543242467 2464684421647518814863701)
            ·
              refine ⟨7220755141545465277921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2464684421647518814863701 7220755141545465277921)
              ·
                rfl

theorem cell23_1139052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 10].length) (baseStart_1139052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139052 prefixEnd_1139052 := by exact prefixLift 1139052
  have htrace : WordTrace (prefixWord ++ tailWord_1139052) baseStart_1139052 baseEnd_1139052 := by
    simpa [prefixWord, tailWord_1139052, baseEnd_1139052] using wordTrace_append hprefix tailTrace_1139052
  have hstable : (prefixWord ++ tailWord_1139052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139052).length < 2 ^ (prefixWord ++ tailWord_1139052).sum := by decide
  have hdescent : baseEnd_1139052 < baseStart_1139052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139056 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_1139056 : Nat := 118140960795 + 1139056 * 2 ^ 59
def prefixEnd_1139056 : Nat := 4983230072969 + 3 ^ 40 * 1139056 * 2
def baseEnd_1139056 : Nat := 194961073462600223953861

theorem tailTrace_1139056 : CollatzResearch.WordTrace tailWord_1139056 prefixEnd_1139056 194961073462600223953861 := by
  unfold tailWord_1139056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772392680701061061082511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27696523574268081414776681 20772392680701061061082511)
  ·
    refine ⟨31158589021051591591623767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20772392680701061061082511 31158589021051591591623767)
    ·
      refine ⟨46737883531577387387435651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31158589021051591591623767 46737883531577387387435651)
      ·
        refine ⟨70106825297366081081153477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46737883531577387387435651 70106825297366081081153477)
        ·
          refine ⟨13145029743256140202716277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70106825297366081081153477 13145029743256140202716277)
          ·
            refine ⟨1232346538430263144004651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13145029743256140202716277 1232346538430263144004651)
            ·
              refine ⟨1848519807645394716006977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232346538430263144004651 1848519807645394716006977)
              ·
                refine ⟨1386389855734046037005233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848519807645394716006977 1386389855734046037005233)
                ·
                  refine ⟨1039792391800534527753925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386389855734046037005233 1039792391800534527753925)
                  ·
                    refine ⟨194961073462600223953861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039792391800534527753925 194961073462600223953861)
                    ·
                      rfl

theorem cell23_1139056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_1139056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139056 prefixEnd_1139056 := by exact prefixLift 1139056
  have htrace : WordTrace (prefixWord ++ tailWord_1139056) baseStart_1139056 baseEnd_1139056 := by
    simpa [prefixWord, tailWord_1139056, baseEnd_1139056] using wordTrace_append hprefix tailTrace_1139056
  have hstable : (prefixWord ++ tailWord_1139056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139056).length < 2 ^ (prefixWord ++ tailWord_1139056).sum := by decide
  have hdescent : baseEnd_1139056 < baseStart_1139056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139073 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1139073 : Nat := 118140960795 + 1139073 * 2 ^ 59
def prefixEnd_1139073 : Nat := 4983230072969 + 3 ^ 40 * 1139073 * 2
def baseEnd_1139073 : Nat := 194963983186309035116335

theorem tailTrace_1139073 : CollatzResearch.WordTrace tailWord_1139073 prefixEnd_1139073 194963983186309035116335 := by
  unfold tailWord_1139073
  simp only [CollatzResearch.WordTrace]
  refine ⟨41545405402340534025533873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27696936934893689350355915 41545405402340534025533873)
  ·
    refine ⟨31159054051755400519150405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41545405402340534025533873 31159054051755400519150405)
    ·
      refine ⟨5842322634704137597340701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31159054051755400519150405 5842322634704137597340701)
      ·
        refine ⟨2190870988014051599002763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5842322634704137597340701 2190870988014051599002763)
        ·
          refine ⟨3286306482021077398504145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190870988014051599002763 3286306482021077398504145)
          ·
            refine ⟨2464729861515808048878109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286306482021077398504145 2464729861515808048878109)
            ·
              refine ⟨924273698068428018329291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2464729861515808048878109 924273698068428018329291)
              ·
                refine ⟨1386410547102642027493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924273698068428018329291 1386410547102642027493937)
                ·
                  refine ⟨1039807910326981520620453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386410547102642027493937 1039807910326981520620453)
                  ·
                    refine ⟨194963983186309035116335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039807910326981520620453 194963983186309035116335)
                    ·
                      rfl

theorem cell23_1139073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1139073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139073 prefixEnd_1139073 := by exact prefixLift 1139073
  have htrace : WordTrace (prefixWord ++ tailWord_1139073) baseStart_1139073 baseEnd_1139073 := by
    simpa [prefixWord, tailWord_1139073, baseEnd_1139073] using wordTrace_append hprefix tailTrace_1139073
  have hstable : (prefixWord ++ tailWord_1139073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139073).length < 2 ^ (prefixWord ++ tailWord_1139073).sum := by decide
  have hdescent : baseEnd_1139073 < baseStart_1139073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139086 : List Nat := [4, 1, 1, 4, 1, 3, 2, 7]
def baseStart_1139086 : Nat := 118140960795 + 1139086 * 2 ^ 59
def prefixEnd_1139086 : Nat := 4983230072969 + 3 ^ 40 * 1139086 * 2
def baseEnd_1139086 : Nat := 21662912029905020536535

theorem tailTrace_1139086 : CollatzResearch.WordTrace tailWord_1139086 prefixEnd_1139086 21662912029905020536535 := by
  unfold tailWord_1139086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193234943911679655719639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27697253034195624830504741 5193234943911679655719639)
  ·
    refine ⟨7789852415867519483579459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5193234943911679655719639 7789852415867519483579459)
    ·
      refine ⟨11684778623801279225369189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7789852415867519483579459 11684778623801279225369189)
      ·
        refine ⟨2190895991962739854756723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11684778623801279225369189 2190895991962739854756723)
        ·
          refine ⟨3286343987944109782135085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190895991962739854756723 3286343987944109782135085)
          ·
            refine ⟨1232378995479041168300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3286343987944109782135085 1232378995479041168300657)
            ·
              refine ⟨924284246609280876225493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232378995479041168300657 924284246609280876225493)
              ·
                refine ⟨21662912029905020536535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 924284246609280876225493 21662912029905020536535)
                ·
                  rfl

theorem cell23_1139086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_1139086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139086 prefixEnd_1139086 := by exact prefixLift 1139086
  have htrace : WordTrace (prefixWord ++ tailWord_1139086) baseStart_1139086 baseEnd_1139086 := by
    simpa [prefixWord, tailWord_1139086, baseEnd_1139086] using wordTrace_append hprefix tailTrace_1139086
  have hstable : (prefixWord ++ tailWord_1139086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139086).length < 2 ^ (prefixWord ++ tailWord_1139086).sum := by decide
  have hdescent : baseEnd_1139086 < baseStart_1139086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139096 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1139096 : Nat := 118140960795 + 1139096 * 2 ^ 59
def prefixEnd_1139096 : Nat := 4983230072969 + 3 ^ 40 * 1139096 * 2
def baseEnd_1139096 : Nat := 584903759613980515361399

theorem tailTrace_1139096 : CollatzResearch.WordTrace tailWord_1139096 prefixEnd_1139096 584903759613980515361399 := by
  unfold tailWord_1139096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773122140628604476810571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27697496187504805969080761 20773122140628604476810571)
  ·
    refine ⟨31159683210942906715215857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20773122140628604476810571 31159683210942906715215857)
    ·
      refine ⟨23369762408207180036411893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31159683210942906715215857 23369762408207180036411893)
      ·
        refine ⟨2190915225769423128413615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23369762408207180036411893 2190915225769423128413615)
        ·
          refine ⟨3286372838654134692620423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190915225769423128413615 3286372838654134692620423)
          ·
            refine ⟨4929559257981202038930635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286372838654134692620423 4929559257981202038930635)
            ·
              refine ⟨7394338886971803058395953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4929559257981202038930635 7394338886971803058395953)
              ·
                refine ⟨5545754165228852293796965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7394338886971803058395953 5545754165228852293796965)
                ·
                  refine ⟨1039828905980409805086931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5545754165228852293796965 1039828905980409805086931)
                  ·
                    refine ⟨1559743358970614707630397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039828905980409805086931 1559743358970614707630397)
                    ·
                      refine ⟨584903759613980515361399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1559743358970614707630397 584903759613980515361399)
                      ·
                        rfl

theorem cell23_1139096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1139096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139096 prefixEnd_1139096 := by exact prefixLift 1139096
  have htrace : WordTrace (prefixWord ++ tailWord_1139096) baseStart_1139096 baseEnd_1139096 := by
    simpa [prefixWord, tailWord_1139096, baseEnd_1139096] using wordTrace_append hprefix tailTrace_1139096
  have hstable : (prefixWord ++ tailWord_1139096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139096).length < 2 ^ (prefixWord ++ tailWord_1139096).sum := by decide
  have hdescent : baseEnd_1139096 < baseStart_1139096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139114 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1139114 : Nat := 118140960795 + 1139114 * 2 ^ 59
def prefixEnd_1139114 : Nat := 4983230072969 + 3 ^ 40 * 1139114 * 2
def baseEnd_1139114 : Nat := 584913002265761444936317

theorem tailTrace_1139114 : CollatzResearch.WordTrace tailWord_1139114 prefixEnd_1139114 584913002265761444936317 := by
  unfold tailWord_1139114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386725198797999506944099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27697933863461332018517597 10386725198797999506944099)
  ·
    refine ⟨15580087798196999260416149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10386725198797999506944099 15580087798196999260416149)
    ·
      refine ⟨730316615540484340332007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15580087798196999260416149 730316615540484340332007)
      ·
        refine ⟨1095474923310726510498011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730316615540484340332007 1095474923310726510498011)
        ·
          refine ⟨1643212384966089765747017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095474923310726510498011 1643212384966089765747017)
          ·
            refine ⟨1232409288724567324310263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643212384966089765747017 1232409288724567324310263)
            ·
              refine ⟨1848613933086850986465395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232409288724567324310263 1848613933086850986465395)
              ·
                refine ⟨2772920899630276479698093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848613933086850986465395 2772920899630276479698093)
                ·
                  refine ⟨1039845337361353679886785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2772920899630276479698093 1039845337361353679886785)
                  ·
                    refine ⟨779884003021015259915089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1039845337361353679886785 779884003021015259915089)
                    ·
                      refine ⟨584913002265761444936317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779884003021015259915089 584913002265761444936317)
                      ·
                        rfl

theorem cell23_1139114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1139114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139114 prefixEnd_1139114 := by exact prefixLift 1139114
  have htrace : WordTrace (prefixWord ++ tailWord_1139114) baseStart_1139114 baseEnd_1139114 := by
    simpa [prefixWord, tailWord_1139114, baseEnd_1139114] using wordTrace_append hprefix tailTrace_1139114
  have hstable : (prefixWord ++ tailWord_1139114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139114).length < 2 ^ (prefixWord ++ tailWord_1139114).sum := by decide
  have hdescent : baseEnd_1139114 < baseStart_1139114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139122 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1139122 : Nat := 118140960795 + 1139122 * 2 ^ 59
def prefixEnd_1139122 : Nat := 4983230072969 + 3 ^ 40 * 1139122 * 2
def baseEnd_1139122 : Nat := 584917110110997413636279

theorem tailTrace_1139122 : CollatzResearch.WordTrace tailWord_1139122 prefixEnd_1139122 584917110110997413636279 := by
  unfold tailWord_1139122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10386798144790753848516905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27698128386108676929378413 10386798144790753848516905)
  ·
    refine ⟨7790098608593065386387679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10386798144790753848516905 7790098608593065386387679)
    ·
      refine ⟨11685147912889598079581519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790098608593065386387679 11685147912889598079581519)
      ·
        refine ⟨17527721869334397119372279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685147912889598079581519 17527721869334397119372279)
        ·
          refine ⟨26291582804001595679058419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17527721869334397119372279 26291582804001595679058419)
          ·
            refine ⟨39437374206002393518587629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26291582804001595679058419 39437374206002393518587629)
            ·
              refine ⟨14789015327250897569470361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39437374206002393518587629 14789015327250897569470361)
              ·
                refine ⟨11091761495438173177102771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14789015327250897569470361 11091761495438173177102771)
                ·
                  refine ⟨16637642243157259765654157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11091761495438173177102771 16637642243157259765654157)
                  ·
                    refine ⟨6239115841183972412120309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16637642243157259765654157 6239115841183972412120309)
                    ·
                      refine ⟨584917110110997413636279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6239115841183972412120309 584917110110997413636279)
                      ·
                        rfl

theorem cell23_1139122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1139122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139122 prefixEnd_1139122 := by exact prefixLift 1139122
  have htrace : WordTrace (prefixWord ++ tailWord_1139122) baseStart_1139122 baseEnd_1139122 := by
    simpa [prefixWord, tailWord_1139122, baseEnd_1139122] using wordTrace_append hprefix tailTrace_1139122
  have hstable : (prefixWord ++ tailWord_1139122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139122).length < 2 ^ (prefixWord ++ tailWord_1139122).sum := by decide
  have hdescent : baseEnd_1139122 < baseStart_1139122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139124 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1139124 : Nat := 118140960795 + 1139124 * 2 ^ 59
def prefixEnd_1139124 : Nat := 4983230072969 + 3 ^ 40 * 1139124 * 2
def baseEnd_1139124 : Nat := 194972712357435468603757

theorem tailTrace_1139124 : CollatzResearch.WordTrace tailWord_1139124 prefixEnd_1139124 194972712357435468603757 := by
  unfold tailWord_1139124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20773632762577884867820213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27698177016770513157093617 20773632762577884867820213)
  ·
    refine ⟨1947528071491676706358145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20773632762577884867820213 1947528071491676706358145)
    ·
      refine ⟨1460646053618757529768609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1947528071491676706358145 1460646053618757529768609)
      ·
        refine ⟨1095484540214068147326457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460646053618757529768609 1095484540214068147326457)
        ·
          refine ⟨821613405160551110494843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095484540214068147326457 821613405160551110494843)
          ·
            refine ⟨1232420107740826665742265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821613405160551110494843 1232420107740826665742265)
            ·
              refine ⟨924315080805619999306699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232420107740826665742265 924315080805619999306699)
              ·
                refine ⟨1386472621208429998960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924315080805619999306699 1386472621208429998960049)
                ·
                  refine ⟨1039854465906322499220037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386472621208429998960049 1039854465906322499220037)
                  ·
                    refine ⟨194972712357435468603757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039854465906322499220037 194972712357435468603757)
                    ·
                      rfl

theorem cell23_1139124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1139124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139124 prefixEnd_1139124 := by exact prefixLift 1139124
  have htrace : WordTrace (prefixWord ++ tailWord_1139124) baseStart_1139124 baseEnd_1139124 := by
    simpa [prefixWord, tailWord_1139124, baseEnd_1139124] using wordTrace_append hprefix tailTrace_1139124
  have hstable : (prefixWord ++ tailWord_1139124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139124).length < 2 ^ (prefixWord ++ tailWord_1139124).sum := by decide
  have hdescent : baseEnd_1139124 < baseStart_1139124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139169 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1139169 : Nat := 118140960795 + 1139169 * 2 ^ 59
def prefixEnd_1139169 : Nat := 4983230072969 + 3 ^ 40 * 1139169 * 2
def baseEnd_1139169 : Nat := 584941243701758729748563

theorem tailTrace_1139169 : CollatzResearch.WordTrace tailWord_1139169 prefixEnd_1139169 584941243701758729748563 := by
  unfold tailWord_1139169
  simp only [CollatzResearch.WordTrace]
  refine ⟨41548906809992742421028561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27699271206661828280685707 41548906809992742421028561)
  ·
    refine ⟨31161680107494556815771421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41548906809992742421028561 31161680107494556815771421)
    ·
      refine ⟨11685630040310458805914283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31161680107494556815771421 11685630040310458805914283)
      ·
        refine ⟨17528445060465688208871425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685630040310458805914283 17528445060465688208871425)
        ·
          refine ⟨13146333795349266156653569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17528445060465688208871425 13146333795349266156653569)
          ·
            refine ⟨9859750346511949617490177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13146333795349266156653569 9859750346511949617490177)
            ·
              refine ⟨7394812759883962213117633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9859750346511949617490177 7394812759883962213117633)
              ·
                refine ⟨5546109569912971659838225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7394812759883962213117633 5546109569912971659838225)
                ·
                  refine ⟨4159582177434728744878669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546109569912971659838225 4159582177434728744878669)
                  ·
                    refine ⟨1559843316538023279329501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4159582177434728744878669 1559843316538023279329501)
                    ·
                      refine ⟨584941243701758729748563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1559843316538023279329501 584941243701758729748563)
                      ·
                        rfl

theorem cell23_1139169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1139169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139169 prefixEnd_1139169 := by exact prefixLift 1139169
  have htrace : WordTrace (prefixWord ++ tailWord_1139169) baseStart_1139169 baseEnd_1139169 := by
    simpa [prefixWord, tailWord_1139169, baseEnd_1139169] using wordTrace_append hprefix tailTrace_1139169
  have hstable : (prefixWord ++ tailWord_1139169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139169).length < 2 ^ (prefixWord ++ tailWord_1139169).sum := by decide
  have hdescent : baseEnd_1139169 < baseStart_1139169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139172 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_1139172 : Nat := 118140960795 + 1139172 * 2 ^ 59
def prefixEnd_1139172 : Nat := 4983230072969 + 3 ^ 40 * 1139172 * 2
def baseEnd_1139172 : Nat := 194980928047907406003683

theorem tailTrace_1139172 : CollatzResearch.WordTrace tailWord_1139172 prefixEnd_1139172 194980928047907406003683 := by
  unfold tailWord_1139172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774508114490936966693885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27699344152654582622258513 20774508114490936966693885)
  ·
    refine ⟨7790440542934101362510207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20774508114490936966693885 7790440542934101362510207)
    ·
      refine ⟨11685660814401152043765311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790440542934101362510207 11685660814401152043765311)
      ·
        refine ⟨17528491221601728065647967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11685660814401152043765311 17528491221601728065647967)
        ·
          refine ⟨26292736832402592098471951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17528491221601728065647967 26292736832402592098471951)
          ·
            refine ⟨39439105248603888147707927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26292736832402592098471951 39439105248603888147707927)
            ·
              refine ⟨59158657872905832221561891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39439105248603888147707927 59158657872905832221561891)
              ·
                refine ⟨88737986809358748332342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59158657872905832221561891 88737986809358748332342837)
                ·
                  refine ⟨8319186263377382656157141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88737986809358748332342837 8319186263377382656157141)
                  ·
                    refine ⟨194980928047907406003683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8319186263377382656157141 194980928047907406003683)
                    ·
                      rfl

theorem cell23_1139172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_1139172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139172 prefixEnd_1139172 := by exact prefixLift 1139172
  have htrace : WordTrace (prefixWord ++ tailWord_1139172) baseStart_1139172 baseEnd_1139172 := by
    simpa [prefixWord, tailWord_1139172, baseEnd_1139172] using wordTrace_append hprefix tailTrace_1139172
  have hstable : (prefixWord ++ tailWord_1139172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139172).length < 2 ^ (prefixWord ++ tailWord_1139172).sum := by decide
  have hdescent : baseEnd_1139172 < baseStart_1139172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139176 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 5]
def baseStart_1139176 : Nat := 118140960795 + 1139176 * 2 ^ 59
def prefixEnd_1139176 : Nat := 4983230072969 + 3 ^ 40 * 1139176 * 2
def baseEnd_1139176 : Nat := 64993870896260022484559

theorem tailTrace_1139176 : CollatzResearch.WordTrace tailWord_1139176 prefixEnd_1139176 64993870896260022484559 := by
  unfold tailWord_1139176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774581060483691308266691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27699441413978255077688921 20774581060483691308266691)
  ·
    refine ⟨31161871590725536962400037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20774581060483691308266691 31161871590725536962400037)
    ·
      refine ⟨5842850923261038180450007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31161871590725536962400037 5842850923261038180450007)
      ·
        refine ⟨8764276384891557270675011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5842850923261038180450007 8764276384891557270675011)
        ·
          refine ⟨13146414577337335906012517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8764276384891557270675011 13146414577337335906012517)
          ·
            refine ⟨2464952733250750482377347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13146414577337335906012517 2464952733250750482377347)
            ·
              refine ⟨3697429099876125723566021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464952733250750482377347 3697429099876125723566021)
              ·
                refine ⟨693267956226773573168629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3697429099876125723566021 693267956226773573168629)
                ·
                  refine ⟨64993870896260022484559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 693267956226773573168629 64993870896260022484559)
                  ·
                    rfl

theorem cell23_1139176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 5].length) (baseStart_1139176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139176 prefixEnd_1139176 := by exact prefixLift 1139176
  have htrace : WordTrace (prefixWord ++ tailWord_1139176) baseStart_1139176 baseEnd_1139176 := by
    simpa [prefixWord, tailWord_1139176, baseEnd_1139176] using wordTrace_append hprefix tailTrace_1139176
  have hstable : (prefixWord ++ tailWord_1139176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139176).length < 2 ^ (prefixWord ++ tailWord_1139176).sum := by decide
  have hdescent : baseEnd_1139176 < baseStart_1139176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139179 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 7, 2]
def baseStart_1139179 : Nat := 118140960795 + 1139179 * 2 ^ 59
def prefixEnd_1139179 : Nat := 4983230072969 + 3 ^ 40 * 1139179 * 2
def baseEnd_1139179 : Nat := 584946378508303690623517

theorem tailTrace_1139179 : CollatzResearch.WordTrace tailWord_1139179 prefixEnd_1139179 584946378508303690623517 := by
  unfold tailWord_1139179
  simp only [CollatzResearch.WordTrace]
  refine ⟨41549271539956514128892591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27699514359971009419261727 41549271539956514128892591)
  ·
    refine ⟨62323907309934771193338887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41549271539956514128892591 62323907309934771193338887)
    ·
      refine ⟨93485860964902156790008331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62323907309934771193338887 93485860964902156790008331)
      ·
        refine ⟨140228791447353235185012497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93485860964902156790008331 140228791447353235185012497)
        ·
          refine ⟨105171593585514926388759373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140228791447353235185012497 105171593585514926388759373)
          ·
            refine ⟨39439347594568097395784765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105171593585514926388759373 39439347594568097395784765)
            ·
              refine ⟨14789755347963036523419287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39439347594568097395784765 14789755347963036523419287)
              ·
                refine ⟨22184633021944554785128931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14789755347963036523419287 22184633021944554785128931)
                ·
                  refine ⟨33276949532916832177693397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22184633021944554785128931 33276949532916832177693397)
                  ·
                    refine ⟨779928504677738254164689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33276949532916832177693397 779928504677738254164689)
                    ·
                      refine ⟨584946378508303690623517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779928504677738254164689 584946378508303690623517)
                      ·
                        rfl

theorem cell23_1139179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7, 2].length) (baseStart_1139179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139179 prefixEnd_1139179 := by exact prefixLift 1139179
  have htrace : WordTrace (prefixWord ++ tailWord_1139179) baseStart_1139179 baseEnd_1139179 := by
    simpa [prefixWord, tailWord_1139179, baseEnd_1139179] using wordTrace_append hprefix tailTrace_1139179
  have hstable : (prefixWord ++ tailWord_1139179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139179).length < 2 ^ (prefixWord ++ tailWord_1139179).sum := by decide
  have hdescent : baseEnd_1139179 < baseStart_1139179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139209 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_1139209 : Nat := 118140960795 + 1139209 * 2 ^ 59
def prefixEnd_1139209 : Nat := 4983230072969 + 3 ^ 40 * 1139209 * 2
def baseEnd_1139209 : Nat := 584961782927938573248379

theorem tailTrace_1139209 : CollatzResearch.WordTrace tailWord_1139209 prefixEnd_1139209 584961782927938573248379 := by
  unfold tailWord_1139209
  simp only [CollatzResearch.WordTrace]
  refine ⟨41550365729847829252484681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27700243819898552834989787 41550365729847829252484681)
  ·
    refine ⟨31162774297385871939363511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41550365729847829252484681 31162774297385871939363511)
    ·
      refine ⟨46744161446078807909045267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31162774297385871939363511 46744161446078807909045267)
      ·
        refine ⟨70116242169118211863567901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46744161446078807909045267 70116242169118211863567901)
        ·
          refine ⟨26293590813419329448837963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70116242169118211863567901 26293590813419329448837963)
          ·
            refine ⟨39440386220128994173256945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26293590813419329448837963 39440386220128994173256945)
            ·
              refine ⟨29580289665096745629942709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39440386220128994173256945 29580289665096745629942709)
              ·
                refine ⟨2773152156102819902807129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29580289665096745629942709 2773152156102819902807129)
                ·
                  refine ⟨2079864117077114927105347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773152156102819902807129 2079864117077114927105347)
                  ·
                    refine ⟨3119796175615672390658021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2079864117077114927105347 3119796175615672390658021)
                    ·
                      refine ⟨584961782927938573248379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3119796175615672390658021 584961782927938573248379)
                      ·
                        rfl

theorem cell23_1139209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_1139209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139209 prefixEnd_1139209 := by exact prefixLift 1139209
  have htrace : WordTrace (prefixWord ++ tailWord_1139209) baseStart_1139209 baseEnd_1139209 := by
    simpa [prefixWord, tailWord_1139209, baseEnd_1139209] using wordTrace_append hprefix tailTrace_1139209
  have hstable : (prefixWord ++ tailWord_1139209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139209).length < 2 ^ (prefixWord ++ tailWord_1139209).sum := by decide
  have hdescent : baseEnd_1139209 < baseStart_1139209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139219 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 5, 4]
def baseStart_1139219 : Nat := 118140960795 + 1139219 * 2 ^ 59
def prefixEnd_1139219 : Nat := 4983230072969 + 3 ^ 40 * 1139219 * 2
def baseEnd_1139219 : Nat := 194988972578161178041111

theorem tailTrace_1139219 : CollatzResearch.WordTrace tailWord_1139219 prefixEnd_1139219 194988972578161178041111 := by
  unfold tailWord_1139219
  simp only [CollatzResearch.WordTrace]
  refine ⟨41550730459811600960348711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27700486973207733973565807 41550730459811600960348711)
  ·
    refine ⟨62326095689717401440523067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41550730459811600960348711 62326095689717401440523067)
    ·
      refine ⟨93489143534576102160784601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62326095689717401440523067 93489143534576102160784601)
      ·
        refine ⟨70116857650932076620588451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93489143534576102160784601 70116857650932076620588451)
        ·
          refine ⟨105175286476398114930882677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70116857650932076620588451 105175286476398114930882677)
          ·
            refine ⟨9860183107162323274770251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105175286476398114930882677 9860183107162323274770251)
            ·
              refine ⟨14790274660743484912155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860183107162323274770251 14790274660743484912155377)
              ·
                refine ⟨11092705995557613684116533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14790274660743484912155377 11092705995557613684116533)
                ·
                  refine ⟨1039941187083526282885925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11092705995557613684116533 1039941187083526282885925)
                  ·
                    refine ⟨194988972578161178041111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1039941187083526282885925 194988972578161178041111)
                    ·
                      rfl

theorem cell23_1139219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 4].length) (baseStart_1139219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139219 prefixEnd_1139219 := by exact prefixLift 1139219
  have htrace : WordTrace (prefixWord ++ tailWord_1139219) baseStart_1139219 baseEnd_1139219 := by
    simpa [prefixWord, tailWord_1139219, baseEnd_1139219] using wordTrace_append hprefix tailTrace_1139219
  have hstable : (prefixWord ++ tailWord_1139219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139219).length < 2 ^ (prefixWord ++ tailWord_1139219).sum := by decide
  have hdescent : baseEnd_1139219 < baseStart_1139219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139226 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_1139226 : Nat := 118140960795 + 1139226 * 2 ^ 59
def prefixEnd_1139226 : Nat := 4983230072969 + 3 ^ 40 * 1139226 * 2
def baseEnd_1139226 : Nat := 584970512099065006735801

theorem tailTrace_1139226 : CollatzResearch.WordTrace tailWord_1139226 prefixEnd_1139226 584970512099065006735801 := by
  unfold tailWord_1139226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387746442696560288963383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27700657180524160770569021 10387746442696560288963383)
  ·
    refine ⟨15581619664044840433445075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387746442696560288963383 15581619664044840433445075)
    ·
      refine ⟨23372429496067260650167613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581619664044840433445075 23372429496067260650167613)
      ·
        refine ⟨8764661061025222743812855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23372429496067260650167613 8764661061025222743812855)
        ·
          refine ⟨13146991591537834115719283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8764661061025222743812855 13146991591537834115719283)
          ·
            refine ⟨19720487387306751173578925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13146991591537834115719283 19720487387306751173578925)
            ·
              refine ⟨7395182770240031690092097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19720487387306751173578925 7395182770240031690092097)
              ·
                refine ⟨5546387077680023767569073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7395182770240031690092097 5546387077680023767569073)
                ·
                  refine ⟨4159790308260017825676805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5546387077680023767569073 4159790308260017825676805)
                  ·
                    refine ⟨779960682798753342314401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4159790308260017825676805 779960682798753342314401)
                    ·
                      refine ⟨584970512099065006735801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 779960682798753342314401 584970512099065006735801)
                      ·
                        rfl

theorem cell23_1139226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_1139226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139226 prefixEnd_1139226 := by exact prefixLift 1139226
  have htrace : WordTrace (prefixWord ++ tailWord_1139226) baseStart_1139226 baseEnd_1139226 := by
    simpa [prefixWord, tailWord_1139226, baseEnd_1139226] using wordTrace_append hprefix tailTrace_1139226
  have hstable : (prefixWord ++ tailWord_1139226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139226).length < 2 ^ (prefixWord ++ tailWord_1139226).sum := by decide
  have hdescent : baseEnd_1139226 < baseStart_1139226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139249 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 6]
def baseStart_1139249 : Nat := 118140960795 + 1139249 * 2 ^ 59
def prefixEnd_1139249 : Nat := 4983230072969 + 3 ^ 40 * 1139249 * 2
def baseEnd_1139249 : Nat := 64998035794902046305355

theorem tailTrace_1139249 : CollatzResearch.WordTrace tailWord_1139249 prefixEnd_1139249 64998035794902046305355 := by
  unfold tailWord_1139249
  simp only [CollatzResearch.WordTrace]
  refine ⟨41551824649702916083940801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27701216433135277389293867 41551824649702916083940801)
  ·
    refine ⟨31163868487277187062955601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41551824649702916083940801 31163868487277187062955601)
    ·
      refine ⟨23372901365457890297216701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31163868487277187062955601 23372901365457890297216701)
      ·
        refine ⟨8764838012046708861456263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23372901365457890297216701 8764838012046708861456263)
        ·
          refine ⟨13147257018070063292184395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8764838012046708861456263 13147257018070063292184395)
          ·
            refine ⟨19720885527105094938276593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13147257018070063292184395 19720885527105094938276593)
            ·
              refine ⟨14790664145328821203707445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19720885527105094938276593 14790664145328821203707445)
              ·
                refine ⟨1386624763624576987847573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14790664145328821203707445 1386624763624576987847573)
                ·
                  refine ⟨64998035794902046305355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1386624763624576987847573 64998035794902046305355)
                  ·
                    rfl

theorem cell23_1139249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_1139249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139249 prefixEnd_1139249 := by exact prefixLift 1139249
  have htrace : WordTrace (prefixWord ++ tailWord_1139249) baseStart_1139249 baseEnd_1139249 := by
    simpa [prefixWord, tailWord_1139249, baseEnd_1139249] using wordTrace_append hprefix tailTrace_1139249
  have hstable : (prefixWord ++ tailWord_1139249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139249).length < 2 ^ (prefixWord ++ tailWord_1139249).sum := by decide
  have hdescent : baseEnd_1139249 < baseStart_1139249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139319 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1139319 : Nat := 118140960795 + 1139319 * 2 ^ 59
def prefixEnd_1139319 : Nat := 4983230072969 + 3 ^ 40 * 1139319 * 2
def baseEnd_1139319 : Nat := 585018265799933142872873

theorem tailTrace_1139319 : CollatzResearch.WordTrace tailWord_1139319 prefixEnd_1139319 585018265799933142872873 := by
  unfold tailWord_1139319
  simp only [CollatzResearch.WordTrace]
  refine ⟨41554377759449318038989011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27702918506299545359326007 41554377759449318038989011)
  ·
    refine ⟨62331566639173977058483517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41554377759449318038989011 62331566639173977058483517)
    ·
      refine ⟨23374337489690241396931319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62331566639173977058483517 23374337489690241396931319)
      ·
        refine ⟨35061506234535362095396979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23374337489690241396931319 35061506234535362095396979)
        ·
          refine ⟨52592259351803043143095469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35061506234535362095396979 52592259351803043143095469)
          ·
            refine ⟨19722097256926141178660801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52592259351803043143095469 19722097256926141178660801)
            ·
              refine ⟨14791572942694605883995601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19722097256926141178660801 14791572942694605883995601)
              ·
                refine ⟨11093679707020954412996701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14791572942694605883995601 11093679707020954412996701)
                ·
                  refine ⟨4160129890132857904873763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11093679707020954412996701 4160129890132857904873763)
                  ·
                    refine ⟨6240194835199286857310645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4160129890132857904873763 6240194835199286857310645)
                    ·
                      refine ⟨585018265799933142872873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6240194835199286857310645 585018265799933142872873)
                      ·
                        rfl

theorem cell23_1139319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1139319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139319 prefixEnd_1139319 := by exact prefixLift 1139319
  have htrace : WordTrace (prefixWord ++ tailWord_1139319) baseStart_1139319 baseEnd_1139319 := by
    simpa [prefixWord, tailWord_1139319, baseEnd_1139319] using wordTrace_append hprefix tailTrace_1139319
  have hstable : (prefixWord ++ tailWord_1139319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139319).length < 2 ^ (prefixWord ++ tailWord_1139319).sum := by decide
  have hdescent : baseEnd_1139319 < baseStart_1139319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139356 : List Nat := [2, 2, 3, 2, 2, 1, 3, 8]
def baseStart_1139356 : Nat := 118140960795 + 1139356 * 2 ^ 59
def prefixEnd_1139356 : Nat := 4983230072969 + 3 ^ 40 * 1139356 * 2
def baseEnd_1139356 : Nat := 21668046836449981411489

theorem tailTrace_1139356 : CollatzResearch.WordTrace tailWord_1139356 prefixEnd_1139356 21668046836449981411489 := by
  unfold tailWord_1139356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20777863630157636679042961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27703818173543515572057281 20777863630157636679042961)
  ·
    refine ⟨15583397722618227509282221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20777863630157636679042961 15583397722618227509282221)
    ·
      refine ⟨5843774145981835315980833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15583397722618227509282221 5843774145981835315980833)
      ·
        refine ⟨4382830609486376486985625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5843774145981835315980833 4382830609486376486985625)
        ·
          refine ⟨3287122957114782365239219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4382830609486376486985625 3287122957114782365239219)
          ·
            refine ⟨4930684435672173547858829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287122957114782365239219 4930684435672173547858829)
            ·
              refine ⟨1849006663377065080447061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4930684435672173547858829 1849006663377065080447061)
              ·
                refine ⟨21668046836449981411489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1849006663377065080447061 21668046836449981411489)
                ·
                  rfl

theorem cell23_1139356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 8].length) (baseStart_1139356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139356 prefixEnd_1139356 := by exact prefixLift 1139356
  have htrace : WordTrace (prefixWord ++ tailWord_1139356) baseStart_1139356 baseEnd_1139356 := by
    simpa [prefixWord, tailWord_1139356, baseEnd_1139356] using wordTrace_append hprefix tailTrace_1139356
  have hstable : (prefixWord ++ tailWord_1139356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139356).length < 2 ^ (prefixWord ++ tailWord_1139356).sum := by decide
  have hdescent : baseEnd_1139356 < baseStart_1139356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139373 : List Nat := [1, 5, 2, 1, 1, 3, 3, 7]
def baseStart_1139373 : Nat := 118140960795 + 1139373 * 2 ^ 59
def prefixEnd_1139373 : Nat := 4983230072969 + 3 ^ 40 * 1139373 * 2
def baseEnd_1139373 : Nat := 21668370139084293762875

theorem tailTrace_1139373 : CollatzResearch.WordTrace tailWord_1139373 prefixEnd_1139373 21668370139084293762875 := by
  unfold tailWord_1139373
  simp only [CollatzResearch.WordTrace]
  refine ⟨41556347301253685261454773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27704231534169123507636515 41556347301253685261454773)
  ·
    refine ⟨3895907559492532993261385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41556347301253685261454773 3895907559492532993261385)
    ·
      refine ⟨2921930669619399744946039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895907559492532993261385 2921930669619399744946039)
      ·
        refine ⟨4382896004429099617419059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921930669619399744946039 4382896004429099617419059)
        ·
          refine ⟨6574344006643649426128589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382896004429099617419059 6574344006643649426128589)
          ·
            refine ⟨2465379002491368534798221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6574344006643649426128589 2465379002491368534798221)
            ·
              refine ⟨924517125934263200549333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2465379002491368534798221 924517125934263200549333)
              ·
                refine ⟨21668370139084293762875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 924517125934263200549333 21668370139084293762875)
                ·
                  rfl

theorem cell23_1139373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 7].length) (baseStart_1139373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139373 prefixEnd_1139373 := by exact prefixLift 1139373
  have htrace : WordTrace (prefixWord ++ tailWord_1139373) baseStart_1139373 baseEnd_1139373 := by
    simpa [prefixWord, tailWord_1139373, baseEnd_1139373] using wordTrace_append hprefix tailTrace_1139373
  have hstable : (prefixWord ++ tailWord_1139373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139373).length < 2 ^ (prefixWord ++ tailWord_1139373).sum := by decide
  have hdescent : baseEnd_1139373 < baseStart_1139373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139400 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_1139400 : Nat := 118140960795 + 1139400 * 2 ^ 59
def prefixEnd_1139400 : Nat := 4983230072969 + 3 ^ 40 * 1139400 * 2
def baseEnd_1139400 : Nat := 585059857732947325960001

theorem tailTrace_1139400 : CollatzResearch.WordTrace tailWord_1139400 prefixEnd_1139400 585059857732947325960001 := by
  unfold tailWord_1139400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20778666036077934436343827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27704888048103912581791769 20778666036077934436343827)
  ·
    refine ⟨31167999054116901654515741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20778666036077934436343827 31167999054116901654515741)
    ·
      refine ⟨11687999645293838120443403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31167999054116901654515741 11687999645293838120443403)
      ·
        refine ⟨17531999467940757180665105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11687999645293838120443403 17531999467940757180665105)
        ·
          refine ⟨13148999600955567885498829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17531999467940757180665105 13148999600955567885498829)
          ·
            refine ⟨4930874850358337957062061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13148999600955567885498829 4930874850358337957062061)
            ·
              refine ⟨1849078068884376733898273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4930874850358337957062061 1849078068884376733898273)
              ·
                refine ⟨1386808551663282550423705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849078068884376733898273 1386808551663282550423705)
                ·
                  refine ⟨1040106413747461912817779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1386808551663282550423705 1040106413747461912817779)
                  ·
                    refine ⟨1560159620621192869226669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040106413747461912817779 1560159620621192869226669)
                    ·
                      refine ⟨585059857732947325960001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560159620621192869226669 585059857732947325960001)
                      ·
                        rfl

theorem cell23_1139400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_1139400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139400 prefixEnd_1139400 := by exact prefixLift 1139400
  have htrace : WordTrace (prefixWord ++ tailWord_1139400) baseStart_1139400 baseEnd_1139400 := by
    simpa [prefixWord, tailWord_1139400, baseEnd_1139400] using wordTrace_append hprefix tailTrace_1139400
  have hstable : (prefixWord ++ tailWord_1139400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139400).length < 2 ^ (prefixWord ++ tailWord_1139400).sum := by decide
  have hdescent : baseEnd_1139400 < baseStart_1139400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139416 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1139416 : Nat := 118140960795 + 1139416 * 2 ^ 59
def prefixEnd_1139416 : Nat := 4983230072969 + 3 ^ 40 * 1139416 * 2
def baseEnd_1139416 : Nat := 195022691141139754453309

theorem tailTrace_1139416 : CollatzResearch.WordTrace tailWord_1139416 prefixEnd_1139416 195022691141139754453309 := by
  unfold tailWord_1139416
  simp only [CollatzResearch.WordTrace]
  refine ⟨20778957820048951802635051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27705277093398602403513401 20778957820048951802635051)
  ·
    refine ⟨31168436730073427703952577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20778957820048951802635051 31168436730073427703952577)
    ·
      refine ⟨23376327547555070777964433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31168436730073427703952577 23376327547555070777964433)
      ·
        refine ⟨17532245660666303083473325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23376327547555070777964433 17532245660666303083473325)
        ·
          refine ⟨6574592122749863656302497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17532245660666303083473325 6574592122749863656302497)
          ·
            refine ⟨4930944092062397742226873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574592122749863656302497 4930944092062397742226873)
            ·
              refine ⟨3698208069046798306670155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4930944092062397742226873 3698208069046798306670155)
              ·
                refine ⟨5547312103570197460005233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3698208069046798306670155 5547312103570197460005233)
                ·
                  refine ⟨4160484077677648095003925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5547312103570197460005233 4160484077677648095003925)
                  ·
                    refine ⟨195022691141139754453309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4160484077677648095003925 195022691141139754453309)
                    ·
                      rfl

theorem cell23_1139416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1139416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139416 prefixEnd_1139416 := by exact prefixLift 1139416
  have htrace : WordTrace (prefixWord ++ tailWord_1139416) baseStart_1139416 baseEnd_1139416 := by
    simpa [prefixWord, tailWord_1139416, baseEnd_1139416] using wordTrace_append hprefix tailTrace_1139416
  have hstable : (prefixWord ++ tailWord_1139416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139416).length < 2 ^ (prefixWord ++ tailWord_1139416).sum := by decide
  have hdescent : baseEnd_1139416 < baseStart_1139416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139419 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6]
def baseStart_1139419 : Nat := 118140960795 + 1139419 * 2 ^ 59
def prefixEnd_1139419 : Nat := 4983230072969 + 3 ^ 40 * 1139419 * 2
def baseEnd_1139419 : Nat := 585069613865382751622413

theorem tailTrace_1139419 : CollatzResearch.WordTrace tailWord_1139419 prefixEnd_1139419 585069613865382751622413 := by
  unfold tailWord_1139419
  simp only [CollatzResearch.WordTrace]
  refine ⟨41558025059087035117629311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27705350039391356745086207 41558025059087035117629311)
  ·
    refine ⟨62337037588630552676443967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41558025059087035117629311 62337037588630552676443967)
    ·
      refine ⟨93505556382945829014665951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62337037588630552676443967 93505556382945829014665951)
      ·
        refine ⟨140258334574418743521998927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93505556382945829014665951 140258334574418743521998927)
        ·
          refine ⟨210387501861628115282998391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140258334574418743521998927 210387501861628115282998391)
          ·
            refine ⟨315581252792442172924497587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210387501861628115282998391 315581252792442172924497587)
            ·
              refine ⟨473371879188663259386746381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315581252792442172924497587 473371879188663259386746381)
              ·
                refine ⟨177514454695748722270029893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473371879188663259386746381 177514454695748722270029893)
                ·
                  refine ⟨33283960255452885425630605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177514454695748722270029893 33283960255452885425630605)
                  ·
                    refine ⟨12481485095794832034611477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33283960255452885425630605 12481485095794832034611477)
                    ·
                      refine ⟨585069613865382751622413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12481485095794832034611477 585069613865382751622413)
                      ·
                        rfl

theorem cell23_1139419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_1139419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139419 prefixEnd_1139419 := by exact prefixLift 1139419
  have htrace : WordTrace (prefixWord ++ tailWord_1139419) baseStart_1139419 baseEnd_1139419 := by
    simpa [prefixWord, tailWord_1139419, baseEnd_1139419] using wordTrace_append hprefix tailTrace_1139419
  have hstable : (prefixWord ++ tailWord_1139419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139419).length < 2 ^ (prefixWord ++ tailWord_1139419).sum := by decide
  have hdescent : baseEnd_1139419 < baseStart_1139419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139427 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1139427 : Nat := 118140960795 + 1139427 * 2 ^ 59
def prefixEnd_1139427 : Nat := 4983230072969 + 3 ^ 40 * 1139427 * 2
def baseEnd_1139427 : Nat := 585073721710618720322377

theorem tailTrace_1139427 : CollatzResearch.WordTrace tailWord_1139427 prefixEnd_1139427 585073721710618720322377 := by
  unfold tailWord_1139427
  simp only [CollatzResearch.WordTrace]
  refine ⟨41558316843058052483920535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27705544562038701655947023 41558316843058052483920535)
  ·
    refine ⟨62337475264587078725880803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41558316843058052483920535 62337475264587078725880803)
    ·
      refine ⟨93506212896880618088821205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62337475264587078725880803 93506212896880618088821205)
      ·
        refine ⟨2191551864770639486456747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 93506212896880618088821205 2191551864770639486456747)
        ·
          refine ⟨3287327797155959229685121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191551864770639486456747 3287327797155959229685121)
          ·
            refine ⟨2465495847866969422263841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3287327797155959229685121 2465495847866969422263841)
            ·
              refine ⟨1849121885900227066697881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2465495847866969422263841 1849121885900227066697881)
              ·
                refine ⟨1386841414425170300023411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849121885900227066697881 1386841414425170300023411)
                ·
                  refine ⟨2080262121637755450035117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386841414425170300023411 2080262121637755450035117)
                  ·
                    refine ⟨780098295614158293763169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080262121637755450035117 780098295614158293763169)
                    ·
                      refine ⟨585073721710618720322377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780098295614158293763169 585073721710618720322377)
                      ·
                        rfl

theorem cell23_1139427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1139427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139427 prefixEnd_1139427 := by exact prefixLift 1139427
  have htrace : WordTrace (prefixWord ++ tailWord_1139427) baseStart_1139427 baseEnd_1139427 := by
    simpa [prefixWord, tailWord_1139427, baseEnd_1139427] using wordTrace_append hprefix tailTrace_1139427
  have hstable : (prefixWord ++ tailWord_1139427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139427).length < 2 ^ (prefixWord ++ tailWord_1139427).sum := by decide
  have hdescent : baseEnd_1139427 < baseStart_1139427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139463 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 7]
def baseStart_1139463 : Nat := 118140960795 + 1139463 * 2 ^ 59
def prefixEnd_1139463 : Nat := 4983230072969 + 3 ^ 40 * 1139463 * 2
def baseEnd_1139463 : Nat := 65010245223797842163579

theorem tailTrace_1139463 : CollatzResearch.WordTrace tailWord_1139463 prefixEnd_1139463 65010245223797842163579 := by
  unfold tailWord_1139463
  simp only [CollatzResearch.WordTrace]
  refine ⟨41559629870927630632231043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27706419913951753754820695 41559629870927630632231043)
  ·
    refine ⟨62339444806391445948346565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41559629870927630632231043 62339444806391445948346565)
    ·
      refine ⟨11688645901198396115314981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62339444806391445948346565 11688645901198396115314981)
      ·
        refine ⟨2191621106474699271621559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11688645901198396115314981 2191621106474699271621559)
        ·
          refine ⟨3287431659712048907432339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191621106474699271621559 3287431659712048907432339)
          ·
            refine ⟨4931147489568073361148509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287431659712048907432339 4931147489568073361148509)
            ·
              refine ⟨1849180308588027510430691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931147489568073361148509 1849180308588027510430691)
              ·
                refine ⟨2773770462882041265646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849180308588027510430691 2773770462882041265646037)
                ·
                  refine ⟨65010245223797842163579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2773770462882041265646037 65010245223797842163579)
                  ·
                    rfl

theorem cell23_1139463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 7].length) (baseStart_1139463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139463 prefixEnd_1139463 := by exact prefixLift 1139463
  have htrace : WordTrace (prefixWord ++ tailWord_1139463) baseStart_1139463 baseEnd_1139463 := by
    simpa [prefixWord, tailWord_1139463, baseEnd_1139463] using wordTrace_append hprefix tailTrace_1139463
  have hstable : (prefixWord ++ tailWord_1139463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139463).length < 2 ^ (prefixWord ++ tailWord_1139463).sum := by decide
  have hdescent : baseEnd_1139463 < baseStart_1139463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139493 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1139493 : Nat := 118140960795 + 1139493 * 2 ^ 59
def prefixEnd_1139493 : Nat := 4983230072969 + 3 ^ 40 * 1139493 * 2
def baseEnd_1139493 : Nat := 195035870477938487365691

theorem tailTrace_1139493 : CollatzResearch.WordTrace tailWord_1139493 prefixEnd_1139493 195035870477938487365691 := by
  unfold tailWord_1139493
  simp only [CollatzResearch.WordTrace]
  refine ⟨41560724060818945755823133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27707149373879297170548755 41560724060818945755823133)
  ·
    refine ⟨15585271522807104658433675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41560724060818945755823133 15585271522807104658433675)
    ·
      refine ⟨23377907284210656987650513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15585271522807104658433675 23377907284210656987650513)
      ·
        refine ⟨17533430463157992740737885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23377907284210656987650513 17533430463157992740737885)
        ·
          refine ⟨6575036423684247277776707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17533430463157992740737885 6575036423684247277776707)
          ·
            refine ⟨9862554635526370916665061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6575036423684247277776707 9862554635526370916665061)
            ·
              refine ⟨1849228994161194546874699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9862554635526370916665061 1849228994161194546874699)
              ·
                refine ⟨2773843491241791820312049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1849228994161194546874699 2773843491241791820312049)
                ·
                  refine ⟨2080382618431343865234037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2773843491241791820312049 2080382618431343865234037)
                  ·
                    refine ⟨195035870477938487365691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2080382618431343865234037 195035870477938487365691)
                    ·
                      rfl

theorem cell23_1139493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1139493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139493 prefixEnd_1139493 := by exact prefixLift 1139493
  have htrace : WordTrace (prefixWord ++ tailWord_1139493) baseStart_1139493 baseEnd_1139493 := by
    simpa [prefixWord, tailWord_1139493, baseEnd_1139493] using wordTrace_append hprefix tailTrace_1139493
  have hstable : (prefixWord ++ tailWord_1139493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139493).length < 2 ^ (prefixWord ++ tailWord_1139493).sum := by decide
  have hdescent : baseEnd_1139493 < baseStart_1139493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139514 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_1139514 : Nat := 118140960795 + 1139514 * 2 ^ 59
def prefixEnd_1139514 : Nat := 4983230072969 + 3 ^ 40 * 1139514 * 2
def baseEnd_1139514 : Nat := 65013154947506653326053

theorem tailTrace_1139514 : CollatzResearch.WordTrace tailWord_1139514 prefixEnd_1139514 65013154947506653326053 := by
  unfold tailWord_1139514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390372498435716585584399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27707659995828577561558397 10390372498435716585584399)
  ·
    refine ⟨15585558747653574878376599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10390372498435716585584399 15585558747653574878376599)
    ·
      refine ⟨23378338121480362317564899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15585558747653574878376599 23378338121480362317564899)
      ·
        refine ⟨35067507182220543476347349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23378338121480362317564899 35067507182220543476347349)
        ·
          refine ⟨821894699583293987726891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35067507182220543476347349 821894699583293987726891)
          ·
            refine ⟨1232842049374940981590337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821894699583293987726891 1232842049374940981590337)
            ·
              refine ⟨924631537031205736192753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232842049374940981590337 924631537031205736192753)
              ·
                refine ⟨693473652773404302144565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924631537031205736192753 693473652773404302144565)
                ·
                  refine ⟨65013154947506653326053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 693473652773404302144565 65013154947506653326053)
                  ·
                    rfl

theorem cell23_1139514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_1139514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139514 prefixEnd_1139514 := by exact prefixLift 1139514
  have htrace : WordTrace (prefixWord ++ tailWord_1139514) baseStart_1139514 baseEnd_1139514 := by
    simpa [prefixWord, tailWord_1139514, baseEnd_1139514] using wordTrace_append hprefix tailTrace_1139514
  have hstable : (prefixWord ++ tailWord_1139514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139514).length < 2 ^ (prefixWord ++ tailWord_1139514).sum := by decide
  have hdescent : baseEnd_1139514 < baseStart_1139514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139516 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1139516 : Nat := 118140960795 + 1139516 * 2 ^ 59
def prefixEnd_1139516 : Nat := 4983230072969 + 3 ^ 40 * 1139516 * 2
def baseEnd_1139516 : Nat := 585119421488868872109467

theorem tailTrace_1139516 : CollatzResearch.WordTrace tailWord_1139516 prefixEnd_1139516 585119421488868872109467 := by
  unfold tailWord_1139516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20780781469867810341955201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27707708626490413789273601 20780781469867810341955201)
  ·
    refine ⟨15585586102400857756466401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20780781469867810341955201 15585586102400857756466401)
    ·
      refine ⟨11689189576800643317349801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15585586102400857756466401 11689189576800643317349801)
      ·
        refine ⟨8766892182600482488012351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11689189576800643317349801 8766892182600482488012351)
        ·
          refine ⟨13150338273900723732018527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8766892182600482488012351 13150338273900723732018527)
          ·
            refine ⟨19725507410851085598027791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13150338273900723732018527 19725507410851085598027791)
            ·
              refine ⟨29588261116276628397041687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19725507410851085598027791 29588261116276628397041687)
              ·
                refine ⟨44382391674414942595562531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29588261116276628397041687 44382391674414942595562531)
                ·
                  refine ⟨66573587511622413893343797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44382391674414942595562531 66573587511622413893343797)
                  ·
                    refine ⟨6241273829214601302500981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66573587511622413893343797 6241273829214601302500981)
                    ·
                      refine ⟨585119421488868872109467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6241273829214601302500981 585119421488868872109467)
                      ·
                        rfl

theorem cell23_1139516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1139516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139516 prefixEnd_1139516 := by exact prefixLift 1139516
  have htrace : WordTrace (prefixWord ++ tailWord_1139516) baseStart_1139516 baseEnd_1139516 := by
    simpa [prefixWord, tailWord_1139516, baseEnd_1139516] using wordTrace_append hprefix tailTrace_1139516
  have hstable : (prefixWord ++ tailWord_1139516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139516).length < 2 ^ (prefixWord ++ tailWord_1139516).sum := by decide
  have hdescent : baseEnd_1139516 < baseStart_1139516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139523 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 3, 4]
def baseStart_1139523 : Nat := 118140960795 + 1139523 * 2 ^ 59
def prefixEnd_1139523 : Nat := 4983230072969 + 3 ^ 40 * 1139523 * 2
def baseEnd_1139523 : Nat := 195041005284483448240645

theorem tailTrace_1139523 : CollatzResearch.WordTrace tailWord_1139523 prefixEnd_1139523 195041005284483448240645 := by
  unfold tailWord_1139523
  simp only [CollatzResearch.WordTrace]
  refine ⟨41561818250710260879415223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27707878833806840586276815 41561818250710260879415223)
  ·
    refine ⟨62342727376065391319122835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41561818250710260879415223 62342727376065391319122835)
    ·
      refine ⟨93514091064098086978684253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62342727376065391319122835 93514091064098086978684253)
      ·
        refine ⟨35067784149036782617006595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93514091064098086978684253 35067784149036782617006595)
        ·
          refine ⟨52601676223555173925509893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35067784149036782617006595 52601676223555173925509893)
          ·
            refine ⟨9862814291916595111033105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52601676223555173925509893 9862814291916595111033105)
            ·
              refine ⟨7397110718937446333274829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9862814291916595111033105 7397110718937446333274829)
              ·
                refine ⟨2773916519601542374978061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7397110718937446333274829 2773916519601542374978061)
                ·
                  refine ⟨1040218694850578390616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2773916519601542374978061 1040218694850578390616773)
                  ·
                    refine ⟨195041005284483448240645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1040218694850578390616773 195041005284483448240645)
                    ·
                      rfl

theorem cell23_1139523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 4].length) (baseStart_1139523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139523 prefixEnd_1139523 := by exact prefixLift 1139523
  have htrace : WordTrace (prefixWord ++ tailWord_1139523) baseStart_1139523 baseEnd_1139523 := by
    simpa [prefixWord, tailWord_1139523, baseEnd_1139523] using wordTrace_append hprefix tailTrace_1139523
  have hstable : (prefixWord ++ tailWord_1139523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139523).length < 2 ^ (prefixWord ++ tailWord_1139523).sum := by decide
  have hdescent : baseEnd_1139523 < baseStart_1139523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139573 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1139573 : Nat := 118140960795 + 1139573 * 2 ^ 59
def prefixEnd_1139573 : Nat := 4983230072969 + 3 ^ 40 * 1139573 * 2
def baseEnd_1139573 : Nat := 585148689886175149096705

theorem tailTrace_1139573 : CollatzResearch.WordTrace tailWord_1139573 prefixEnd_1139573 585148689886175149096705 := by
  unfold tailWord_1139573
  simp only [CollatzResearch.WordTrace]
  refine ⟨41563641900529119418735373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27709094600352746279156915 41563641900529119418735373)
  ·
    refine ⟨15586365712698419782025765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41563641900529119418735373 15586365712698419782025765)
    ·
      refine ⟨2922443571130953709129831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15586365712698419782025765 2922443571130953709129831)
      ·
        refine ⟨4383665356696430563694747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2922443571130953709129831 4383665356696430563694747)
        ·
          refine ⟨6575498035044645845542121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4383665356696430563694747 6575498035044645845542121)
          ·
            refine ⟨4931623526283484384156591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6575498035044645845542121 4931623526283484384156591)
            ·
              refine ⟨7397435289425226576234887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4931623526283484384156591 7397435289425226576234887)
              ·
                refine ⟨11096152934137839864352331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7397435289425226576234887 11096152934137839864352331)
                ·
                  refine ⟨16644229401206759796528497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11096152934137839864352331 16644229401206759796528497)
                  ·
                    refine ⟨12483172050905069847396373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16644229401206759796528497 12483172050905069847396373)
                    ·
                      refine ⟨585148689886175149096705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12483172050905069847396373 585148689886175149096705)
                      ·
                        rfl

theorem cell23_1139573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1139573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139573 prefixEnd_1139573 := by exact prefixLift 1139573
  have htrace : WordTrace (prefixWord ++ tailWord_1139573) baseStart_1139573 baseEnd_1139573 := by
    simpa [prefixWord, tailWord_1139573, baseEnd_1139573] using wordTrace_append hprefix tailTrace_1139573
  have hstable : (prefixWord ++ tailWord_1139573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139573).length < 2 ^ (prefixWord ++ tailWord_1139573).sum := by decide
  have hdescent : baseEnd_1139573 < baseStart_1139573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139574 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1139574 : Nat := 118140960795 + 1139574 * 2 ^ 59
def prefixEnd_1139574 : Nat := 4983230072969 + 3 ^ 40 * 1139574 * 2
def baseEnd_1139574 : Nat := 195049734455609881728067

theorem tailTrace_1139574 : CollatzResearch.WordTrace tailWord_1139574 prefixEnd_1139574 195049734455609881728067 := by
  unfold tailWord_1139574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597729898345343536845111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27709118915683664393014517 2597729898345343536845111)
  ·
    refine ⟨3896594847518015305267667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597729898345343536845111 3896594847518015305267667)
    ·
      refine ⟨5844892271277022957901501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3896594847518015305267667 5844892271277022957901501)
      ·
        refine ⟨2191834601728883609213063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5844892271277022957901501 2191834601728883609213063)
        ·
          refine ⟨3287751902593325413819595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191834601728883609213063 3287751902593325413819595)
          ·
            refine ⟨4931627853889988120729393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3287751902593325413819595 4931627853889988120729393)
            ·
              refine ⟨3698720890417491090547045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931627853889988120729393 3698720890417491090547045)
              ·
                refine ⟨693510166953279579477571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3698720890417491090547045 693510166953279579477571)
                ·
                  refine ⟨1040265250429919369216357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693510166953279579477571 1040265250429919369216357)
                  ·
                    refine ⟨195049734455609881728067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1040265250429919369216357 195049734455609881728067)
                    ·
                      rfl

theorem cell23_1139574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1139574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139574 prefixEnd_1139574 := by exact prefixLift 1139574
  have htrace : WordTrace (prefixWord ++ tailWord_1139574) baseStart_1139574 baseEnd_1139574 := by
    simpa [prefixWord, tailWord_1139574, baseEnd_1139574] using wordTrace_append hprefix tailTrace_1139574
  have hstable : (prefixWord ++ tailWord_1139574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139574).length < 2 ^ (prefixWord ++ tailWord_1139574).sum := by decide
  have hdescent : baseEnd_1139574 < baseStart_1139574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139576 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1139576 : Nat := 118140960795 + 1139576 * 2 ^ 59
def prefixEnd_1139576 : Nat := 4983230072969 + 3 ^ 40 * 1139576 * 2
def baseEnd_1139576 : Nat := 585150230328138637359191

theorem tailTrace_1139576 : CollatzResearch.WordTrace tailWord_1139576 prefixEnd_1139576 585150230328138637359191 := by
  unfold tailWord_1139576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20781875659759125465547291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27709167546345500620729721 20781875659759125465547291)
  ·
    refine ⟨31172813489638688198320937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20781875659759125465547291 31172813489638688198320937)
    ·
      refine ⟨23379610117229016148740703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31172813489638688198320937 23379610117229016148740703)
      ·
        refine ⟨35069415175843524223111055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23379610117229016148740703 35069415175843524223111055)
        ·
          refine ⟨52604122763765286334666583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35069415175843524223111055 52604122763765286334666583)
          ·
            refine ⟨78906184145647929501999875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52604122763765286334666583 78906184145647929501999875)
            ·
              refine ⟨118359276218471894252999813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78906184145647929501999875 118359276218471894252999813)
              ·
                refine ⟨22192364290963480172437465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118359276218471894252999813 22192364290963480172437465)
                ·
                  refine ⟨16644273218222610129328099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22192364290963480172437465 16644273218222610129328099)
                  ·
                    refine ⟨24966409827333915193992149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16644273218222610129328099 24966409827333915193992149)
                    ·
                      refine ⟨585150230328138637359191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24966409827333915193992149 585150230328138637359191)
                      ·
                        rfl

theorem cell23_1139576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1139576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139576 prefixEnd_1139576 := by exact prefixLift 1139576
  have htrace : WordTrace (prefixWord ++ tailWord_1139576) baseStart_1139576 baseEnd_1139576 := by
    simpa [prefixWord, tailWord_1139576, baseEnd_1139576] using wordTrace_append hprefix tailTrace_1139576
  have hstable : (prefixWord ++ tailWord_1139576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139576).length < 2 ^ (prefixWord ++ tailWord_1139576).sum := by decide
  have hdescent : baseEnd_1139576 < baseStart_1139576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139613 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1139613 : Nat := 118140960795 + 1139613 * 2 ^ 59
def prefixEnd_1139613 : Nat := 4983230072969 + 3 ^ 40 * 1139613 * 2
def baseEnd_1139613 : Nat := 195056409704118330865507

theorem tailTrace_1139613 : CollatzResearch.WordTrace tailWord_1139613 prefixEnd_1139613 195056409704118330865507 := by
  unfold tailWord_1139613
  simp only [CollatzResearch.WordTrace]
  refine ⟨41565100820384206250191493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27710067213589470833460995 41565100820384206250191493)
  ·
    refine ⟨7793456403822038671910905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41565100820384206250191493 7793456403822038671910905)
    ·
      refine ⟨5845092302866529003933179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7793456403822038671910905 5845092302866529003933179)
      ·
        refine ⟨8767638454299793505899769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5845092302866529003933179 8767638454299793505899769)
        ·
          refine ⟨6575728840724845129424827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8767638454299793505899769 6575728840724845129424827)
          ·
            refine ⟨9863593261087267694137241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6575728840724845129424827 9863593261087267694137241)
            ·
              refine ⟨7397694945815450770602931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9863593261087267694137241 7397694945815450770602931)
              ·
                refine ⟨11096542418723176155904397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7397694945815450770602931 11096542418723176155904397)
                ·
                  refine ⟨4161203407021191058464149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11096542418723176155904397 4161203407021191058464149)
                  ·
                    refine ⟨195056409704118330865507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4161203407021191058464149 195056409704118330865507)
                    ·
                      rfl

theorem cell23_1139613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1139613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139613 prefixEnd_1139613 := by exact prefixLift 1139613
  have htrace : WordTrace (prefixWord ++ tailWord_1139613) baseStart_1139613 baseEnd_1139613 := by
    simpa [prefixWord, tailWord_1139613, baseEnd_1139613] using wordTrace_append hprefix tailTrace_1139613
  have hstable : (prefixWord ++ tailWord_1139613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139613).length < 2 ^ (prefixWord ++ tailWord_1139613).sum := by decide
  have hdescent : baseEnd_1139613 < baseStart_1139613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139620 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_1139620 : Nat := 118140960795 + 1139620 * 2 ^ 59
def prefixEnd_1139620 : Nat := 4983230072969 + 3 ^ 40 * 1139620 * 2
def baseEnd_1139620 : Nat := 585172823476936465208989

theorem tailTrace_1139620 : CollatzResearch.WordTrace tailWord_1139620 prefixEnd_1139620 585172823476936465208989 := by
  unfold tailWord_1139620
  simp only [CollatzResearch.WordTrace]
  refine ⟨20782678065679423222848157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27710237420905897630464209 20782678065679423222848157)
  ·
    refine ⟨7793504274629783708568059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20782678065679423222848157 7793504274629783708568059)
    ·
      refine ⟨11690256411944675562852089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7793504274629783708568059 11690256411944675562852089)
      ·
        refine ⟨8767692308958506672139067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11690256411944675562852089 8767692308958506672139067)
        ·
          refine ⟨13151538463437760008208601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8767692308958506672139067 13151538463437760008208601)
          ·
            refine ⟨9863653847578320006156451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13151538463437760008208601 9863653847578320006156451)
            ·
              refine ⟨14795480771367480009234677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9863653847578320006156451 14795480771367480009234677)
              ·
                refine ⟨1387076322315701250865751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14795480771367480009234677 1387076322315701250865751)
                ·
                  refine ⟨2080614483473551876298627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387076322315701250865751 2080614483473551876298627)
                  ·
                    refine ⟨3120921725210327814447941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2080614483473551876298627 3120921725210327814447941)
                    ·
                      refine ⟨585172823476936465208989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3120921725210327814447941 585172823476936465208989)
                      ·
                        rfl

theorem cell23_1139620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_1139620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139620 prefixEnd_1139620 := by exact prefixLift 1139620
  have htrace : WordTrace (prefixWord ++ tailWord_1139620) baseStart_1139620 baseEnd_1139620 := by
    simpa [prefixWord, tailWord_1139620, baseEnd_1139620] using wordTrace_append hprefix tailTrace_1139620
  have hstable : (prefixWord ++ tailWord_1139620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139620).length < 2 ^ (prefixWord ++ tailWord_1139620).sum := by decide
  have hdescent : baseEnd_1139620 < baseStart_1139620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139638 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1139638 : Nat := 118140960795 + 1139638 * 2 ^ 59
def prefixEnd_1139638 : Nat := 4983230072969 + 3 ^ 40 * 1139638 * 2
def baseEnd_1139638 : Nat := 65020229569857488309323

theorem tailTrace_1139638 : CollatzResearch.WordTrace tailWord_1139638 prefixEnd_1139638 65020229569857488309323 := by
  unfold tailWord_1139638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597875790330852219990723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27710675096862423679901045 2597875790330852219990723)
  ·
    refine ⟨3896813685496278329986085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2597875790330852219990723 3896813685496278329986085)
    ·
      refine ⟨730652566030552186872391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3896813685496278329986085 730652566030552186872391)
      ·
        refine ⟨1095978849045828280308587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730652566030552186872391 1095978849045828280308587)
        ·
          refine ⟨1643968273568742420462881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1095978849045828280308587 1643968273568742420462881)
          ·
            refine ⟨1232976205176556815347161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1643968273568742420462881 1232976205176556815347161)
            ·
              refine ⟨924732153882417611510371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232976205176556815347161 924732153882417611510371)
              ·
                refine ⟨1387098230823626417265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924732153882417611510371 1387098230823626417265557)
                ·
                  refine ⟨65020229569857488309323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1387098230823626417265557 65020229569857488309323)
                  ·
                    rfl

theorem cell23_1139638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1139638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139638 prefixEnd_1139638 := by exact prefixLift 1139638
  have htrace : WordTrace (prefixWord ++ tailWord_1139638) baseStart_1139638 baseEnd_1139638 := by
    simpa [prefixWord, tailWord_1139638, baseEnd_1139638] using wordTrace_append hprefix tailTrace_1139638
  have hstable : (prefixWord ++ tailWord_1139638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139638).length < 2 ^ (prefixWord ++ tailWord_1139638).sum := by decide
  have hdescent : baseEnd_1139638 < baseStart_1139638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139674 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_1139674 : Nat := 118140960795 + 1139674 * 2 ^ 59
def prefixEnd_1139674 : Nat := 4983230072969 + 3 ^ 40 * 1139674 * 2
def baseEnd_1139674 : Nat := 585200551432279253933741

theorem tailTrace_1139674 : CollatzResearch.WordTrace tailWord_1139674 prefixEnd_1139674 585200551432279253933741 := by
  unfold tailWord_1139674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391831418290803417040519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27711550448775475778774717 10391831418290803417040519)
  ·
    refine ⟨15587747127436205125560779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10391831418290803417040519 15587747127436205125560779)
    ·
      refine ⟨23381620691154307688341169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15587747127436205125560779 23381620691154307688341169)
      ·
        refine ⟨17536215518365730766255877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23381620691154307688341169 17536215518365730766255877)
        ·
          refine ⟨3288040409693574518672977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17536215518365730766255877 3288040409693574518672977)
          ·
            refine ⟨2466030307270180889004733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288040409693574518672977 2466030307270180889004733)
            ·
              refine ⟨924761365226317833376775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2466030307270180889004733 924761365226317833376775)
              ·
                refine ⟨1387142047839476750065163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924761365226317833376775 1387142047839476750065163)
                ·
                  refine ⟨2080713071759215125097745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387142047839476750065163 2080713071759215125097745)
                  ·
                    refine ⟨1560534803819411343823309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2080713071759215125097745 1560534803819411343823309)
                    ·
                      refine ⟨585200551432279253933741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560534803819411343823309 585200551432279253933741)
                      ·
                        rfl

theorem cell23_1139674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_1139674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139674 prefixEnd_1139674 := by exact prefixLift 1139674
  have htrace : WordTrace (prefixWord ++ tailWord_1139674) baseStart_1139674 baseEnd_1139674 := by
    simpa [prefixWord, tailWord_1139674, baseEnd_1139674] using wordTrace_append hprefix tailTrace_1139674
  have hstable : (prefixWord ++ tailWord_1139674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139674).length < 2 ^ (prefixWord ++ tailWord_1139674).sum := by decide
  have hdescent : baseEnd_1139674 < baseStart_1139674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139697 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_1139697 : Nat := 118140960795 + 1139697 * 2 ^ 59
def prefixEnd_1139697 : Nat := 4983230072969 + 3 ^ 40 * 1139697 * 2
def baseEnd_1139697 : Nat := 585212361487332663946135

theorem tailTrace_1139697 : CollatzResearch.WordTrace tailWord_1139697 prefixEnd_1139697 585212361487332663946135 := by
  unfold tailWord_1139697
  simp only [CollatzResearch.WordTrace]
  refine ⟨41568164552079888596249345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27712109701386592397499563 41568164552079888596249345)
  ·
    refine ⟨31176123414059916447187009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41568164552079888596249345 31176123414059916447187009)
    ·
      refine ⟨23382092560544937335390257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31176123414059916447187009 23382092560544937335390257)
      ·
        refine ⟨17536569420408703001542693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23382092560544937335390257 17536569420408703001542693)
        ·
          refine ⟨3288106766326631812789255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17536569420408703001542693 3288106766326631812789255)
          ·
            refine ⟨4932160149489947719183883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288106766326631812789255 4932160149489947719183883)
            ·
              refine ⟨7398240224234921578775825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4932160149489947719183883 7398240224234921578775825)
              ·
                refine ⟨5548680168176191184081869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7398240224234921578775825 5548680168176191184081869)
                ·
                  refine ⟨2080755063066071694030701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5548680168176191184081869 2080755063066071694030701)
                  ·
                    refine ⟨780283148649776885261513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2080755063066071694030701 780283148649776885261513)
                    ·
                      refine ⟨585212361487332663946135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780283148649776885261513 585212361487332663946135)
                      ·
                        rfl

theorem cell23_1139697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_1139697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139697 prefixEnd_1139697 := by exact prefixLift 1139697
  have htrace : WordTrace (prefixWord ++ tailWord_1139697) baseStart_1139697 baseEnd_1139697 := by
    simpa [prefixWord, tailWord_1139697, baseEnd_1139697] using wordTrace_append hprefix tailTrace_1139697
  have hstable : (prefixWord ++ tailWord_1139697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139697).length < 2 ^ (prefixWord ++ tailWord_1139697).sum := by decide
  have hdescent : baseEnd_1139697 < baseStart_1139697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139760 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_1139760 : Nat := 118140960795 + 1139760 * 2 ^ 59
def prefixEnd_1139760 : Nat := 4983230072969 + 3 ^ 40 * 1139760 * 2
def baseEnd_1139760 : Nat := 585244710768565917458345

theorem tailTrace_1139760 : CollatzResearch.WordTrace tailWord_1139760 prefixEnd_1139760 585244710768565917458345 := by
  unfold tailWord_1139760
  simp only [CollatzResearch.WordTrace]
  refine ⟨20785231175425825177896367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27713641567234433570528489 20785231175425825177896367)
  ·
    refine ⟨31177846763138737766844551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20785231175425825177896367 31177846763138737766844551)
    ·
      refine ⟨46766770144708106650266827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31177846763138737766844551 46766770144708106650266827)
      ·
        refine ⟨70150155217062159975400241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46766770144708106650266827 70150155217062159975400241)
        ·
          refine ⟨52612616412796619981550181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70150155217062159975400241 52612616412796619981550181)
          ·
            refine ⟨9864865577399366246540659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52612616412796619981550181 9864865577399366246540659)
            ·
              refine ⟨14797298366099049369810989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9864865577399366246540659 14797298366099049369810989)
              ·
                refine ⟨5548986887287143513679121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14797298366099049369810989 5548986887287143513679121)
                ·
                  refine ⟨4161740165465357635259341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5548986887287143513679121 4161740165465357635259341)
                  ·
                    refine ⟨1560652562049509113222253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4161740165465357635259341 1560652562049509113222253)
                    ·
                      refine ⟨585244710768565917458345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560652562049509113222253 585244710768565917458345)
                      ·
                        rfl

theorem cell23_1139760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_1139760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139760 prefixEnd_1139760 := by exact prefixLift 1139760
  have htrace : WordTrace (prefixWord ++ tailWord_1139760) baseStart_1139760 baseEnd_1139760 := by
    simpa [prefixWord, tailWord_1139760, baseEnd_1139760] using wordTrace_append hprefix tailTrace_1139760
  have hstable : (prefixWord ++ tailWord_1139760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139760).length < 2 ^ (prefixWord ++ tailWord_1139760).sum := by decide
  have hdescent : baseEnd_1139760 < baseStart_1139760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139761 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_1139761 : Nat := 118140960795 + 1139761 * 2 ^ 59
def prefixEnd_1139761 : Nat := 4983230072969 + 3 ^ 40 * 1139761 * 2
def baseEnd_1139761 : Nat := 585245224249220413545841

theorem tailTrace_1139761 : CollatzResearch.WordTrace tailWord_1139761 prefixEnd_1139761 585245224249220413545841 := by
  unfold tailWord_1139761
  simp only [CollatzResearch.WordTrace]
  refine ⟨41570498823848027526579137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27713665882565351684386091 41570498823848027526579137)
  ·
    refine ⟨31177874117886020644934353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41570498823848027526579137 31177874117886020644934353)
    ·
      refine ⟨23383405588414515483700765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31177874117886020644934353 23383405588414515483700765)
      ·
        refine ⟨8768777095655443306387787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23383405588414515483700765 8768777095655443306387787)
        ·
          refine ⟨13153165643483164959581681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8768777095655443306387787 13153165643483164959581681)
          ·
            refine ⟨9864874232612373719686261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13153165643483164959581681 9864874232612373719686261)
            ·
              refine ⟨924831959307410036220587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9864874232612373719686261 924831959307410036220587)
              ·
                refine ⟨1387247938961115054330881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924831959307410036220587 1387247938961115054330881)
                ·
                  refine ⟨1040435954220836290748161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1387247938961115054330881 1040435954220836290748161)
                  ·
                    refine ⟨780326965665627218061121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1040435954220836290748161 780326965665627218061121)
                    ·
                      refine ⟨585245224249220413545841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780326965665627218061121 585245224249220413545841)
                      ·
                        rfl

theorem cell23_1139761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_1139761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139761 prefixEnd_1139761 := by exact prefixLift 1139761
  have htrace : WordTrace (prefixWord ++ tailWord_1139761) baseStart_1139761 baseEnd_1139761 := by
    simpa [prefixWord, tailWord_1139761, baseEnd_1139761] using wordTrace_append hprefix tailTrace_1139761
  have hstable : (prefixWord ++ tailWord_1139761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139761).length < 2 ^ (prefixWord ++ tailWord_1139761).sum := by decide
  have hdescent : baseEnd_1139761 < baseStart_1139761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139790 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1139790 : Nat := 118140960795 + 1139790 * 2 ^ 59
def prefixEnd_1139790 : Nat := 4983230072969 + 3 ^ 40 * 1139790 * 2
def baseEnd_1139790 : Nat := 585260115188200800083207

theorem tailTrace_1139790 : CollatzResearch.WordTrace tailWord_1139790 prefixEnd_1139790 585260115188200800083207 := by
  unfold tailWord_1139790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196444567592870684923103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27714371027161976986256549 5196444567592870684923103)
  ·
    refine ⟨7794666851389306027384655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196444567592870684923103 7794666851389306027384655)
    ·
      refine ⟨11692000277083959041076983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7794666851389306027384655 11692000277083959041076983)
      ·
        refine ⟨17538000415625938561615475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11692000277083959041076983 17538000415625938561615475)
        ·
          refine ⟨26307000623438907842423213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17538000415625938561615475 26307000623438907842423213)
          ·
            refine ⟨9865125233789590440908705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26307000623438907842423213 9865125233789590440908705)
            ·
              refine ⟨7398843925342192830681529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9865125233789590440908705 7398843925342192830681529)
              ·
                refine ⟨5549132944006644623011147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7398843925342192830681529 5549132944006644623011147)
                ·
                  refine ⟨8323699416009966934516721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549132944006644623011147 8323699416009966934516721)
                  ·
                    refine ⟨6242774562007475200887541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8323699416009966934516721 6242774562007475200887541)
                    ·
                      refine ⟨585260115188200800083207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6242774562007475200887541 585260115188200800083207)
                      ·
                        rfl

theorem cell23_1139790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1139790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139790 prefixEnd_1139790 := by exact prefixLift 1139790
  have htrace : WordTrace (prefixWord ++ tailWord_1139790) baseStart_1139790 baseEnd_1139790 := by
    simpa [prefixWord, tailWord_1139790, baseEnd_1139790] using wordTrace_append hprefix tailTrace_1139790
  have hstable : (prefixWord ++ tailWord_1139790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139790).length < 2 ^ (prefixWord ++ tailWord_1139790).sum := by decide
  have hdescent : baseEnd_1139790 < baseStart_1139790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139854 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1139854 : Nat := 118140960795 + 1139854 * 2 ^ 59
def prefixEnd_1139854 : Nat := 4983230072969 + 3 ^ 40 * 1139854 * 2
def baseEnd_1139854 : Nat := 585292977950088549682913

theorem tailTrace_1139854 : CollatzResearch.WordTrace tailWord_1139854 prefixEnd_1139854 585292977950088549682913 := by
  unfold tailWord_1139854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196736351563888051214327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27715927208340736273143077 5196736351563888051214327)
  ·
    refine ⟨7795104527345832076821491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5196736351563888051214327 7795104527345832076821491)
    ·
      refine ⟨11692656791018748115232237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7795104527345832076821491 11692656791018748115232237)
      ·
        refine ⟨4384746296632030543212089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11692656791018748115232237 4384746296632030543212089)
        ·
          refine ⟨3288559722474022907409067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384746296632030543212089 3288559722474022907409067)
          ·
            refine ⟨4932839583711034361113601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3288559722474022907409067 4932839583711034361113601)
            ·
              refine ⟨3699629687783275770835201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4932839583711034361113601 3699629687783275770835201)
              ·
                refine ⟨2774722265837456828126401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3699629687783275770835201 2774722265837456828126401)
                ·
                  refine ⟨2081041699378092621094801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2774722265837456828126401 2081041699378092621094801)
                  ·
                    refine ⟨1560781274533569465821101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081041699378092621094801 1560781274533569465821101)
                    ·
                      refine ⟨585292977950088549682913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560781274533569465821101 585292977950088549682913)
                      ·
                        rfl

theorem cell23_1139854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1139854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139854 prefixEnd_1139854 := by exact prefixLift 1139854
  have htrace : WordTrace (prefixWord ++ tailWord_1139854) baseStart_1139854 baseEnd_1139854 := by
    simpa [prefixWord, tailWord_1139854, baseEnd_1139854] using wordTrace_append hprefix tailTrace_1139854
  have hstable : (prefixWord ++ tailWord_1139854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139854).length < 2 ^ (prefixWord ++ tailWord_1139854).sum := by decide
  have hdescent : baseEnd_1139854 < baseStart_1139854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139901 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_1139901 : Nat := 118140960795 + 1139901 * 2 ^ 59
def prefixEnd_1139901 : Nat := 4983230072969 + 3 ^ 40 * 1139901 * 2
def baseEnd_1139901 : Nat := 585317111540849865795197

theorem tailTrace_1139901 : CollatzResearch.WordTrace tailWord_1139901 prefixEnd_1139901 585317111540849865795197 := by
  unfold tailWord_1139901
  simp only [CollatzResearch.WordTrace]
  refine ⟨41575605043340831436675557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27717070028893887624450371 41575605043340831436675557)
  ·
    refine ⟨7795425945626405894376667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41575605043340831436675557 7795425945626405894376667)
    ·
      refine ⟨11693138918439608841565001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7795425945626405894376667 11693138918439608841565001)
      ·
        refine ⟨8769854188829706631173751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11693138918439608841565001 8769854188829706631173751)
        ·
          refine ⟨13154781283244559946760627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8769854188829706631173751 13154781283244559946760627)
          ·
            refine ⟨19732171924866839920140941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13154781283244559946760627 19732171924866839920140941)
            ·
              refine ⟨7399564471825064970052853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19732171924866839920140941 7399564471825064970052853)
              ·
                refine ⟨693709169233599840942455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7399564471825064970052853 693709169233599840942455)
                ·
                  refine ⟨1040563753850399761413683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693709169233599840942455 1040563753850399761413683)
                  ·
                    refine ⟨1560845630775599642120525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040563753850399761413683 1560845630775599642120525)
                    ·
                      refine ⟨585317111540849865795197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560845630775599642120525 585317111540849865795197)
                      ·
                        rfl

theorem cell23_1139901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_1139901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139901 prefixEnd_1139901 := by exact prefixLift 1139901
  have htrace : WordTrace (prefixWord ++ tailWord_1139901) baseStart_1139901 baseEnd_1139901 := by
    simpa [prefixWord, tailWord_1139901, baseEnd_1139901] using wordTrace_append hprefix tailTrace_1139901
  have hstable : (prefixWord ++ tailWord_1139901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139901).length < 2 ^ (prefixWord ++ tailWord_1139901).sum := by decide
  have hdescent : baseEnd_1139901 < baseStart_1139901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139904 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_1139904 : Nat := 118140960795 + 1139904 * 2 ^ 59
def prefixEnd_1139904 : Nat := 4983230072969 + 3 ^ 40 * 1139904 * 2
def baseEnd_1139904 : Nat := 195106217327604451352561

theorem tailTrace_1139904 : CollatzResearch.WordTrace tailWord_1139904 prefixEnd_1139904 195106217327604451352561 := by
  unfold tailWord_1139904
  simp only [CollatzResearch.WordTrace]
  refine ⟨20787857231164981474517383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27717142974886641966023177 20787857231164981474517383)
  ·
    refine ⟨31181785846747472211776075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20787857231164981474517383 31181785846747472211776075)
    ·
      refine ⟨46772678770121208317664113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31181785846747472211776075 46772678770121208317664113)
      ·
        refine ⟨35079509077590906238248085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46772678770121208317664113 35079509077590906238248085)
        ·
          refine ⟨1644351988012073729917879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35079509077590906238248085 1644351988012073729917879)
          ·
            refine ⟨2466527982018110594876819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644351988012073729917879 2466527982018110594876819)
            ·
              refine ⟨3699791973027165892315229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466527982018110594876819 3699791973027165892315229)
              ·
                refine ⟨1387421989885187209618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3699791973027165892315229 1387421989885187209618211)
                ·
                  refine ⟨2081132984827780814427317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387421989885187209618211 2081132984827780814427317)
                  ·
                    refine ⟨195106217327604451352561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2081132984827780814427317 195106217327604451352561)
                    ·
                      rfl

theorem cell23_1139904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_1139904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139904 prefixEnd_1139904 := by exact prefixLift 1139904
  have htrace : WordTrace (prefixWord ++ tailWord_1139904) baseStart_1139904 baseEnd_1139904 := by
    simpa [prefixWord, tailWord_1139904, baseEnd_1139904] using wordTrace_append hprefix tailTrace_1139904
  have hstable : (prefixWord ++ tailWord_1139904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139904).length < 2 ^ (prefixWord ++ tailWord_1139904).sum := by decide
  have hdescent : baseEnd_1139904 < baseStart_1139904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139920 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_1139920 : Nat := 118140960795 + 1139920 * 2 ^ 59
def prefixEnd_1139920 : Nat := 4983230072969 + 3 ^ 40 * 1139920 * 2
def baseEnd_1139920 : Nat := 585326867673285291457609

theorem tailTrace_1139920 : CollatzResearch.WordTrace tailWord_1139920 prefixEnd_1139920 585326867673285291457609 := by
  unfold tailWord_1139920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788149015135998840808607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27717532020181331787744809 20788149015135998840808607)
  ·
    refine ⟨31182223522703998261212911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20788149015135998840808607 31182223522703998261212911)
    ·
      refine ⟨46773335284055997391819367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31182223522703998261212911 46773335284055997391819367)
      ·
        refine ⟨70160002926083996087729051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46773335284055997391819367 70160002926083996087729051)
        ·
          refine ⟨105240004389125994131593577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70160002926083996087729051 105240004389125994131593577)
          ·
            refine ⟨78930003291844495598695183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105240004389125994131593577 78930003291844495598695183)
            ·
              refine ⟨118395004937766743398042775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78930003291844495598695183 118395004937766743398042775)
              ·
                refine ⟨177592507406650115097064163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118395004937766743398042775 177592507406650115097064163)
                ·
                  refine ⟨266388761109975172645596245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177592507406650115097064163 266388761109975172645596245)
                  ·
                    refine ⟨3121743294257521554440581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 266388761109975172645596245 3121743294257521554440581)
                    ·
                      refine ⟨585326867673285291457609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3121743294257521554440581 585326867673285291457609)
                      ·
                        rfl

theorem cell23_1139920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_1139920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139920 prefixEnd_1139920 := by exact prefixLift 1139920
  have htrace : WordTrace (prefixWord ++ tailWord_1139920) baseStart_1139920 baseEnd_1139920 := by
    simpa [prefixWord, tailWord_1139920, baseEnd_1139920] using wordTrace_append hprefix tailTrace_1139920
  have hstable : (prefixWord ++ tailWord_1139920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139920).length < 2 ^ (prefixWord ++ tailWord_1139920).sum := by decide
  have hdescent : baseEnd_1139920 < baseStart_1139920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139927 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1139927 : Nat := 118140960795 + 1139927 * 2 ^ 59
def prefixEnd_1139927 : Nat := 4983230072969 + 3 ^ 40 * 1139927 * 2
def baseEnd_1139927 : Nat := 585330462037866764070077

theorem tailTrace_1139927 : CollatzResearch.WordTrace tailWord_1139927 prefixEnd_1139927 585330462037866764070077 := by
  unfold tailWord_1139927
  simp only [CollatzResearch.WordTrace]
  refine ⟨41576553341246637877122035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27717702227497758584748023 41576553341246637877122035)
  ·
    refine ⟨62364830011869956815683053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41576553341246637877122035 62364830011869956815683053)
    ·
      refine ⟨23386811254451233805881145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62364830011869956815683053 23386811254451233805881145)
      ·
        refine ⟨17540108440838425354410859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23386811254451233805881145 17540108440838425354410859)
        ·
          refine ⟨26310162661257638031616289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17540108440838425354410859 26310162661257638031616289)
          ·
            refine ⟨19732621995943228523712217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26310162661257638031616289 19732621995943228523712217)
            ·
              refine ⟨14799466496957421392784163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19732621995943228523712217 14799466496957421392784163)
              ·
                refine ⟨22199199745436132089176245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14799466496957421392784163 22199199745436132089176245)
                ·
                  refine ⟨2081174976134637383360273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22199199745436132089176245 2081174976134637383360273)
                  ·
                    refine ⟨1560881232100978037520205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2081174976134637383360273 1560881232100978037520205)
                    ·
                      refine ⟨585330462037866764070077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560881232100978037520205 585330462037866764070077)
                      ·
                        rfl

theorem cell23_1139927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1139927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139927 prefixEnd_1139927 := by exact prefixLift 1139927
  have htrace : WordTrace (prefixWord ++ tailWord_1139927) baseStart_1139927 baseEnd_1139927 := by
    simpa [prefixWord, tailWord_1139927, baseEnd_1139927] using wordTrace_append hprefix tailTrace_1139927
  have hstable : (prefixWord ++ tailWord_1139927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139927).length < 2 ^ (prefixWord ++ tailWord_1139927).sum := by decide
  have hdescent : baseEnd_1139927 < baseStart_1139927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139930 : List Nat := [3, 1, 1, 2, 2, 1, 1, 12]
def baseStart_1139930 : Nat := 118140960795 + 1139930 * 2 ^ 59
def prefixEnd_1139930 : Nat := 4983230072969 + 3 ^ 40 * 1139930 * 2
def baseEnd_1139930 : Nat := 21678963054808527864169

theorem tailTrace_1139930 : CollatzResearch.WordTrace tailWord_1139930 prefixEnd_1139930 21678963054808527864169 := by
  unfold tailWord_1139930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10394165690058942347370311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27717775173490512926320829 10394165690058942347370311)
  ·
    refine ⟨15591248535088413521055467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10394165690058942347370311 15591248535088413521055467)
    ·
      refine ⟨23386872802632620281583201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591248535088413521055467 23386872802632620281583201)
      ·
        refine ⟨17540154601974465211187401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23386872802632620281583201 17540154601974465211187401)
        ·
          refine ⟨13155115951480848908390551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17540154601974465211187401 13155115951480848908390551)
          ·
            refine ⟨19732673927221273362585827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13155115951480848908390551 19732673927221273362585827)
            ·
              refine ⟨29599010890831910043878741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19732673927221273362585827 29599010890831910043878741)
              ·
                refine ⟨21678963054808527864169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 29599010890831910043878741 21678963054808527864169)
                ·
                  rfl

theorem cell23_1139930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_1139930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139930 prefixEnd_1139930 := by exact prefixLift 1139930
  have htrace : WordTrace (prefixWord ++ tailWord_1139930) baseStart_1139930 baseEnd_1139930 := by
    simpa [prefixWord, tailWord_1139930, baseEnd_1139930] using wordTrace_append hprefix tailTrace_1139930
  have hstable : (prefixWord ++ tailWord_1139930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139930).length < 2 ^ (prefixWord ++ tailWord_1139930).sum := by decide
  have hdescent : baseEnd_1139930 < baseStart_1139930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139937 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1139937 : Nat := 118140960795 + 1139937 * 2 ^ 59
def prefixEnd_1139937 : Nat := 4983230072969 + 3 ^ 40 * 1139937 * 2
def baseEnd_1139937 : Nat := 585335596844411724945031

theorem tailTrace_1139937 : CollatzResearch.WordTrace tailWord_1139937 prefixEnd_1139937 585335596844411724945031 := by
  unfold tailWord_1139937
  simp only [CollatzResearch.WordTrace]
  refine ⟨41576918071210409584986065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27717945380806939723324043 41576918071210409584986065)
  ·
    refine ⟨31182688553407807188739549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41576918071210409584986065 31182688553407807188739549)
    ·
      refine ⟨11693508207527927695777331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31182688553407807188739549 11693508207527927695777331)
      ·
        refine ⟨17540262311291891543665997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693508207527927695777331 17540262311291891543665997)
        ·
          refine ⟨6577598366734459328874749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17540262311291891543665997 6577598366734459328874749)
          ·
            refine ⟨2466599387525422248328031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6577598366734459328874749 2466599387525422248328031)
            ·
              refine ⟨3699899081288133372492047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466599387525422248328031 3699899081288133372492047)
              ·
                refine ⟨5549848621932200058738071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3699899081288133372492047 5549848621932200058738071)
                ·
                  refine ⟨8324772932898300088107107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5549848621932200058738071 8324772932898300088107107)
                  ·
                    refine ⟨12487159399347450132160661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8324772932898300088107107 12487159399347450132160661)
                    ·
                      refine ⟨585335596844411724945031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12487159399347450132160661 585335596844411724945031)
                      ·
                        rfl

theorem cell23_1139937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1139937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139937 prefixEnd_1139937 := by exact prefixLift 1139937
  have htrace : WordTrace (prefixWord ++ tailWord_1139937) baseStart_1139937 baseEnd_1139937 := by
    simpa [prefixWord, tailWord_1139937, baseEnd_1139937] using wordTrace_append hprefix tailTrace_1139937
  have hstable : (prefixWord ++ tailWord_1139937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139937).length < 2 ^ (prefixWord ++ tailWord_1139937).sum := by decide
  have hdescent : baseEnd_1139937 < baseStart_1139937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139941 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1139941 : Nat := 118140960795 + 1139941 * 2 ^ 59
def prefixEnd_1139941 : Nat := 4983230072969 + 3 ^ 40 * 1139941 * 2
def baseEnd_1139941 : Nat := 585337650767029709295013

theorem tailTrace_1139941 : CollatzResearch.WordTrace tailWord_1139941 prefixEnd_1139941 585337650767029709295013 := by
  unfold tailWord_1139941
  simp only [CollatzResearch.WordTrace]
  refine ⟨41577063963195918268131677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27718042642130612178754451 41577063963195918268131677)
  ·
    refine ⟨15591398986198469350549379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41577063963195918268131677 15591398986198469350549379)
    ·
      refine ⟨23387098479297704025824069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15591398986198469350549379 23387098479297704025824069)
      ·
        refine ⟨4385080964868319504842013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23387098479297704025824069 4385080964868319504842013)
        ·
          refine ⟨1644405361825619814315755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4385080964868319504842013 1644405361825619814315755)
          ·
            refine ⟨2466608042738429721473633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644405361825619814315755 2466608042738429721473633)
            ·
              refine ⟨1849956032053822291105225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2466608042738429721473633 1849956032053822291105225)
              ·
                refine ⟨1387467024040366718328919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849956032053822291105225 1387467024040366718328919)
                ·
                  refine ⟨2081200536060550077493379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387467024040366718328919 2081200536060550077493379)
                  ·
                    refine ⟨3121800804090825116240069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2081200536060550077493379 3121800804090825116240069)
                    ·
                      refine ⟨585337650767029709295013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3121800804090825116240069 585337650767029709295013)
                      ·
                        rfl

theorem cell23_1139941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1139941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139941 prefixEnd_1139941 := by exact prefixLift 1139941
  have htrace : WordTrace (prefixWord ++ tailWord_1139941) baseStart_1139941 baseEnd_1139941 := by
    simpa [prefixWord, tailWord_1139941, baseEnd_1139941] using wordTrace_append hprefix tailTrace_1139941
  have hstable : (prefixWord ++ tailWord_1139941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139941).length < 2 ^ (prefixWord ++ tailWord_1139941).sum := by decide
  have hdescent : baseEnd_1139941 < baseStart_1139941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139947 : List Nat := [1, 1, 1, 1, 2, 6, 4, 7]
def baseStart_1139947 : Nat := 118140960795 + 1139947 * 2 ^ 59
def prefixEnd_1139947 : Nat := 4983230072969 + 3 ^ 40 * 1139947 * 2
def baseEnd_1139947 : Nat := 21679286357442840215555

theorem tailTrace_1139947 : CollatzResearch.WordTrace tailWord_1139947 prefixEnd_1139947 21679286357442840215555 := by
  unfold tailWord_1139947
  simp only [CollatzResearch.WordTrace]
  refine ⟨41577282801174181292850095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27718188534116120861900063 41577282801174181292850095)
  ·
    refine ⟨62365924201761271939275143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41577282801174181292850095 62365924201761271939275143)
    ·
      refine ⟨93548886302641907908912715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62365924201761271939275143 93548886302641907908912715)
      ·
        refine ⟨140323329453962861863369073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93548886302641907908912715 140323329453962861863369073)
        ·
          refine ⟨105242497090472146397526805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140323329453962861863369073 105242497090472146397526805)
          ·
            refine ⟨4933242051115881862384069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105242497090472146397526805 4933242051115881862384069)
            ·
              refine ⟨924982884584227849197013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4933242051115881862384069 924982884584227849197013)
              ·
                refine ⟨21679286357442840215555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 924982884584227849197013 21679286357442840215555)
                ·
                  rfl

theorem cell23_1139947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 7].length) (baseStart_1139947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139947 prefixEnd_1139947 := by exact prefixLift 1139947
  have htrace : WordTrace (prefixWord ++ tailWord_1139947) baseStart_1139947 baseEnd_1139947 := by
    simpa [prefixWord, tailWord_1139947, baseEnd_1139947] using wordTrace_append hprefix tailTrace_1139947
  have hstable : (prefixWord ++ tailWord_1139947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139947).length < 2 ^ (prefixWord ++ tailWord_1139947).sum := by decide
  have hdescent : baseEnd_1139947 < baseStart_1139947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139960 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1139960 : Nat := 118140960795 + 1139960 * 2 ^ 59
def prefixEnd_1139960 : Nat := 4983230072969 + 3 ^ 40 * 1139960 * 2
def baseEnd_1139960 : Nat := 195115802299821711652475

theorem tailTrace_1139960 : CollatzResearch.WordTrace tailWord_1139960 prefixEnd_1139960 195115802299821711652475 := by
  unfold tailWord_1139960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788878475063542256536667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27718504633418056342048889 20788878475063542256536667)
  ·
    refine ⟨31183317712595313384805001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20788878475063542256536667 31183317712595313384805001)
    ·
      refine ⟨23387488284446485038603751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31183317712595313384805001 23387488284446485038603751)
      ·
        refine ⟨35081232426669727557905627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23387488284446485038603751 35081232426669727557905627)
        ·
          refine ⟨52621848640004591336858441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35081232426669727557905627 52621848640004591336858441)
          ·
            refine ⟨39466386480003443502643831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52621848640004591336858441 39466386480003443502643831)
            ·
              refine ⟨59199579720005165253965747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39466386480003443502643831 59199579720005165253965747)
              ·
                refine ⟨88799369580007747880948621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59199579720005165253965747 88799369580007747880948621)
                ·
                  refine ⟨33299763592502905455355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88799369580007747880948621 33299763592502905455355733)
                  ·
                    refine ⟨195115802299821711652475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 33299763592502905455355733 195115802299821711652475)
                    ·
                      rfl

theorem cell23_1139960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1139960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139960 prefixEnd_1139960 := by exact prefixLift 1139960
  have htrace : WordTrace (prefixWord ++ tailWord_1139960) baseStart_1139960 baseEnd_1139960 := by
    simpa [prefixWord, tailWord_1139960, baseEnd_1139960] using wordTrace_append hprefix tailTrace_1139960
  have hstable : (prefixWord ++ tailWord_1139960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139960).length < 2 ^ (prefixWord ++ tailWord_1139960).sum := by decide
  have hdescent : baseEnd_1139960 < baseStart_1139960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139964 : List Nat := [2, 2, 2, 1, 6, 1, 9]
def baseStart_1139964 : Nat := 118140960795 + 1139964 * 2 ^ 59
def prefixEnd_1139964 : Nat := 4983230072969 + 3 ^ 40 * 1139964 * 2
def baseEnd_1139964 : Nat := 7226536553359050855647

theorem tailTrace_1139964 : CollatzResearch.WordTrace tailWord_1139964 prefixEnd_1139964 7226536553359050855647 := by
  unfold tailWord_1139964
  simp only [CollatzResearch.WordTrace]
  refine ⟨20788951421056296598109473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27718601894741728797479297 20788951421056296598109473)
  ·
    refine ⟨15591713565792222448582105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20788951421056296598109473 15591713565792222448582105)
    ·
      refine ⟨11693785174344166836436579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15591713565792222448582105 11693785174344166836436579)
      ·
        refine ⟨17540677761516250254654869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11693785174344166836436579 17540677761516250254654869)
        ·
          refine ⟨822219270071074230686947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17540677761516250254654869 822219270071074230686947)
          ·
            refine ⟨1233328905106611346030421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822219270071074230686947 1233328905106611346030421)
            ·
              refine ⟨7226536553359050855647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1233328905106611346030421 7226536553359050855647)
              ·
                rfl

theorem cell23_1139964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 9].length) (baseStart_1139964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139964 prefixEnd_1139964 := by exact prefixLift 1139964
  have htrace : WordTrace (prefixWord ++ tailWord_1139964) baseStart_1139964 baseEnd_1139964 := by
    simpa [prefixWord, tailWord_1139964, baseEnd_1139964] using wordTrace_append hprefix tailTrace_1139964
  have hstable : (prefixWord ++ tailWord_1139964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139964).length < 2 ^ (prefixWord ++ tailWord_1139964).sum := by decide
  have hdescent : baseEnd_1139964 < baseStart_1139964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139991 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1139991 : Nat := 118140960795 + 1139991 * 2 ^ 59
def prefixEnd_1139991 : Nat := 4983230072969 + 3 ^ 40 * 1139991 * 2
def baseEnd_1139991 : Nat := 585363324799754513669783

theorem tailTrace_1139991 : CollatzResearch.WordTrace tailWord_1139991 prefixEnd_1139991 585363324799754513669783 := by
  unfold tailWord_1139991
  simp only [CollatzResearch.WordTrace]
  refine ⟨41578887613014776807451827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27719258408676517871634551 41578887613014776807451827)
  ·
    refine ⟨62368331419522165211177741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41578887613014776807451827 62368331419522165211177741)
    ·
      refine ⟨23388124282320811954191653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62368331419522165211177741 23388124282320811954191653)
      ·
        refine ⟨4385273302935152241410935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23388124282320811954191653 4385273302935152241410935)
        ·
          refine ⟨6577909954402728362116403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385273302935152241410935 6577909954402728362116403)
          ·
            refine ⟨9866864931604092543174605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6577909954402728362116403 9866864931604092543174605)
            ·
              refine ⟨3700074349351534703690477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9866864931604092543174605 3700074349351534703690477)
              ·
                refine ⟨1387527881006825513883929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3700074349351534703690477 1387527881006825513883929)
                ·
                  refine ⟨1040645910755119135412947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1387527881006825513883929 1040645910755119135412947)
                  ·
                    refine ⟨1560968866132678703119421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040645910755119135412947 1560968866132678703119421)
                    ·
                      refine ⟨585363324799754513669783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1560968866132678703119421 585363324799754513669783)
                      ·
                        rfl

theorem cell23_1139991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1139991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1139991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1139991 prefixEnd_1139991 := by exact prefixLift 1139991
  have htrace : WordTrace (prefixWord ++ tailWord_1139991) baseStart_1139991 baseEnd_1139991 := by
    simpa [prefixWord, tailWord_1139991, baseEnd_1139991] using wordTrace_append hprefix tailTrace_1139991
  have hstable : (prefixWord ++ tailWord_1139991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139991).length < 2 ^ (prefixWord ++ tailWord_1139991).sum := by decide
  have hdescent : baseEnd_1139991 < baseStart_1139991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140044 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1140044 : Nat := 118140960795 + 1140044 * 2 ^ 59
def prefixEnd_1140044 : Nat := 4983230072969 + 3 ^ 40 * 1140044 * 2
def baseEnd_1140044 : Nat := 585390539274442806307039

theorem tailTrace_1140044 : CollatzResearch.WordTrace tailWord_1140044 prefixEnd_1140044 585390539274442806307039 := by
  unfold tailWord_1140044
  simp only [CollatzResearch.WordTrace]
  refine ⟨20790410340911383429565593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27720547121215177906087457 20790410340911383429565593)
  ·
    refine ⟨15592807755683537572174195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20790410340911383429565593 15592807755683537572174195)
    ·
      refine ⟨23389211633525306358261293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15592807755683537572174195 23389211633525306358261293)
      ·
        refine ⟨8770954362571989884347985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23389211633525306358261293 8770954362571989884347985)
        ·
          refine ⟨6578215771928992413260989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8770954362571989884347985 6578215771928992413260989)
          ·
            refine ⟨2466830914473372154972871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6578215771928992413260989 2466830914473372154972871)
            ·
              refine ⟨3700246371710058232459307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466830914473372154972871 3700246371710058232459307)
              ·
                refine ⟨5550369557565087348688961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700246371710058232459307 5550369557565087348688961)
                ·
                  refine ⟨4162777168173815511516721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550369557565087348688961 4162777168173815511516721)
                  ·
                    refine ⟨3122082876130361633637541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4162777168173815511516721 3122082876130361633637541)
                    ·
                      refine ⟨585390539274442806307039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3122082876130361633637541 585390539274442806307039)
                      ·
                        rfl

theorem cell23_1140044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1140044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140044 prefixEnd_1140044 := by exact prefixLift 1140044
  have htrace : WordTrace (prefixWord ++ tailWord_1140044) baseStart_1140044 baseEnd_1140044 := by
    simpa [prefixWord, tailWord_1140044, baseEnd_1140044] using wordTrace_append hprefix tailTrace_1140044
  have hstable : (prefixWord ++ tailWord_1140044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140044).length < 2 ^ (prefixWord ++ tailWord_1140044).sum := by decide
  have hdescent : baseEnd_1140044 < baseStart_1140044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140098 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1140098 : Nat := 118140960795 + 1140098 * 2 ^ 59
def prefixEnd_1140098 : Nat := 4983230072969 + 3 ^ 40 * 1140098 * 2
def baseEnd_1140098 : Nat := 585418267229785595031791

theorem tailTrace_1140098 : CollatzResearch.WordTrace tailWord_1140098 prefixEnd_1140098 585418267229785595031791 := by
  unfold tailWord_1140098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395697555906783520399237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27721860149084756054397965 10395697555906783520399237)
  ·
    refine ⟨1949193291732521910074857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10395697555906783520399237 1949193291732521910074857)
    ·
      refine ⟨1461894968799391432556143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1949193291732521910074857 1461894968799391432556143)
      ·
        refine ⟨2192842453199087148834215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461894968799391432556143 2192842453199087148834215)
        ·
          refine ⟨3289263679798630723251323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192842453199087148834215 3289263679798630723251323)
          ·
            refine ⟨4933895519697946084876985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3289263679798630723251323 4933895519697946084876985)
            ·
              refine ⟨3700421639773459563657739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4933895519697946084876985 3700421639773459563657739)
              ·
                refine ⟨5550632459660189345486609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3700421639773459563657739 5550632459660189345486609)
                ·
                  refine ⟨4162974344745142009114957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5550632459660189345486609 4162974344745142009114957)
                  ·
                    refine ⟨1561115379279428253418109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4162974344745142009114957 1561115379279428253418109)
                    ·
                      refine ⟨585418267229785595031791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561115379279428253418109 585418267229785595031791)
                      ·
                        rfl

theorem cell23_1140098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1140098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140098 prefixEnd_1140098 := by exact prefixLift 1140098
  have htrace : WordTrace (prefixWord ++ tailWord_1140098) baseStart_1140098 baseEnd_1140098 := by
    simpa [prefixWord, tailWord_1140098, baseEnd_1140098] using wordTrace_append hprefix tailTrace_1140098
  have hstable : (prefixWord ++ tailWord_1140098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140098).length < 2 ^ (prefixWord ++ tailWord_1140098).sum := by decide
  have hdescent : baseEnd_1140098 < baseStart_1140098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140104 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1140104 : Nat := 118140960795 + 1140104 * 2 ^ 59
def prefixEnd_1140104 : Nat := 4983230072969 + 3 ^ 40 * 1140104 * 2
def baseEnd_1140104 : Nat := 585421348113712571556763

theorem tailTrace_1140104 : CollatzResearch.WordTrace tailWord_1140104 prefixEnd_1140104 585421348113712571556763 := by
  unfold tailWord_1140104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20791504530802698553157683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27722006041070264737543577 20791504530802698553157683)
  ·
    refine ⟨31187256796204047829736525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20791504530802698553157683 31187256796204047829736525)
    ·
      refine ⟨11695221298576517936151197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31187256796204047829736525 11695221298576517936151197)
      ·
        refine ⟨4385707986966194226056699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11695221298576517936151197 4385707986966194226056699)
        ·
          refine ⟨6578561980449291339085049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4385707986966194226056699 6578561980449291339085049)
          ·
            refine ⟨4933921485336968504313787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6578561980449291339085049 4933921485336968504313787)
            ·
              refine ⟨7400882228005452756470681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4933921485336968504313787 7400882228005452756470681)
              ·
                refine ⟨5550661671004089567353011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7400882228005452756470681 5550661671004089567353011)
                ·
                  refine ⟨8325992506506134351029517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5550661671004089567353011 8325992506506134351029517)
                  ·
                    refine ⟨3122247189939800381636069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8325992506506134351029517 3122247189939800381636069)
                    ·
                      refine ⟨585421348113712571556763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3122247189939800381636069 585421348113712571556763)
                      ·
                        rfl

theorem cell23_1140104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1140104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140104 prefixEnd_1140104 := by exact prefixLift 1140104
  have htrace : WordTrace (prefixWord ++ tailWord_1140104) baseStart_1140104 baseEnd_1140104 := by
    simpa [prefixWord, tailWord_1140104, baseEnd_1140104] using wordTrace_append hprefix tailTrace_1140104
  have hstable : (prefixWord ++ tailWord_1140104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140104).length < 2 ^ (prefixWord ++ tailWord_1140104).sum := by decide
  have hdescent : baseEnd_1140104 < baseStart_1140104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140147 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8]
def baseStart_1140147 : Nat := 118140960795 + 1140147 * 2 ^ 59
def prefixEnd_1140147 : Nat := 4983230072969 + 3 ^ 40 * 1140147 * 2
def baseEnd_1140147 : Nat := 585443427781855903319065

theorem tailTrace_1140147 : CollatzResearch.WordTrace tailWord_1140147 prefixEnd_1140147 585443427781855903319065 := by
  unfold tailWord_1140147
  simp only [CollatzResearch.WordTrace]
  refine ⟨41584577400449615450130695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27723051600299743633420463 41584577400449615450130695)
  ·
    refine ⟨62376866100674423175196043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41584577400449615450130695 62376866100674423175196043)
    ·
      refine ⟨93565299151011634762794065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62376866100674423175196043 93565299151011634762794065)
      ·
        refine ⟨70173974363258726072095549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93565299151011634762794065 70173974363258726072095549)
        ·
          refine ⟨26315240386222022277035831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70173974363258726072095549 26315240386222022277035831)
          ·
            refine ⟨39472860579333033415553747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26315240386222022277035831 39472860579333033415553747)
            ·
              refine ⟨59209290868999550123330621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39472860579333033415553747 59209290868999550123330621)
              ·
                refine ⟨22203484075874831296248983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59209290868999550123330621 22203484075874831296248983)
                ·
                  refine ⟨33305226113812246944373475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22203484075874831296248983 33305226113812246944373475)
                  ·
                    refine ⟨49957839170718370416560213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33305226113812246944373475 49957839170718370416560213)
                    ·
                      refine ⟨585443427781855903319065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 49957839170718370416560213 585443427781855903319065)
                      ·
                        rfl

theorem cell23_1140147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_1140147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140147 prefixEnd_1140147 := by exact prefixLift 1140147
  have htrace : WordTrace (prefixWord ++ tailWord_1140147) baseStart_1140147 baseEnd_1140147 := by
    simpa [prefixWord, tailWord_1140147, baseEnd_1140147] using wordTrace_append hprefix tailTrace_1140147
  have hstable : (prefixWord ++ tailWord_1140147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140147).length < 2 ^ (prefixWord ++ tailWord_1140147).sum := by decide
  have hdescent : baseEnd_1140147 < baseStart_1140147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140171 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 3]
def baseStart_1140171 : Nat := 118140960795 + 1140171 * 2 ^ 59
def prefixEnd_1140171 : Nat := 4983230072969 + 3 ^ 40 * 1140171 * 2
def baseEnd_1140171 : Nat := 585455751317563809418955

theorem tailTrace_1140171 : CollatzResearch.WordTrace tailWord_1140171 prefixEnd_1140171 585455751317563809418955 := by
  unfold tailWord_1140171
  simp only [CollatzResearch.WordTrace]
  refine ⟨41585452752362667549004367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27723635168241778366002911 41585452752362667549004367)
  ·
    refine ⟨62378179128544001323506551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41585452752362667549004367 62378179128544001323506551)
    ·
      refine ⟨93567268692816001985259827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62378179128544001323506551 93567268692816001985259827)
      ·
        refine ⟨140350903039224002977889741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93567268692816001985259827 140350903039224002977889741)
        ·
          refine ⟨52631588639709001116708653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140350903039224002977889741 52631588639709001116708653)
          ·
            refine ⟨19736845739890875418765745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52631588639709001116708653 19736845739890875418765745)
            ·
              refine ⟨14802634304918156564074309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19736845739890875418765745 14802634304918156564074309)
              ·
                refine ⟨2775493932172154355763933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14802634304918156564074309 2775493932172154355763933)
                ·
                  refine ⟨1040810224564557883411475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2775493932172154355763933 1040810224564557883411475)
                  ·
                    refine ⟨1561215336846836825117213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040810224564557883411475 1561215336846836825117213)
                    ·
                      refine ⟨585455751317563809418955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561215336846836825117213 585455751317563809418955)
                      ·
                        rfl

theorem cell23_1140171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 3].length) (baseStart_1140171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140171 prefixEnd_1140171 := by exact prefixLift 1140171
  have htrace : WordTrace (prefixWord ++ tailWord_1140171) baseStart_1140171 baseEnd_1140171 := by
    simpa [prefixWord, tailWord_1140171, baseEnd_1140171] using wordTrace_append hprefix tailTrace_1140171
  have hstable : (prefixWord ++ tailWord_1140171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140171).length < 2 ^ (prefixWord ++ tailWord_1140171).sum := by decide
  have hdescent : baseEnd_1140171 < baseStart_1140171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140221 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1140221 : Nat := 118140960795 + 1140221 * 2 ^ 59
def prefixEnd_1140221 : Nat := 4983230072969 + 3 ^ 40 * 1140221 * 2
def baseEnd_1140221 : Nat := 195160475116762871264575

theorem tailTrace_1140221 : CollatzResearch.WordTrace tailWord_1140221 prefixEnd_1140221 195160475116762871264575 := by
  unfold tailWord_1140221
  simp only [CollatzResearch.WordTrace]
  refine ⟨41587276402181526088324517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27724850934787684058883011 41587276402181526088324517)
  ·
    refine ⟨7797614325409036141560847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41587276402181526088324517 7797614325409036141560847)
    ·
      refine ⟨11696421488113554212341271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7797614325409036141560847 11696421488113554212341271)
      ·
        refine ⟨17544632232170331318511907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11696421488113554212341271 17544632232170331318511907)
        ·
          refine ⟨26316948348255496977767861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17544632232170331318511907 26316948348255496977767861)
          ·
            refine ⟨2467213907648952841665737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26316948348255496977767861 2467213907648952841665737)
            ·
              refine ⟨1850410430736714631249303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467213907648952841665737 1850410430736714631249303)
              ·
                refine ⟨2775615646105071946873955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1850410430736714631249303 2775615646105071946873955)
                ·
                  refine ⟨4163423469157607920310933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2775615646105071946873955 4163423469157607920310933)
                  ·
                    refine ⟨195160475116762871264575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4163423469157607920310933 195160475116762871264575)
                    ·
                      rfl

theorem cell23_1140221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1140221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140221 prefixEnd_1140221 := by exact prefixLift 1140221
  have htrace : WordTrace (prefixWord ++ tailWord_1140221) baseStart_1140221 baseEnd_1140221 := by
    simpa [prefixWord, tailWord_1140221, baseEnd_1140221] using wordTrace_append hprefix tailTrace_1140221
  have hstable : (prefixWord ++ tailWord_1140221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140221).length < 2 ^ (prefixWord ++ tailWord_1140221).sum := by decide
  have hdescent : baseEnd_1140221 < baseStart_1140221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140222 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1140222 : Nat := 118140960795 + 1140222 * 2 ^ 59
def prefixEnd_1140222 : Nat := 4983230072969 + 3 ^ 40 * 1140222 * 2
def baseEnd_1140222 : Nat := 585481938830943109881221

theorem tailTrace_1140222 : CollatzResearch.WordTrace tailWord_1140222 prefixEnd_1140222 585481938830943109881221 := by
  unfold tailWord_1140222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198414109397237907388865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27724875250118602172740613 5198414109397237907388865)
  ·
    refine ⟨3898810582047928430541649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5198414109397237907388865 3898810582047928430541649)
    ·
      refine ⟨2924107936535946322906237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3898810582047928430541649 2924107936535946322906237)
      ·
        refine ⟨1096540476200979871089839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2924107936535946322906237 1096540476200979871089839)
        ·
          refine ⟨1644810714301469806634759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096540476200979871089839 1644810714301469806634759)
          ·
            refine ⟨2467216071452204709952139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644810714301469806634759 2467216071452204709952139)
            ·
              refine ⟨3700824107178307064928209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467216071452204709952139 3700824107178307064928209)
              ·
                refine ⟨2775618080383730298696157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3700824107178307064928209 2775618080383730298696157)
                ·
                  refine ⟨1040856780143898862011059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2775618080383730298696157 1040856780143898862011059)
                  ·
                    refine ⟨1561285170215848293016589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1040856780143898862011059 1561285170215848293016589)
                    ·
                      refine ⟨585481938830943109881221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561285170215848293016589 585481938830943109881221)
                      ·
                        rfl

theorem cell23_1140222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1140222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140222 prefixEnd_1140222 := by exact prefixLift 1140222
  have htrace : WordTrace (prefixWord ++ tailWord_1140222) baseStart_1140222 baseEnd_1140222 := by
    simpa [prefixWord, tailWord_1140222, baseEnd_1140222] using wordTrace_append hprefix tailTrace_1140222
  have hstable : (prefixWord ++ tailWord_1140222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140222).length < 2 ^ (prefixWord ++ tailWord_1140222).sum := by decide
  have hdescent : baseEnd_1140222 < baseStart_1140222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140245 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_1140245 : Nat := 118140960795 + 1140245 * 2 ^ 59
def prefixEnd_1140245 : Nat := 4983230072969 + 3 ^ 40 * 1140245 * 2
def baseEnd_1140245 : Nat := 585493748885996519893615

theorem tailTrace_1140245 : CollatzResearch.WordTrace tailWord_1140245 prefixEnd_1140245 585493748885996519893615 := by
  unfold tailWord_1140245
  simp only [CollatzResearch.WordTrace]
  refine ⟨41588151754094578187198189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27725434502729718791465459 41588151754094578187198189)
  ·
    refine ⟨15595556907785466820199321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41588151754094578187198189 15595556907785466820199321)
    ·
      refine ⟨11696667680839100115149491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15595556907785466820199321 11696667680839100115149491)
      ·
        refine ⟨17545001521258650172724237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11696667680839100115149491 17545001521258650172724237)
        ·
          refine ⟨6579375570471993814771589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17545001521258650172724237 6579375570471993814771589)
          ·
            refine ⟨1233632919463498840269673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6579375570471993814771589 1233632919463498840269673)
            ·
              refine ⟨925224689597624130202255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233632919463498840269673 925224689597624130202255)
              ·
                refine ⟨1387837034396436195303383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925224689597624130202255 1387837034396436195303383)
                ·
                  refine ⟨2081755551594654292955075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1387837034396436195303383 2081755551594654292955075)
                  ·
                    refine ⟨3122633327391981439432613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2081755551594654292955075 3122633327391981439432613)
                    ·
                      refine ⟨585493748885996519893615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3122633327391981439432613 585493748885996519893615)
                      ·
                        rfl

theorem cell23_1140245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_1140245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140245 prefixEnd_1140245 := by exact prefixLift 1140245
  have htrace : WordTrace (prefixWord ++ tailWord_1140245) baseStart_1140245 baseEnd_1140245 := by
    simpa [prefixWord, tailWord_1140245, baseEnd_1140245] using wordTrace_append hprefix tailTrace_1140245
  have hstable : (prefixWord ++ tailWord_1140245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140245).length < 2 ^ (prefixWord ++ tailWord_1140245).sum := by decide
  have hdescent : baseEnd_1140245 < baseStart_1140245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140285 : List Nat := [1, 4, 1, 3, 4, 1, 2, 7]
def baseStart_1140285 : Nat := 118140960795 + 1140285 * 2 ^ 59
def prefixEnd_1140285 : Nat := 4983230072969 + 3 ^ 40 * 1140285 * 2
def baseEnd_1140285 : Nat := 21685714374525050496053

theorem tailTrace_1140285 : CollatzResearch.WordTrace tailWord_1140285 prefixEnd_1140285 21685714374525050496053 := by
  unfold tailWord_1140285
  simp only [CollatzResearch.WordTrace]
  refine ⟨41589610673949665018654309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27726407115966443345769539 41589610673949665018654309)
  ·
    refine ⟨7798052001365562190997683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41589610673949665018654309 7798052001365562190997683)
    ·
      refine ⟨11697078002048343286496525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7798052001365562190997683 11697078002048343286496525)
      ·
        refine ⟨4386404250768128732436197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11697078002048343286496525 4386404250768128732436197)
        ·
          refine ⟨822450797019024137331787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4386404250768128732436197 822450797019024137331787)
          ·
            refine ⟨1233676195528536205997681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822450797019024137331787 1233676195528536205997681)
            ·
              refine ⟨925257146646402154498261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233676195528536205997681 925257146646402154498261)
              ·
                refine ⟨21685714374525050496053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 925257146646402154498261 21685714374525050496053)
                ·
                  rfl

theorem cell23_1140285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 7].length) (baseStart_1140285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140285 prefixEnd_1140285 := by exact prefixLift 1140285
  have htrace : WordTrace (prefixWord ++ tailWord_1140285) baseStart_1140285 baseEnd_1140285 := by
    simpa [prefixWord, tailWord_1140285, baseEnd_1140285] using wordTrace_append hprefix tailTrace_1140285
  have hstable : (prefixWord ++ tailWord_1140285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140285).length < 2 ^ (prefixWord ++ tailWord_1140285).sum := by decide
  have hdescent : baseEnd_1140285 < baseStart_1140285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140321 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1140321 : Nat := 118140960795 + 1140321 * 2 ^ 59
def prefixEnd_1140321 : Nat := 4983230072969 + 3 ^ 40 * 1140321 * 2
def baseEnd_1140321 : Nat := 585532773415738222543265

theorem tailTrace_1140321 : CollatzResearch.WordTrace tailWord_1140321 prefixEnd_1140321 585532773415738222543265 := by
  unfold tailWord_1140321
  simp only [CollatzResearch.WordTrace]
  refine ⟨41590923701819243166964817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27727282467879495444643211 41590923701819243166964817)
  ·
    refine ⟨31193192776364432375223613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41590923701819243166964817 31193192776364432375223613)
    ·
      refine ⟨11697447291136662140708855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31193192776364432375223613 11697447291136662140708855)
      ·
        refine ⟨17546170936704993211063283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11697447291136662140708855 17546170936704993211063283)
        ·
          refine ⟨26319256405057489816594925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17546170936704993211063283 26319256405057489816594925)
          ·
            refine ⟨9869721151896558681223097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26319256405057489816594925 9869721151896558681223097)
            ·
              refine ⟨7402290863922419010917323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9869721151896558681223097 7402290863922419010917323)
              ·
                refine ⟨11103436295883628516375985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7402290863922419010917323 11103436295883628516375985)
                ·
                  refine ⟨8327577221912721387281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11103436295883628516375985 8327577221912721387281989)
                  ·
                    refine ⟨1561420729108635260115373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8327577221912721387281989 1561420729108635260115373)
                    ·
                      refine ⟨585532773415738222543265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561420729108635260115373 585532773415738222543265)
                      ·
                        rfl

theorem cell23_1140321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1140321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140321 prefixEnd_1140321 := by exact prefixLift 1140321
  have htrace : WordTrace (prefixWord ++ tailWord_1140321) baseStart_1140321 baseEnd_1140321 := by
    simpa [prefixWord, tailWord_1140321, baseEnd_1140321] using wordTrace_append hprefix tailTrace_1140321
  have hstable : (prefixWord ++ tailWord_1140321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140321).length < 2 ^ (prefixWord ++ tailWord_1140321).sum := by decide
  have hdescent : baseEnd_1140321 < baseStart_1140321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140375 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 5]
def baseStart_1140375 : Nat := 118140960795 + 1140375 * 2 ^ 59
def prefixEnd_1140375 : Nat := 4983230072969 + 3 ^ 40 * 1140375 * 2
def baseEnd_1140375 : Nat := 65062277930120112363113

theorem tailTrace_1140375 : CollatzResearch.WordTrace tailWord_1140375 prefixEnd_1140375 65062277930120112363113 := by
  unfold tailWord_1140375
  simp only [CollatzResearch.WordTrace]
  refine ⟨41592893243623610389430579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27728595495749073592953719 41592893243623610389430579)
  ·
    refine ⟨62389339865435415584145869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41592893243623610389430579 62389339865435415584145869)
    ·
      refine ⟨23396002449538280844054701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62389339865435415584145869 23396002449538280844054701)
      ·
        refine ⟨8773500918576855316520513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23396002449538280844054701 8773500918576855316520513)
        ·
          refine ⟨6580125688932641487390385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8773500918576855316520513 6580125688932641487390385)
          ·
            refine ⟨4935094266699481115542789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6580125688932641487390385 4935094266699481115542789)
            ·
              refine ⟨925330175006152709164273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4935094266699481115542789 925330175006152709164273)
              ·
                refine ⟨693997631254614531873205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925330175006152709164273 693997631254614531873205)
                ·
                  refine ⟨65062277930120112363113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 693997631254614531873205 65062277930120112363113)
                  ·
                    rfl

theorem cell23_1140375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 5].length) (baseStart_1140375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140375 prefixEnd_1140375 := by exact prefixLift 1140375
  have htrace : WordTrace (prefixWord ++ tailWord_1140375) baseStart_1140375 baseEnd_1140375 := by
    simpa [prefixWord, tailWord_1140375, baseEnd_1140375] using wordTrace_append hprefix tailTrace_1140375
  have hstable : (prefixWord ++ tailWord_1140375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140375).length < 2 ^ (prefixWord ++ tailWord_1140375).sum := by decide
  have hdescent : baseEnd_1140375 < baseStart_1140375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140392 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 7]
def baseStart_1140392 : Nat := 118140960795 + 1140392 * 2 ^ 59
def prefixEnd_1140392 : Nat := 4983230072969 + 3 ^ 40 * 1140392 * 2
def baseEnd_1140392 : Nat := 65063247838023049417271

theorem tailTrace_1140392 : CollatzResearch.WordTrace tailWord_1140392 prefixEnd_1140392 65063247838023049417271 := by
  unfold tailWord_1140392
  simp only [CollatzResearch.WordTrace]
  refine ⟨20796756642281011146399715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27729008856374681528532953 20796756642281011146399715)
  ·
    refine ⟨31195134963421516719599573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20796756642281011146399715 31195134963421516719599573)
    ·
      refine ⟨731135975705191798115615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31195134963421516719599573 731135975705191798115615)
      ·
        refine ⟨1096703963557787697173423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731135975705191798115615 1096703963557787697173423)
        ·
          refine ⟨1645055945336681545760135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096703963557787697173423 1645055945336681545760135)
          ·
            refine ⟨2467583918005022318640203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645055945336681545760135 2467583918005022318640203)
            ·
              refine ⟨3701375877007533477960305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2467583918005022318640203 3701375877007533477960305)
              ·
                refine ⟨2776031907755650108470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3701375877007533477960305 2776031907755650108470229)
                ·
                  refine ⟨65063247838023049417271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2776031907755650108470229 65063247838023049417271)
                  ·
                    rfl

theorem cell23_1140392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 7].length) (baseStart_1140392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140392 prefixEnd_1140392 := by exact prefixLift 1140392
  have htrace : WordTrace (prefixWord ++ tailWord_1140392) baseStart_1140392 baseEnd_1140392 := by
    simpa [prefixWord, tailWord_1140392, baseEnd_1140392] using wordTrace_append hprefix tailTrace_1140392
  have hstable : (prefixWord ++ tailWord_1140392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140392).length < 2 ^ (prefixWord ++ tailWord_1140392).sum := by decide
  have hdescent : baseEnd_1140392 < baseStart_1140392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140492 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_1140492 : Nat := 118140960795 + 1140492 * 2 ^ 59
def prefixEnd_1140492 : Nat := 4983230072969 + 3 ^ 40 * 1140492 * 2
def baseEnd_1140492 : Nat := 585620578607657053504979

theorem tailTrace_1140492 : CollatzResearch.WordTrace tailWord_1140492 prefixEnd_1140492 585620578607657053504979 := by
  unfold tailWord_1140492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20798580292099869685719865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27731440389466492914293153 20798580292099869685719865)
  ·
    refine ⟨15598935219074902264289899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20798580292099869685719865 15598935219074902264289899)
    ·
      refine ⟨23398402828612353396434849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15598935219074902264289899 23398402828612353396434849)
      ·
        refine ⟨17548802121459265047326137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23398402828612353396434849 17548802121459265047326137)
        ·
          refine ⟨13161601591094448785494603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17548802121459265047326137 13161601591094448785494603)
          ·
            refine ⟨19742402386641673178241905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161601591094448785494603 19742402386641673178241905)
            ·
              refine ⟨14806801789981254883681429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19742402386641673178241905 14806801789981254883681429)
              ·
                refine ⟨694068833905371322672567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14806801789981254883681429 694068833905371322672567)
                ·
                  refine ⟨1041103250858056984008851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694068833905371322672567 1041103250858056984008851)
                  ·
                    refine ⟨1561654876287085476013277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041103250858056984008851 1561654876287085476013277)
                    ·
                      refine ⟨585620578607657053504979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561654876287085476013277 585620578607657053504979)
                      ·
                        rfl

theorem cell23_1140492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_1140492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140492 prefixEnd_1140492 := by exact prefixLift 1140492
  have htrace : WordTrace (prefixWord ++ tailWord_1140492) baseStart_1140492 baseEnd_1140492 := by
    simpa [prefixWord, tailWord_1140492, baseEnd_1140492] using wordTrace_append hprefix tailTrace_1140492
  have hstable : (prefixWord ++ tailWord_1140492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140492).length < 2 ^ (prefixWord ++ tailWord_1140492).sum := by decide
  have hdescent : baseEnd_1140492 < baseStart_1140492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140508 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1140508 : Nat := 118140960795 + 1140508 * 2 ^ 59
def prefixEnd_1140508 : Nat := 4983230072969 + 3 ^ 40 * 1140508 * 2
def baseEnd_1140508 : Nat := 195209598099376330301635

theorem tailTrace_1140508 : CollatzResearch.WordTrace tailWord_1140508 prefixEnd_1140508 195209598099376330301635 := by
  unfold tailWord_1140508
  simp only [CollatzResearch.WordTrace]
  refine ⟨20798872076070887052011089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27731829434761182736014785 20798872076070887052011089)
  ·
    refine ⟨15599154057053165289008317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20798872076070887052011089 15599154057053165289008317)
    ·
      refine ⟨5849682771394936983378119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15599154057053165289008317 5849682771394936983378119)
      ·
        refine ⟨8774524157092405475067179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5849682771394936983378119 8774524157092405475067179)
        ·
          refine ⟨13161786235638608212600769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774524157092405475067179 13161786235638608212600769)
          ·
            refine ⟨9871339676728956159450577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13161786235638608212600769 9871339676728956159450577)
            ·
              refine ⟨7403504757546717119587933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9871339676728956159450577 7403504757546717119587933)
              ·
                refine ⟨2776314284080018919845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7403504757546717119587933 2776314284080018919845475)
                ·
                  refine ⟨4164471426120028379768213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776314284080018919845475 4164471426120028379768213)
                  ·
                    refine ⟨195209598099376330301635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4164471426120028379768213 195209598099376330301635)
                    ·
                      rfl

theorem cell23_1140508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1140508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140508 prefixEnd_1140508 := by exact prefixLift 1140508
  have htrace : WordTrace (prefixWord ++ tailWord_1140508) baseStart_1140508 baseEnd_1140508 := by
    simpa [prefixWord, tailWord_1140508, baseEnd_1140508] using wordTrace_append hprefix tailTrace_1140508
  have hstable : (prefixWord ++ tailWord_1140508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140508).length < 2 ^ (prefixWord ++ tailWord_1140508).sum := by decide
  have hdescent : baseEnd_1140508 < baseStart_1140508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140515 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 4]
def baseStart_1140515 : Nat := 118140960795 + 1140515 * 2 ^ 59
def prefixEnd_1140515 : Nat := 4983230072969 + 3 ^ 40 * 1140515 * 2
def baseEnd_1140515 : Nat := 585632388662710463517373

theorem tailTrace_1140515 : CollatzResearch.WordTrace tailWord_1140515 prefixEnd_1140515 585632388662710463517373 := by
  unfold tailWord_1140515
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597999463116414299526999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27731999642077609533017999 41597999463116414299526999)
  ·
    refine ⟨62396999194674621449290499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41597999463116414299526999 62396999194674621449290499)
    ·
      refine ⟨93595498792011932173935749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62396999194674621449290499 93595498792011932173935749)
      ·
        refine ⟨17549156023502237282612953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93595498792011932173935749 17549156023502237282612953)
        ·
          refine ⟨13161867017626677961959715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17549156023502237282612953 13161867017626677961959715)
          ·
            refine ⟨19742800526440016942939573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13161867017626677961959715 19742800526440016942939573)
            ·
              refine ⟨1850887549353751588400585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19742800526440016942939573 1850887549353751588400585)
              ·
                refine ⟨1388165662015313691300439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850887549353751588400585 1388165662015313691300439)
                ·
                  refine ⟨2082248493022970536950659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388165662015313691300439 2082248493022970536950659)
                  ·
                    refine ⟨3123372739534455805425989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2082248493022970536950659 3123372739534455805425989)
                    ·
                      refine ⟨585632388662710463517373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3123372739534455805425989 585632388662710463517373)
                      ·
                        rfl

theorem cell23_1140515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_1140515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140515 prefixEnd_1140515 := by exact prefixLift 1140515
  have htrace : WordTrace (prefixWord ++ tailWord_1140515) baseStart_1140515 baseEnd_1140515 := by
    simpa [prefixWord, tailWord_1140515, baseEnd_1140515] using wordTrace_append hprefix tailTrace_1140515
  have hstable : (prefixWord ++ tailWord_1140515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140515).length < 2 ^ (prefixWord ++ tailWord_1140515).sum := by decide
  have hdescent : baseEnd_1140515 < baseStart_1140515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140542 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1140542 : Nat := 118140960795 + 1140542 * 2 ^ 59
def prefixEnd_1140542 : Nat := 4983230072969 + 3 ^ 40 * 1140542 * 2
def baseEnd_1140542 : Nat := 195215417546793952626583

theorem tailTrace_1140542 : CollatzResearch.WordTrace tailWord_1140542 prefixEnd_1140542 195215417546793952626583 := by
  unfold tailWord_1140542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199873029252324738844985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27732656156012398607173253 5199873029252324738844985)
  ·
    refine ⟨3899904771939243554133739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5199873029252324738844985 3899904771939243554133739)
    ·
      refine ⟨5849857157908865331200609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3899904771939243554133739 5849857157908865331200609)
      ·
        refine ⟨4387392868431648998400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5849857157908865331200609 4387392868431648998400457)
        ·
          refine ⟨3290544651323736748800343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387392868431648998400457 3290544651323736748800343)
          ·
            refine ⟨4935816976985605123200515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290544651323736748800343 4935816976985605123200515)
            ·
              refine ⟨7403725465478407684800773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935816976985605123200515 7403725465478407684800773)
              ·
                refine ⟨1388198524777201440900145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7403725465478407684800773 1388198524777201440900145)
                ·
                  refine ⟨1041148893582901080675109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388198524777201440900145 1041148893582901080675109)
                  ·
                    refine ⟨195215417546793952626583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041148893582901080675109 195215417546793952626583)
                    ·
                      rfl

theorem cell23_1140542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1140542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140542 prefixEnd_1140542 := by exact prefixLift 1140542
  have htrace : WordTrace (prefixWord ++ tailWord_1140542) baseStart_1140542 baseEnd_1140542 := by
    simpa [prefixWord, tailWord_1140542, baseEnd_1140542] using wordTrace_append hprefix tailTrace_1140542
  have hstable : (prefixWord ++ tailWord_1140542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140542).length < 2 ^ (prefixWord ++ tailWord_1140542).sum := by decide
  have hdescent : baseEnd_1140542 < baseStart_1140542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140543 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 1, 1, 3]
def baseStart_1140543 : Nat := 118140960795 + 1140543 * 2 ^ 59
def prefixEnd_1140543 : Nat := 4983230072969 + 3 ^ 40 * 1140543 * 2
def baseEnd_1140543 : Nat := 585646766121036353967245

theorem tailTrace_1140543 : CollatzResearch.WordTrace tailWord_1140543 prefixEnd_1140543 585646766121036353967245 := by
  unfold tailWord_1140543
  simp only [CollatzResearch.WordTrace]
  refine ⟨41599020707014975081546283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27732680471343316721030855 41599020707014975081546283)
  ·
    refine ⟨62398531060522462622319425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41599020707014975081546283 62398531060522462622319425)
    ·
      refine ⟨46798898295391846966739569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62398531060522462622319425 46798898295391846966739569)
      ·
        refine ⟨35099173721543885225054677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46798898295391846966739569 35099173721543885225054677)
        ·
          refine ⟨822636884098684809962219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35099173721543885225054677 822636884098684809962219)
          ·
            refine ⟨1233955326148027214943329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822636884098684809962219 1233955326148027214943329)
            ·
              refine ⟨925466494611020411207497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233955326148027214943329 925466494611020411207497)
              ·
                refine ⟨694099870958265308405623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925466494611020411207497 694099870958265308405623)
                ·
                  refine ⟨1041149806437397962608435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694099870958265308405623 1041149806437397962608435)
                  ·
                    refine ⟨1561724709656096943912653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041149806437397962608435 1561724709656096943912653)
                    ·
                      refine ⟨585646766121036353967245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561724709656096943912653 585646766121036353967245)
                      ·
                        rfl

theorem cell23_1140543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_1140543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140543 prefixEnd_1140543 := by exact prefixLift 1140543
  have htrace : WordTrace (prefixWord ++ tailWord_1140543) baseStart_1140543 baseEnd_1140543 := by
    simpa [prefixWord, tailWord_1140543, baseEnd_1140543] using wordTrace_append hprefix tailTrace_1140543
  have hstable : (prefixWord ++ tailWord_1140543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140543).length < 2 ^ (prefixWord ++ tailWord_1140543).sum := by decide
  have hdescent : baseEnd_1140543 < baseStart_1140543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140549 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_1140549 : Nat := 118140960795 + 1140549 * 2 ^ 59
def prefixEnd_1140549 : Nat := 4983230072969 + 3 ^ 40 * 1140549 * 2
def baseEnd_1140549 : Nat := 585649847004963330492217

theorem tailTrace_1140549 : CollatzResearch.WordTrace tailWord_1140549 prefixEnd_1140549 585649847004963330492217 := by
  unfold tailWord_1140549
  simp only [CollatzResearch.WordTrace]
  refine ⟨41599239544993238106264701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27732826363328825404176467 41599239544993238106264701)
  ·
    refine ⟨15599714829372464289849263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41599239544993238106264701 15599714829372464289849263)
    ·
      refine ⟨23399572244058696434773895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15599714829372464289849263 23399572244058696434773895)
      ·
        refine ⟨35099358366088044652160843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23399572244058696434773895 35099358366088044652160843)
        ·
          refine ⟨52649037549132066978241265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35099358366088044652160843 52649037549132066978241265)
          ·
            refine ⟨39486778161849050233680949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52649037549132066978241265 39486778161849050233680949)
            ·
              refine ⟨3701885452673348459407589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39486778161849050233680949 3701885452673348459407589)
              ·
                refine ⟨694103522376252836138923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3701885452673348459407589 694103522376252836138923)
                ·
                  refine ⟨1041155283564379254208385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694103522376252836138923 1041155283564379254208385)
                  ·
                    refine ⟨780866462673284440656289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041155283564379254208385 780866462673284440656289)
                    ·
                      refine ⟨585649847004963330492217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780866462673284440656289 585649847004963330492217)
                      ·
                        rfl

theorem cell23_1140549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_1140549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140549 prefixEnd_1140549 := by exact prefixLift 1140549
  have htrace : WordTrace (prefixWord ++ tailWord_1140549) baseStart_1140549 baseEnd_1140549 := by
    simpa [prefixWord, tailWord_1140549, baseEnd_1140549] using wordTrace_append hprefix tailTrace_1140549
  have hstable : (prefixWord ++ tailWord_1140549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140549).length < 2 ^ (prefixWord ++ tailWord_1140549).sum := by decide
  have hdescent : baseEnd_1140549 < baseStart_1140549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140565 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1140565 : Nat := 118140960795 + 1140565 * 2 ^ 59
def prefixEnd_1140565 : Nat := 4983230072969 + 3 ^ 40 * 1140565 * 2
def baseEnd_1140565 : Nat := 585658062695435267892143

theorem tailTrace_1140565 : CollatzResearch.WordTrace tailWord_1140565 prefixEnd_1140565 585658062695435267892143 := by
  unfold tailWord_1140565
  simp only [CollatzResearch.WordTrace]
  refine ⟨41599823112935272838847149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27733215408623515225898099 41599823112935272838847149)
  ·
    refine ⟨15599933667350727314567681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41599823112935272838847149 15599933667350727314567681)
    ·
      refine ⟨11699950250513045485925761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15599933667350727314567681 11699950250513045485925761)
      ·
        refine ⟨8774962687884784114444321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11699950250513045485925761 8774962687884784114444321)
        ·
          refine ⟨6581222015913588085833241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8774962687884784114444321 6581222015913588085833241)
          ·
            refine ⟨4935916511935191064374931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6581222015913588085833241 4935916511935191064374931)
            ·
              refine ⟨7403874767902786596562397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4935916511935191064374931 7403874767902786596562397)
              ·
                refine ⟨2776453037963544973710899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7403874767902786596562397 2776453037963544973710899)
                ·
                  refine ⟨4164679556945317460566349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2776453037963544973710899 4164679556945317460566349)
                  ·
                    refine ⟨1561754833854494047712381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4164679556945317460566349 1561754833854494047712381)
                    ·
                      refine ⟨585658062695435267892143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561754833854494047712381 585658062695435267892143)
                      ·
                        rfl

theorem cell23_1140565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1140565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140565 prefixEnd_1140565 := by exact prefixLift 1140565
  have htrace : WordTrace (prefixWord ++ tailWord_1140565) baseStart_1140565 baseEnd_1140565 := by
    simpa [prefixWord, tailWord_1140565, baseEnd_1140565] using wordTrace_append hprefix tailTrace_1140565
  have hstable : (prefixWord ++ tailWord_1140565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140565).length < 2 ^ (prefixWord ++ tailWord_1140565).sum := by decide
  have hdescent : baseEnd_1140565 < baseStart_1140565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140572 : List Nat := [2, 2, 4, 2, 2, 1, 3, 7]
def baseStart_1140572 : Nat := 118140960795 + 1140572 * 2 ^ 59
def prefixEnd_1140572 : Nat := 4983230072969 + 3 ^ 40 * 1140572 * 2
def baseEnd_1140572 : Nat := 21691172483704323722393

theorem tailTrace_1140572 : CollatzResearch.WordTrace tailWord_1140572 prefixEnd_1140572 21691172483704323722393 := by
  unfold tailWord_1140572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20800039211954956517175985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27733385615939942022901313 20800039211954956517175985)
  ·
    refine ⟨15600029408966217387881989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20800039211954956517175985 15600029408966217387881989)
    ·
      refine ⟨2925005514181165760227873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15600029408966217387881989 2925005514181165760227873)
      ·
        refine ⟨2193754135635874320170905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2925005514181165760227873 2193754135635874320170905)
        ·
          refine ⟨1645315601726905740128179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193754135635874320170905 1645315601726905740128179)
          ·
            refine ⟨2467973402590358610192269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645315601726905740128179 2467973402590358610192269)
            ·
              refine ⟨925490025971384478822101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2467973402590358610192269 925490025971384478822101)
              ·
                refine ⟨21691172483704323722393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 925490025971384478822101 21691172483704323722393)
                ·
                  rfl

theorem cell23_1140572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 7].length) (baseStart_1140572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140572 prefixEnd_1140572 := by exact prefixLift 1140572
  have htrace : WordTrace (prefixWord ++ tailWord_1140572) baseStart_1140572 baseEnd_1140572 := by
    simpa [prefixWord, tailWord_1140572, baseEnd_1140572] using wordTrace_append hprefix tailTrace_1140572
  have hstable : (prefixWord ++ tailWord_1140572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140572).length < 2 ^ (prefixWord ++ tailWord_1140572).sum := by decide
  have hdescent : baseEnd_1140572 < baseStart_1140572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140616 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1140616 : Nat := 118140960795 + 1140616 * 2 ^ 59
def prefixEnd_1140616 : Nat := 4983230072969 + 3 ^ 40 * 1140616 * 2
def baseEnd_1140616 : Nat := 585684250208814568354409

theorem tailTrace_1140616 : CollatzResearch.WordTrace tailWord_1140616 prefixEnd_1140616 585684250208814568354409 := by
  unfold tailWord_1140616
  simp only [CollatzResearch.WordTrace]
  refine ⟨20800841617875254274476851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27734455490500339032635801 20800841617875254274476851)
  ·
    refine ⟨31201262426812881411715277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20800841617875254274476851 31201262426812881411715277)
    ·
      refine ⟨11700473410054830529393229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31201262426812881411715277 11700473410054830529393229)
      ·
        refine ⟨4387677528770561448522461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11700473410054830529393229 4387677528770561448522461)
        ·
          refine ⟨1645379073288960543195923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387677528770561448522461 1645379073288960543195923)
          ·
            refine ⟨2468068609933440814793885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645379073288960543195923 2468068609933440814793885)
            ·
              refine ⟨925525728725040305547707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468068609933440814793885 925525728725040305547707)
              ·
                refine ⟨1388288593087560458321561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925525728725040305547707 1388288593087560458321561)
                ·
                  refine ⟨1041216444815670343741171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388288593087560458321561 1041216444815670343741171)
                  ·
                    refine ⟨1561824667223505515611757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041216444815670343741171 1561824667223505515611757)
                    ·
                      refine ⟨585684250208814568354409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1561824667223505515611757 585684250208814568354409)
                      ·
                        rfl

theorem cell23_1140616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1140616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140616 prefixEnd_1140616 := by exact prefixLift 1140616
  have htrace : WordTrace (prefixWord ++ tailWord_1140616) baseStart_1140616 baseEnd_1140616 := by
    simpa [prefixWord, tailWord_1140616, baseEnd_1140616] using wordTrace_append hprefix tailTrace_1140616
  have hstable : (prefixWord ++ tailWord_1140616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140616).length < 2 ^ (prefixWord ++ tailWord_1140616).sum := by decide
  have hdescent : baseEnd_1140616 < baseStart_1140616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140626 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1140626 : Nat := 118140960795 + 1140626 * 2 ^ 59
def prefixEnd_1140626 : Nat := 4983230072969 + 3 ^ 40 * 1140626 * 2
def baseEnd_1140626 : Nat := 585689385015359529229363

theorem tailTrace_1140626 : CollatzResearch.WordTrace tailWord_1140626 prefixEnd_1140626 585689385015359529229363 := by
  unfold tailWord_1140626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400511991428570064204433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27734698643809520171211821 10400511991428570064204433)
  ·
    refine ⟨7800383993571427548153325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10400511991428570064204433 7800383993571427548153325)
    ·
      refine ⟨2925143997589285330557497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7800383993571427548153325 2925143997589285330557497)
      ·
        refine ⟨2193857998191963997918123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2925143997589285330557497 2193857998191963997918123)
        ·
          refine ⟨3290786997287945996877185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2193857998191963997918123 3290786997287945996877185)
          ·
            refine ⟨2468090247965959497657889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3290786997287945996877185 2468090247965959497657889)
            ·
              refine ⟨1851067685974469623243417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468090247965959497657889 1851067685974469623243417)
              ·
                refine ⟨1388300764480852217432563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851067685974469623243417 1388300764480852217432563)
                ·
                  refine ⟨2082451146721278326148845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388300764480852217432563 2082451146721278326148845)
                  ·
                    refine ⟨780919180020479372305817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2082451146721278326148845 780919180020479372305817)
                    ·
                      refine ⟨585689385015359529229363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780919180020479372305817 585689385015359529229363)
                      ·
                        rfl

theorem cell23_1140626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1140626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140626 prefixEnd_1140626 := by exact prefixLift 1140626
  have htrace : WordTrace (prefixWord ++ tailWord_1140626) baseStart_1140626 baseEnd_1140626 := by
    simpa [prefixWord, tailWord_1140626, baseEnd_1140626] using wordTrace_append hprefix tailTrace_1140626
  have hstable : (prefixWord ++ tailWord_1140626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140626).length < 2 ^ (prefixWord ++ tailWord_1140626).sum := by decide
  have hdescent : baseEnd_1140626 < baseStart_1140626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140642 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1140642 : Nat := 118140960795 + 1140642 * 2 ^ 59
def prefixEnd_1140642 : Nat := 4983230072969 + 3 ^ 40 * 1140642 * 2
def baseEnd_1140642 : Nat := 585697600705831466629289

theorem tailTrace_1140642 : CollatzResearch.WordTrace tailWord_1140642 prefixEnd_1140642 585697600705831466629289 := by
  unfold tailWord_1140642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400657883414078747350045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27735087689104209992933453 10400657883414078747350045)
  ·
    refine ⟨3900246706280279530256267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10400657883414078747350045 3900246706280279530256267)
    ·
      refine ⟨5850370059420419295384401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900246706280279530256267 5850370059420419295384401)
      ·
        refine ⟨4387777544565314471538301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850370059420419295384401 4387777544565314471538301)
        ·
          refine ⟨1645416579211992926826863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387777544565314471538301 1645416579211992926826863)
          ·
            refine ⟨2468124868817989390240295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645416579211992926826863 2468124868817989390240295)
            ·
              refine ⟨3702187303226984085360443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468124868817989390240295 3702187303226984085360443)
              ·
                refine ⟨5553280954840476128040665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702187303226984085360443 5553280954840476128040665)
                ·
                  refine ⟨4164960716130357096030499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553280954840476128040665 4164960716130357096030499)
                  ·
                    refine ⟨6247441074195535644045749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4164960716130357096030499 6247441074195535644045749)
                    ·
                      refine ⟨585697600705831466629289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6247441074195535644045749 585697600705831466629289)
                      ·
                        rfl

theorem cell23_1140642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1140642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140642 prefixEnd_1140642 := by exact prefixLift 1140642
  have htrace : WordTrace (prefixWord ++ tailWord_1140642) baseStart_1140642 baseEnd_1140642 := by
    simpa [prefixWord, tailWord_1140642, baseEnd_1140642] using wordTrace_append hprefix tailTrace_1140642
  have hstable : (prefixWord ++ tailWord_1140642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140642).length < 2 ^ (prefixWord ++ tailWord_1140642).sum := by decide
  have hdescent : baseEnd_1140642 < baseStart_1140642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140688 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_1140688 : Nat := 118140960795 + 1140688 * 2 ^ 59
def prefixEnd_1140688 : Nat := 4983230072969 + 3 ^ 40 * 1140688 * 2
def baseEnd_1140688 : Nat := 195240406938646095551359

theorem tailTrace_1140688 : CollatzResearch.WordTrace tailWord_1140688 prefixEnd_1140688 195240406938646095551359 := by
  unfold tailWord_1140688
  simp only [CollatzResearch.WordTrace]
  refine ⟨20802154645744832422787359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27736206194326443230383145 20802154645744832422787359)
  ·
    refine ⟨31203231968617248634181039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20802154645744832422787359 31203231968617248634181039)
    ·
      refine ⟨46804847952925872951271559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31203231968617248634181039 46804847952925872951271559)
      ·
        refine ⟨70207271929388809426907339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46804847952925872951271559 70207271929388809426907339)
        ·
          refine ⟨105310907894083214140361009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70207271929388809426907339 105310907894083214140361009)
          ·
            refine ⟨78983180920562410605270757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105310907894083214140361009 78983180920562410605270757)
            ·
              refine ⟨14809346422605451988488267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78983180920562410605270757 14809346422605451988488267)
              ·
                refine ⟨22214019633908177982732401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14809346422605451988488267 22214019633908177982732401)
                ·
                  refine ⟨16660514725431133487049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22214019633908177982732401 16660514725431133487049301)
                  ·
                    refine ⟨195240406938646095551359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16660514725431133487049301 195240406938646095551359)
                    ·
                      rfl

theorem cell23_1140688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_1140688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140688 prefixEnd_1140688 := by exact prefixLift 1140688
  have htrace : WordTrace (prefixWord ++ tailWord_1140688) baseStart_1140688 baseEnd_1140688 := by
    simpa [prefixWord, tailWord_1140688, baseEnd_1140688] using wordTrace_append hprefix tailTrace_1140688
  have hstable : (prefixWord ++ tailWord_1140688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140688).length < 2 ^ (prefixWord ++ tailWord_1140688).sum := by decide
  have hdescent : baseEnd_1140688 < baseStart_1140688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140692 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1140692 : Nat := 118140960795 + 1140692 * 2 ^ 59
def prefixEnd_1140692 : Nat := 4983230072969 + 3 ^ 40 * 1140692 * 2
def baseEnd_1140692 : Nat := 195241091579518757001353

theorem tailTrace_1140692 : CollatzResearch.WordTrace tailWord_1140692 prefixEnd_1140692 195241091579518757001353 := by
  unfold tailWord_1140692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20802227591737586764360165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27736303455650115685813553 20802227591737586764360165)
  ·
    refine ⟨3900417673450797518317531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20802227591737586764360165 3900417673450797518317531)
    ·
      refine ⟨5850626510176196277476297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3900417673450797518317531 5850626510176196277476297)
      ·
        refine ⟨4387969882632147208107223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850626510176196277476297 4387969882632147208107223)
        ·
          refine ⟨6581954823948220812160835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387969882632147208107223 6581954823948220812160835)
          ·
            refine ⟨9872932235922331218241253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581954823948220812160835 9872932235922331218241253)
            ·
              refine ⟨1851174794235437103420235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9872932235922331218241253 1851174794235437103420235)
              ·
                refine ⟨2776762191353155655130353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851174794235437103420235 2776762191353155655130353)
                ·
                  refine ⟨2082571643514866741347765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2776762191353155655130353 2082571643514866741347765)
                  ·
                    refine ⟨195241091579518757001353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2082571643514866741347765 195241091579518757001353)
                    ·
                      rfl

theorem cell23_1140692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1140692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140692 prefixEnd_1140692 := by exact prefixLift 1140692
  have htrace : WordTrace (prefixWord ++ tailWord_1140692) baseStart_1140692 baseEnd_1140692 := by
    simpa [prefixWord, tailWord_1140692, baseEnd_1140692] using wordTrace_append hprefix tailTrace_1140692
  have hstable : (prefixWord ++ tailWord_1140692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140692).length < 2 ^ (prefixWord ++ tailWord_1140692).sum := by decide
  have hdescent : baseEnd_1140692 < baseStart_1140692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140712 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1140712 : Nat := 118140960795 + 1140712 * 2 ^ 59
def prefixEnd_1140712 : Nat := 4983230072969 + 3 ^ 40 * 1140712 * 2
def baseEnd_1140712 : Nat := 585733544351646192753967

theorem tailTrace_1140712 : CollatzResearch.WordTrace tailWord_1140712 prefixEnd_1140712 585733544351646192753967 := by
  unfold tailWord_1140712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20802592321701358472224195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27736789762268477962965593 20802592321701358472224195)
  ·
    refine ⟨31203888482552037708336293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20802592321701358472224195 31203888482552037708336293)
    ·
      refine ⟨5850729090478507070313055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31203888482552037708336293 5850729090478507070313055)
      ·
        refine ⟨8776093635717760605469583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850729090478507070313055 8776093635717760605469583)
        ·
          refine ⟨13164140453576640908204375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776093635717760605469583 13164140453576640908204375)
          ·
            refine ⟨19746210680364961362306563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13164140453576640908204375 19746210680364961362306563)
            ·
              refine ⟨29619316020547442043459845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19746210680364961362306563 29619316020547442043459845)
              ·
                refine ⟨5553621753852645383148721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29619316020547442043459845 5553621753852645383148721)
                ·
                  refine ⟨4165216315389484037361541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5553621753852645383148721 4165216315389484037361541)
                  ·
                    refine ⟨780978059135528257005289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4165216315389484037361541 780978059135528257005289)
                    ·
                      refine ⟨585733544351646192753967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 780978059135528257005289 585733544351646192753967)
                      ·
                        rfl

theorem cell23_1140712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1140712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140712 prefixEnd_1140712 := by exact prefixLift 1140712
  have htrace : WordTrace (prefixWord ++ tailWord_1140712) baseStart_1140712 baseEnd_1140712 := by
    simpa [prefixWord, tailWord_1140712, baseEnd_1140712] using wordTrace_append hprefix tailTrace_1140712
  have hstable : (prefixWord ++ tailWord_1140712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140712).length < 2 ^ (prefixWord ++ tailWord_1140712).sum := by decide
  have hdescent : baseEnd_1140712 < baseStart_1140712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140746 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_1140746 : Nat := 118140960795 + 1140746 * 2 ^ 59
def prefixEnd_1140746 : Nat := 4983230072969 + 3 ^ 40 * 1140746 * 2
def baseEnd_1140746 : Nat := 585751002693899059728811

theorem tailTrace_1140746 : CollatzResearch.WordTrace tailWord_1140746 prefixEnd_1140746 585751002693899059728811 := by
  unfold tailWord_1140746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401606181319885187796523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27737616483519693834124061 10401606181319885187796523)
  ·
    refine ⟨15602409271979827781694785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10401606181319885187796523 15602409271979827781694785)
    ·
      refine ⟨11701806953984870836271089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15602409271979827781694785 11701806953984870836271089)
      ·
        refine ⟨8776355215488653127203317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11701806953984870836271089 8776355215488653127203317)
        ·
          refine ⟨822783301452061230675311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8776355215488653127203317 822783301452061230675311)
          ·
            refine ⟨1234174952178091846012967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822783301452061230675311 1234174952178091846012967)
            ·
              refine ⟨1851262428267137769019451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234174952178091846012967 1851262428267137769019451)
              ·
                refine ⟨2776893642400706653529177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851262428267137769019451 2776893642400706653529177)
                ·
                  refine ⟨2082670231800529990146883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2776893642400706653529177 2082670231800529990146883)
                  ·
                    refine ⟨3124005347700794985220325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2082670231800529990146883 3124005347700794985220325)
                    ·
                      refine ⟨585751002693899059728811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3124005347700794985220325 585751002693899059728811)
                      ·
                        rfl

theorem cell23_1140746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_1140746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140746 prefixEnd_1140746 := by exact prefixLift 1140746
  have htrace : WordTrace (prefixWord ++ tailWord_1140746) baseStart_1140746 baseEnd_1140746 := by
    simpa [prefixWord, tailWord_1140746, baseEnd_1140746] using wordTrace_append hprefix tailTrace_1140746
  have hstable : (prefixWord ++ tailWord_1140746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140746).length < 2 ^ (prefixWord ++ tailWord_1140746).sum := by decide
  have hdescent : baseEnd_1140746 < baseStart_1140746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140769 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 6]
def baseStart_1140769 : Nat := 118140960795 + 1140769 * 2 ^ 59
def prefixEnd_1140769 : Nat := 4983230072969 + 3 ^ 40 * 1140769 * 2
def baseEnd_1140769 : Nat := 65084756972105829971245

theorem tailTrace_1140769 : CollatzResearch.WordTrace tailWord_1140769 prefixEnd_1140769 65084756972105829971245 := by
  unfold tailWord_1140769
  simp only [CollatzResearch.WordTrace]
  refine ⟨41607263604196215679273361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27738175736130810452848907 41607263604196215679273361)
  ·
    refine ⟨31205447703147161759455021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41607263604196215679273361 31205447703147161759455021)
    ·
      refine ⟨11702042888680185659795633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31205447703147161759455021 11702042888680185659795633)
      ·
        refine ⟨8776532166510139244846725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11702042888680185659795633 8776532166510139244846725)
        ·
          refine ⟨1645599781220651108408761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8776532166510139244846725 1645599781220651108408761)
          ·
            refine ⟨1234199835915488331306571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645599781220651108408761 1234199835915488331306571)
            ·
              refine ⟨1851299753873232496959857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234199835915488331306571 1851299753873232496959857)
              ·
                refine ⟨1388474815404924372719893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851299753873232496959857 1388474815404924372719893)
                ·
                  refine ⟨65084756972105829971245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1388474815404924372719893 65084756972105829971245)
                  ·
                    rfl

theorem cell23_1140769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_1140769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140769 prefixEnd_1140769 := by exact prefixLift 1140769
  have htrace : WordTrace (prefixWord ++ tailWord_1140769) baseStart_1140769 baseEnd_1140769 := by
    simpa [prefixWord, tailWord_1140769, baseEnd_1140769] using wordTrace_append hprefix tailTrace_1140769
  have hstable : (prefixWord ++ tailWord_1140769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140769).length < 2 ^ (prefixWord ++ tailWord_1140769).sum := by decide
  have hdescent : baseEnd_1140769 < baseStart_1140769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140805 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_1140805 : Nat := 118140960795 + 1140805 * 2 ^ 59
def prefixEnd_1140805 : Nat := 4983230072969 + 3 ^ 40 * 1140805 * 2
def baseEnd_1140805 : Nat := 585781298052514328891039

theorem tailTrace_1140805 : CollatzResearch.WordTrace tailWord_1140805 prefixEnd_1140805 585781298052514328891039 := by
  unfold tailWord_1140805
  simp only [CollatzResearch.WordTrace]
  refine ⟨41608576632065793827583869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27739051088043862551722579 41608576632065793827583869)
  ·
    refine ⟨15603216237024672685343951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41608576632065793827583869 15603216237024672685343951)
    ·
      refine ⟨23404824355537009028015927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15603216237024672685343951 23404824355537009028015927)
      ·
        refine ⟨35107236533305513542023891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23404824355537009028015927 35107236533305513542023891)
        ·
          refine ⟨52660854799958270313035837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35107236533305513542023891 52660854799958270313035837)
          ·
            refine ⟨19747820549984351367388439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52660854799958270313035837 19747820549984351367388439)
            ·
              refine ⟨29621730824976527051082659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19747820549984351367388439 29621730824976527051082659)
              ·
                refine ⟨44432596237464790576623989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29621730824976527051082659 44432596237464790576623989)
                ·
                  refine ⟨4165555897262324116558499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44432596237464790576623989 4165555897262324116558499)
                  ·
                    refine ⟨6248333845893486174837749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4165555897262324116558499 6248333845893486174837749)
                    ·
                      refine ⟨585781298052514328891039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6248333845893486174837749 585781298052514328891039)
                      ·
                        rfl

theorem cell23_1140805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_1140805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140805 prefixEnd_1140805 := by exact prefixLift 1140805
  have htrace : WordTrace (prefixWord ++ tailWord_1140805) baseStart_1140805 baseEnd_1140805 := by
    simpa [prefixWord, tailWord_1140805, baseEnd_1140805] using wordTrace_append hprefix tailTrace_1140805
  have hstable : (prefixWord ++ tailWord_1140805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140805).length < 2 ^ (prefixWord ++ tailWord_1140805).sum := by decide
  have hdescent : baseEnd_1140805 < baseStart_1140805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140806 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1140806 : Nat := 118140960795 + 1140806 * 2 ^ 59
def prefixEnd_1140806 : Nat := 4983230072969 + 3 ^ 40 * 1140806 * 2
def baseEnd_1140806 : Nat := 585781811533168824978535

theorem tailTrace_1140806 : CollatzResearch.WordTrace tailWord_1140806 prefixEnd_1140806 585781811533168824978535 := by
  unfold tailWord_1140806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300269159533192843699071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27739075403374780665580181 1300269159533192843699071)
  ·
    refine ⟨1950403739299789265548607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1300269159533192843699071 1950403739299789265548607)
    ·
      refine ⟨2925605608949683898322911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950403739299789265548607 2925605608949683898322911)
      ·
        refine ⟨4388408413424525847484367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2925605608949683898322911 4388408413424525847484367)
        ·
          refine ⟨6582612620136788771226551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4388408413424525847484367 6582612620136788771226551)
          ·
            refine ⟨9873918930205183156839827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6582612620136788771226551 9873918930205183156839827)
            ·
              refine ⟨14810878395307774735259741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9873918930205183156839827 14810878395307774735259741)
              ·
                refine ⟨5554079398240415525722403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14810878395307774735259741 5554079398240415525722403)
                ·
                  refine ⟨8331119097360623288583605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5554079398240415525722403 8331119097360623288583605)
                  ·
                    refine ⟨781042415377558433304713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8331119097360623288583605 781042415377558433304713)
                    ·
                      refine ⟨585781811533168824978535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781042415377558433304713 585781811533168824978535)
                      ·
                        rfl

theorem cell23_1140806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1140806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140806 prefixEnd_1140806 := by exact prefixLift 1140806
  have htrace : WordTrace (prefixWord ++ tailWord_1140806) baseStart_1140806 baseEnd_1140806 := by
    simpa [prefixWord, tailWord_1140806, baseEnd_1140806] using wordTrace_append hprefix tailTrace_1140806
  have hstable : (prefixWord ++ tailWord_1140806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140806).length < 2 ^ (prefixWord ++ tailWord_1140806).sum := by decide
  have hdescent : baseEnd_1140806 < baseStart_1140806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140812 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_1140812 : Nat := 118140960795 + 1140812 * 2 ^ 59
def prefixEnd_1140812 : Nat := 4983230072969 + 3 ^ 40 * 1140812 * 2
def baseEnd_1140812 : Nat := 195261630805698600501169

theorem tailTrace_1140812 : CollatzResearch.WordTrace tailWord_1140812 prefixEnd_1140812 195261630805698600501169 := by
  unfold tailWord_1140812
  simp only [CollatzResearch.WordTrace]
  refine ⟨20804415971520217011544345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27739221295360289348725793 20804415971520217011544345)
  ·
    refine ⟨15603311978640162758658259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20804415971520217011544345 15603311978640162758658259)
    ·
      refine ⟨23404967967960244137987389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15603311978640162758658259 23404967967960244137987389)
      ·
        refine ⟨8776862987985091551745271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23404967967960244137987389 8776862987985091551745271)
        ·
          refine ⟨13165294481977637327617907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776862987985091551745271 13165294481977637327617907)
          ·
            refine ⟨19747941722966455991426861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165294481977637327617907 19747941722966455991426861)
            ·
              refine ⟨7405478146112420996785073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19747941722966455991426861 7405478146112420996785073)
              ·
                refine ⟨5554108609584315747588805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7405478146112420996785073 5554108609584315747588805)
                ·
                  refine ⟨1041395364297059202672901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5554108609584315747588805 1041395364297059202672901)
                  ·
                    refine ⟨195261630805698600501169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041395364297059202672901 195261630805698600501169)
                    ·
                      rfl

theorem cell23_1140812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_1140812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140812 prefixEnd_1140812 := by exact prefixLift 1140812
  have htrace : WordTrace (prefixWord ++ tailWord_1140812) baseStart_1140812 baseEnd_1140812 := by
    simpa [prefixWord, tailWord_1140812, baseEnd_1140812] using wordTrace_append hprefix tailTrace_1140812
  have hstable : (prefixWord ++ tailWord_1140812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140812).length < 2 ^ (prefixWord ++ tailWord_1140812).sum := by decide
  have hdescent : baseEnd_1140812 < baseStart_1140812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140836 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_1140836 : Nat := 118140960795 + 1140836 * 2 ^ 59
def prefixEnd_1140836 : Nat := 4983230072969 + 3 ^ 40 * 1140836 * 2
def baseEnd_1140836 : Nat := 585797215952803707603397

theorem tailTrace_1140836 : CollatzResearch.WordTrace tailWord_1140836 prefixEnd_1140836 585797215952803707603397 := by
  unfold tailWord_1140836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20804853647476743060981181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27739804863302324081308241 20804853647476743060981181)
  ·
    refine ⟨7801820117803778647867943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20804853647476743060981181 7801820117803778647867943)
    ·
      refine ⟨11702730176705667971801915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7801820117803778647867943 11702730176705667971801915)
      ·
        refine ⟨17554095265058501957702873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11702730176705667971801915 17554095265058501957702873)
        ·
          refine ⟨13165571448793876468277155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17554095265058501957702873 13165571448793876468277155)
          ·
            refine ⟨19748357173190814702415733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165571448793876468277155 19748357173190814702415733)
            ·
              refine ⟨1851408484986638878351475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19748357173190814702415733 1851408484986638878351475)
              ·
                refine ⟨2777112727479958317527213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851408484986638878351475 2777112727479958317527213)
                ·
                  refine ⟨1041417272804984369072705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2777112727479958317527213 1041417272804984369072705)
                  ·
                    refine ⟨781062954603738276804529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041417272804984369072705 781062954603738276804529)
                    ·
                      refine ⟨585797215952803707603397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781062954603738276804529 585797215952803707603397)
                      ·
                        rfl

theorem cell23_1140836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_1140836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140836 prefixEnd_1140836 := by exact prefixLift 1140836
  have htrace : WordTrace (prefixWord ++ tailWord_1140836) baseStart_1140836 baseEnd_1140836 := by
    simpa [prefixWord, tailWord_1140836, baseEnd_1140836] using wordTrace_append hprefix tailTrace_1140836
  have hstable : (prefixWord ++ tailWord_1140836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140836).length < 2 ^ (prefixWord ++ tailWord_1140836).sum := by decide
  have hdescent : baseEnd_1140836 < baseStart_1140836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140869 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_1140869 : Nat := 118140960795 + 1140869 * 2 ^ 59
def prefixEnd_1140869 : Nat := 4983230072969 + 3 ^ 40 * 1140869 * 2
def baseEnd_1140869 : Nat := 585814160814402078490745

theorem tailTrace_1140869 : CollatzResearch.WordTrace tailWord_1140869 prefixEnd_1140869 585814160814402078490745 := by
  unfold tailWord_1140869
  simp only [CollatzResearch.WordTrace]
  refine ⟨41610910903833932757913661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27740607269222621838609107 41610910903833932757913661)
  ·
    refine ⟨15604091588937724784217623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41610910903833932757913661 15604091588937724784217623)
    ·
      refine ⟨23406137383406587176326435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15604091588937724784217623 23406137383406587176326435)
      ·
        refine ⟨35109206075109880764489653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23406137383406587176326435 35109206075109880764489653)
        ·
          refine ⟨3291488069541551321670905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35109206075109880764489653 3291488069541551321670905)
          ·
            refine ⟨2468616052156163491253179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291488069541551321670905 2468616052156163491253179)
            ·
              refine ⟨3702924078234245236879769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468616052156163491253179 3702924078234245236879769)
              ·
                refine ⟨2777193058675683927659827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3702924078234245236879769 2777193058675683927659827)
                ·
                  refine ⟨4165789588013525891489741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777193058675683927659827 4165789588013525891489741)
                  ·
                    refine ⟨1562171095505072209308653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4165789588013525891489741 1562171095505072209308653)
                    ·
                      refine ⟨585814160814402078490745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1562171095505072209308653 585814160814402078490745)
                      ·
                        rfl

theorem cell23_1140869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_1140869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140869 prefixEnd_1140869 := by exact prefixLift 1140869
  have htrace : WordTrace (prefixWord ++ tailWord_1140869) baseStart_1140869 baseEnd_1140869 := by
    simpa [prefixWord, tailWord_1140869, baseEnd_1140869] using wordTrace_append hprefix tailTrace_1140869
  have hstable : (prefixWord ++ tailWord_1140869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140869).length < 2 ^ (prefixWord ++ tailWord_1140869).sum := by decide
  have hdescent : baseEnd_1140869 < baseStart_1140869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140887 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 1, 2, 2]
def baseStart_1140887 : Nat := 118140960795 + 1140887 * 2 ^ 59
def prefixEnd_1140887 : Nat := 4983230072969 + 3 ^ 40 * 1140887 * 2
def baseEnd_1140887 : Nat := 585823403466183008065663

theorem tailTrace_1140887 : CollatzResearch.WordTrace tailWord_1140887 prefixEnd_1140887 585823403466183008065663 := by
  unfold tailWord_1140887
  simp only [CollatzResearch.WordTrace]
  refine ⟨41611567417768721832068915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27741044945179147888045943 41611567417768721832068915)
  ·
    refine ⟨62417351126653082748103373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41611567417768721832068915 62417351126653082748103373)
    ·
      refine ⟨23406506672494906030538765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62417351126653082748103373 23406506672494906030538765)
      ·
        refine ⟨8777440002185589761452037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23406506672494906030538765 8777440002185589761452037)
        ·
          refine ⟨1645770000409798080272257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8777440002185589761452037 1645770000409798080272257)
          ·
            refine ⟨1234327500307348560204193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645770000409798080272257 1234327500307348560204193)
            ·
              refine ⟨925745625230511420153145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234327500307348560204193 925745625230511420153145)
              ·
                refine ⟨694309218922883565114859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925745625230511420153145 694309218922883565114859)
                ·
                  refine ⟨1041463828384325347672289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694309218922883565114859 1041463828384325347672289)
                  ·
                    refine ⟨781097871288244010754217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041463828384325347672289 781097871288244010754217)
                    ·
                      refine ⟨585823403466183008065663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781097871288244010754217 585823403466183008065663)
                      ·
                        rfl

theorem cell23_1140887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_1140887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140887 prefixEnd_1140887 := by exact prefixLift 1140887
  have htrace : WordTrace (prefixWord ++ tailWord_1140887) baseStart_1140887 baseEnd_1140887 := by
    simpa [prefixWord, tailWord_1140887, baseEnd_1140887] using wordTrace_append hprefix tailTrace_1140887
  have hstable : (prefixWord ++ tailWord_1140887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140887).length < 2 ^ (prefixWord ++ tailWord_1140887).sum := by decide
  have hdescent : baseEnd_1140887 < baseStart_1140887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140892 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1140892 : Nat := 118140960795 + 1140892 * 2 ^ 59
def prefixEnd_1140892 : Nat := 4983230072969 + 3 ^ 40 * 1140892 * 2
def baseEnd_1140892 : Nat := 585825970869455488503139

theorem tailTrace_1140892 : CollatzResearch.WordTrace tailWord_1140892 prefixEnd_1140892 585825970869455488503139 := by
  unfold tailWord_1140892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20805874891375303843000465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27741166521833738457333953 20805874891375303843000465)
  ·
    refine ⟨15604406168531477882250349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20805874891375303843000465 15604406168531477882250349)
    ·
      refine ⟨5851652313199304205843881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15604406168531477882250349 5851652313199304205843881)
      ·
        refine ⟨4388739234899478154382911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5851652313199304205843881 4388739234899478154382911)
        ·
          refine ⟨6583108852349217231574367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4388739234899478154382911 6583108852349217231574367)
          ·
            refine ⟨9874663278523825847361551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6583108852349217231574367 9874663278523825847361551)
            ·
              refine ⟨14811994917785738771042327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9874663278523825847361551 14811994917785738771042327)
              ·
                refine ⟨22217992376678608156563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14811994917785738771042327 22217992376678608156563491)
                ·
                  refine ⟨33326988565017912234845237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22217992376678608156563491 33326988565017912234845237)
                  ·
                    refine ⟨3124405177970429272016741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33326988565017912234845237 3124405177970429272016741)
                    ·
                      refine ⟨585825970869455488503139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3124405177970429272016741 585825970869455488503139)
                      ·
                        rfl

theorem cell23_1140892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1140892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140892 prefixEnd_1140892 := by exact prefixLift 1140892
  have htrace : WordTrace (prefixWord ++ tailWord_1140892) baseStart_1140892 baseEnd_1140892 := by
    simpa [prefixWord, tailWord_1140892, baseEnd_1140892] using wordTrace_append hprefix tailTrace_1140892
  have hstable : (prefixWord ++ tailWord_1140892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140892).length < 2 ^ (prefixWord ++ tailWord_1140892).sum := by decide
  have hdescent : baseEnd_1140892 < baseStart_1140892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140905 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_1140905 : Nat := 118140960795 + 1140905 * 2 ^ 59
def prefixEnd_1140905 : Nat := 4983230072969 + 3 ^ 40 * 1140905 * 2
def baseEnd_1140905 : Nat := 585832646117963937640579

theorem tailTrace_1140905 : CollatzResearch.WordTrace tailWord_1140905 prefixEnd_1140905 585832646117963937640579 := by
  unfold tailWord_1140905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41612223931703510906224169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27741482621135673937482779 41612223931703510906224169)
  ·
    refine ⟨31209167948777633179668127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41612223931703510906224169 31209167948777633179668127)
    ·
      refine ⟨46813751923166449769502191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31209167948777633179668127 46813751923166449769502191)
      ·
        refine ⟨70220627884749674654253287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46813751923166449769502191 70220627884749674654253287)
        ·
          refine ⟨105330941827124511981379931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70220627884749674654253287 105330941827124511981379931)
          ·
            refine ⟨157996412740686767972069897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105330941827124511981379931 157996412740686767972069897)
            ·
              refine ⟨118497309555515075979052423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157996412740686767972069897 118497309555515075979052423)
              ·
                refine ⟨177745964333272613968578635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118497309555515075979052423 177745964333272613968578635)
                ·
                  refine ⟨266618946499908920952867953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177745964333272613968578635 266618946499908920952867953)
                  ·
                    refine ⟨199964209874931690714650965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 266618946499908920952867953 199964209874931690714650965)
                    ·
                      refine ⟨585832646117963937640579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 199964209874931690714650965 585832646117963937640579)
                      ·
                        rfl

theorem cell23_1140905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_1140905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140905 prefixEnd_1140905 := by exact prefixLift 1140905
  have htrace : WordTrace (prefixWord ++ tailWord_1140905) baseStart_1140905 baseEnd_1140905 := by
    simpa [prefixWord, tailWord_1140905, baseEnd_1140905] using wordTrace_append hprefix tailTrace_1140905
  have hstable : (prefixWord ++ tailWord_1140905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140905).length < 2 ^ (prefixWord ++ tailWord_1140905).sum := by decide
  have hdescent : baseEnd_1140905 < baseStart_1140905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140996 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1140996 : Nat := 118140960795 + 1140996 * 2 ^ 59
def prefixEnd_1140996 : Nat := 4983230072969 + 3 ^ 40 * 1140996 * 2
def baseEnd_1140996 : Nat := 195293124285841027200887

theorem tailTrace_1140996 : CollatzResearch.WordTrace tailWord_1140996 prefixEnd_1140996 195293124285841027200887 := by
  unfold tailWord_1140996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807771487186916723893421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27743695316249222298524561 20807771487186916723893421)
  ·
    refine ⟨7802914307695093771460033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20807771487186916723893421 7802914307695093771460033)
    ·
      refine ⟨5852185730771320328595025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7802914307695093771460033 5852185730771320328595025)
      ·
        refine ⟨4389139298078490246446269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5852185730771320328595025 4389139298078490246446269)
        ·
          refine ⟨1645927236779433842417351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4389139298078490246446269 1645927236779433842417351)
          ·
            refine ⟨2468890855169150763626027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645927236779433842417351 2468890855169150763626027)
            ·
              refine ⟨3703336282753726145439041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468890855169150763626027 3703336282753726145439041)
              ·
                refine ⟨2777502212065294609079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3703336282753726145439041 2777502212065294609079281)
                ·
                  refine ⟨2083126659048970956809461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777502212065294609079281 2083126659048970956809461)
                  ·
                    refine ⟨195293124285841027200887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2083126659048970956809461 195293124285841027200887)
                    ·
                      rfl

theorem cell23_1140996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1140996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1140996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1140996 prefixEnd_1140996 := by exact prefixLift 1140996
  have htrace : WordTrace (prefixWord ++ tailWord_1140996) baseStart_1140996 baseEnd_1140996 := by
    simpa [prefixWord, tailWord_1140996, baseEnd_1140996] using wordTrace_append hprefix tailTrace_1140996
  have hstable : (prefixWord ++ tailWord_1140996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140996).length < 2 ^ (prefixWord ++ tailWord_1140996).sum := by decide
  have hdescent : baseEnd_1140996 < baseStart_1140996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141093 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_1141093 : Nat := 118140960795 + 1141093 * 2 ^ 59
def prefixEnd_1141093 : Nat := 4983230072969 + 3 ^ 40 * 1141093 * 2
def baseEnd_1141093 : Nat := 585929180481009202089715

theorem tailTrace_1141093 : CollatzResearch.WordTrace tailWord_1141093 prefixEnd_1141093 585929180481009202089715 := by
  unfold tailWord_1141093
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619080855022419014067933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27746053903348279342711955 41619080855022419014067933)
  ·
    refine ⟨15607155320633407130275475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41619080855022419014067933 15607155320633407130275475)
    ·
      refine ⟨23410732980950110695413213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607155320633407130275475 23410732980950110695413213)
      ·
        refine ⟨8779024867856291510779955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23410732980950110695413213 8779024867856291510779955)
        ·
          refine ⟨13168537301784437266169933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779024867856291510779955 13168537301784437266169933)
          ·
            refine ⟨4938201488169163974813725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13168537301784437266169933 4938201488169163974813725)
            ·
              refine ⟨1851825558063436490555147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4938201488169163974813725 1851825558063436490555147)
              ·
                refine ⟨2777738337095154735832721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851825558063436490555147 2777738337095154735832721)
                ·
                  refine ⟨2083303752821366051874541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2777738337095154735832721 2083303752821366051874541)
                  ·
                    refine ⟨781238907308012269452953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083303752821366051874541 781238907308012269452953)
                    ·
                      refine ⟨585929180481009202089715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781238907308012269452953 585929180481009202089715)
                      ·
                        rfl

theorem cell23_1141093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_1141093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141093 prefixEnd_1141093 := by exact prefixLift 1141093
  have htrace : WordTrace (prefixWord ++ tailWord_1141093) baseStart_1141093 baseEnd_1141093 := by
    simpa [prefixWord, tailWord_1141093, baseEnd_1141093] using wordTrace_append hprefix tailTrace_1141093
  have hstable : (prefixWord ++ tailWord_1141093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141093).length < 2 ^ (prefixWord ++ tailWord_1141093).sum := by decide
  have hdescent : baseEnd_1141093 < baseStart_1141093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141099 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 6, 4]
def baseStart_1141099 : Nat := 118140960795 + 1141099 * 2 ^ 59
def prefixEnd_1141099 : Nat := 4983230072969 + 3 ^ 40 * 1141099 * 2
def baseEnd_1141099 : Nat := 195310753788312059538229

theorem tailTrace_1141099 : CollatzResearch.WordTrace tailWord_1141099 prefixEnd_1141099 195310753788312059538229 := by
  unfold tailWord_1141099
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619299693000682038786351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27746199795333788025857567 41619299693000682038786351)
  ·
    refine ⟨62428949539501023058179527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41619299693000682038786351 62428949539501023058179527)
    ·
      refine ⟨93643424309251534587269291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62428949539501023058179527 93643424309251534587269291)
      ·
        refine ⟨140465136463877301880903937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93643424309251534587269291 140465136463877301880903937)
        ·
          refine ⟨105348852347907976410677953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140465136463877301880903937 105348852347907976410677953)
          ·
            refine ⟨79011639260930982308008465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105348852347907976410677953 79011639260930982308008465)
            ·
              refine ⟨59258729445698236731006349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79011639260930982308008465 59258729445698236731006349)
              ·
                refine ⟨22222023542136838774127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59258729445698236731006349 22222023542136838774127381)
                ·
                  refine ⟨1041657353537664317537221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22222023542136838774127381 1041657353537664317537221)
                  ·
                    refine ⟨195310753788312059538229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041657353537664317537221 195310753788312059538229)
                    ·
                      rfl

theorem cell23_1141099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 4].length) (baseStart_1141099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141099 prefixEnd_1141099 := by exact prefixLift 1141099
  have htrace : WordTrace (prefixWord ++ tailWord_1141099) baseStart_1141099 baseEnd_1141099 := by
    simpa [prefixWord, tailWord_1141099, baseEnd_1141099] using wordTrace_append hprefix tailTrace_1141099
  have hstable : (prefixWord ++ tailWord_1141099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141099).length < 2 ^ (prefixWord ++ tailWord_1141099).sum := by decide
  have hdescent : baseEnd_1141099 < baseStart_1141099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141116 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1141116 : Nat := 118140960795 + 1141116 * 2 ^ 59
def prefixEnd_1141116 : Nat := 4983230072969 + 3 ^ 40 * 1141116 * 2
def baseEnd_1141116 : Nat := 195313663512020870700703

theorem tailTrace_1141116 : CollatzResearch.WordTrace tailWord_1141116 prefixEnd_1141116 195313663512020870700703 := by
  unfold tailWord_1141116
  simp only [CollatzResearch.WordTrace]
  refine ⟨20809959866969546971077601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27746613155959395961436801 20809959866969546971077601)
  ·
    refine ⟨15607469900227160228308201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20809959866969546971077601 15607469900227160228308201)
    ·
      refine ⟨11705602425170370171231151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15607469900227160228308201 11705602425170370171231151)
      ·
        refine ⟨17558403637755555256846727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705602425170370171231151 17558403637755555256846727)
        ·
          refine ⟨26337605456633332885270091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17558403637755555256846727 26337605456633332885270091)
          ·
            refine ⟨39506408184949999327905137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26337605456633332885270091 39506408184949999327905137)
            ·
              refine ⟨29629806138712499495928853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39506408184949999327905137 29629806138712499495928853)
              ·
                refine ⟨1388897162752148413871665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29629806138712499495928853 1388897162752148413871665)
                ·
                  refine ⟨1041672872064111310403749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1388897162752148413871665 1041672872064111310403749)
                  ·
                    refine ⟨195313663512020870700703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041672872064111310403749 195313663512020870700703)
                    ·
                      rfl

theorem cell23_1141116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1141116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141116 prefixEnd_1141116 := by exact prefixLift 1141116
  have htrace : WordTrace (prefixWord ++ tailWord_1141116) baseStart_1141116 baseEnd_1141116 := by
    simpa [prefixWord, tailWord_1141116, baseEnd_1141116] using wordTrace_append hprefix tailTrace_1141116
  have hstable : (prefixWord ++ tailWord_1141116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141116).length < 2 ^ (prefixWord ++ tailWord_1141116).sum := by decide
  have hdescent : baseEnd_1141116 < baseStart_1141116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141140 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1141140 : Nat := 118140960795 + 1141140 * 2 ^ 59
def prefixEnd_1141140 : Nat := 4983230072969 + 3 ^ 40 * 1141140 * 2
def baseEnd_1141140 : Nat := 585953314071770518201999

theorem tailTrace_1141140 : CollatzResearch.WordTrace tailWord_1141140 prefixEnd_1141140 585953314071770518201999 := by
  unfold tailWord_1141140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20810397542926073020514437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27747196723901430694019249 20810397542926073020514437)
  ·
    refine ⟨3901949539298638691346457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20810397542926073020514437 3901949539298638691346457)
    ·
      refine ⟨2926462154473979018509843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3901949539298638691346457 2926462154473979018509843)
      ·
        refine ⟨4389693231710968527764765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926462154473979018509843 4389693231710968527764765)
        ·
          refine ⟨1646134961891613197911787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4389693231710968527764765 1646134961891613197911787)
          ·
            refine ⟨2469202442837419796867681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646134961891613197911787 2469202442837419796867681)
            ·
              refine ⟨1851901832128064847650761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469202442837419796867681 1851901832128064847650761)
              ·
                refine ⟨1388926374096048635738071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851901832128064847650761 1388926374096048635738071)
                ·
                  refine ⟨2083389561144072953607107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388926374096048635738071 2083389561144072953607107)
                  ·
                    refine ⟨3125084341716109430410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2083389561144072953607107 3125084341716109430410661)
                    ·
                      refine ⟨585953314071770518201999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3125084341716109430410661 585953314071770518201999)
                      ·
                        rfl

theorem cell23_1141140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1141140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141140 prefixEnd_1141140 := by exact prefixLift 1141140
  have htrace : WordTrace (prefixWord ++ tailWord_1141140) baseStart_1141140 baseEnd_1141140 := by
    simpa [prefixWord, tailWord_1141140, baseEnd_1141140] using wordTrace_append hprefix tailTrace_1141140
  have hstable : (prefixWord ++ tailWord_1141140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141140).length < 2 ^ (prefixWord ++ tailWord_1141140).sum := by decide
  have hdescent : baseEnd_1141140 < baseStart_1141140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141146 : List Nat := [3, 1, 1, 4, 1, 2, 4, 7]
def baseStart_1141146 : Nat := 118140960795 + 1141146 * 2 ^ 59
def prefixEnd_1141146 : Nat := 4983230072969 + 3 ^ 40 * 1141146 * 2
def baseEnd_1141146 : Nat := 21702088702062870175073

theorem tailTrace_1141146 : CollatzResearch.WordTrace tailWord_1141146 prefixEnd_1141146 21702088702062870175073 := by
  unfold tailWord_1141146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10405253480957602266436823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27747342615886939377164861 10405253480957602266436823)
  ·
    refine ⟨15607880221436403399655235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10405253480957602266436823 15607880221436403399655235)
    ·
      refine ⟨23411820332154605099482853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15607880221436403399655235 23411820332154605099482853)
      ·
        refine ⟨4389716312278988456153035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23411820332154605099482853 4389716312278988456153035)
        ·
          refine ⟨6584574468418482684229553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389716312278988456153035 6584574468418482684229553)
          ·
            refine ⟨4938430851313862013172165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6584574468418482684229553 4938430851313862013172165)
            ·
              refine ⟨925955784621349127469781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4938430851313862013172165 925955784621349127469781)
              ·
                refine ⟨21702088702062870175073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 925955784621349127469781 21702088702062870175073)
                ·
                  rfl

theorem cell23_1141146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_1141146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141146 prefixEnd_1141146 := by exact prefixLift 1141146
  have htrace : WordTrace (prefixWord ++ tailWord_1141146) baseStart_1141146 baseEnd_1141146 := by
    simpa [prefixWord, tailWord_1141146, baseEnd_1141146] using wordTrace_append hprefix tailTrace_1141146
  have hstable : (prefixWord ++ tailWord_1141146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141146).length < 2 ^ (prefixWord ++ tailWord_1141146).sum := by decide
  have hdescent : baseEnd_1141146 < baseStart_1141146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141156 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1141156 : Nat := 118140960795 + 1141156 * 2 ^ 59
def prefixEnd_1141156 : Nat := 4983230072969 + 3 ^ 40 * 1141156 * 2
def baseEnd_1141156 : Nat := 585961529762242455601925

theorem tailTrace_1141156 : CollatzResearch.WordTrace tailWord_1141156 prefixEnd_1141156 585961529762242455601925 := by
  unfold tailWord_1141156
  simp only [CollatzResearch.WordTrace]
  refine ⟨20810689326897090386805661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27747585769196120515740881 20810689326897090386805661)
  ·
    refine ⟨7804008497586408895052123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20810689326897090386805661 7804008497586408895052123)
    ·
      refine ⟨11706012746379613342578185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804008497586408895052123 11706012746379613342578185)
      ·
        refine ⟨8779509559784710006933639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11706012746379613342578185 8779509559784710006933639)
        ·
          refine ⟨13169264339677065010400459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8779509559784710006933639 13169264339677065010400459)
          ·
            refine ⟨19753896509515597515600689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13169264339677065010400459 19753896509515597515600689)
            ·
              refine ⟨14815422382136698136700517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19753896509515597515600689 14815422382136698136700517)
              ·
                refine ⟨2777891696650630900631347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14815422382136698136700517 2777891696650630900631347)
                ·
                  refine ⟨4166837544975946350947021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2777891696650630900631347 4166837544975946350947021)
                  ·
                    refine ⟨1562564079365979881605133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4166837544975946350947021 1562564079365979881605133)
                    ·
                      refine ⟨585961529762242455601925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1562564079365979881605133 585961529762242455601925)
                      ·
                        rfl

theorem cell23_1141156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1141156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141156 prefixEnd_1141156 := by exact prefixLift 1141156
  have htrace : WordTrace (prefixWord ++ tailWord_1141156) baseStart_1141156 baseEnd_1141156 := by
    simpa [prefixWord, tailWord_1141156, baseEnd_1141156] using wordTrace_append hprefix tailTrace_1141156
  have hstable : (prefixWord ++ tailWord_1141156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141156).length < 2 ^ (prefixWord ++ tailWord_1141156).sum := by decide
  have hdescent : baseEnd_1141156 < baseStart_1141156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141160 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1141160 : Nat := 118140960795 + 1141160 * 2 ^ 59
def prefixEnd_1141160 : Nat := 4983230072969 + 3 ^ 40 * 1141160 * 2
def baseEnd_1141160 : Nat := 585963583684860439951907

theorem tailTrace_1141160 : CollatzResearch.WordTrace tailWord_1141160 prefixEnd_1141160 585963583684860439951907 := by
  unfold tailWord_1141160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20810762272889844728378467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27747683030519792971171289 20810762272889844728378467)
  ·
    refine ⟨31216143409334767092567701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20810762272889844728378467 31216143409334767092567701)
    ·
      refine ⟨1463256722312567207464111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31216143409334767092567701 1463256722312567207464111)
      ·
        refine ⟨2194885083468850811196167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463256722312567207464111 2194885083468850811196167)
        ·
          refine ⟨3292327625203276216794251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2194885083468850811196167 3292327625203276216794251)
          ·
            refine ⟨4938491437804914325191377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3292327625203276216794251 4938491437804914325191377)
            ·
              refine ⟨3703868578353685743893533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4938491437804914325191377 3703868578353685743893533)
              ·
                refine ⟨1388950716882632153960075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3703868578353685743893533 1388950716882632153960075)
                ·
                  refine ⟨2083426075323948230940113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1388950716882632153960075 2083426075323948230940113)
                  ·
                    refine ⟨1562569556492961173205085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2083426075323948230940113 1562569556492961173205085)
                    ·
                      refine ⟨585963583684860439951907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1562569556492961173205085 585963583684860439951907)
                      ·
                        rfl

theorem cell23_1141160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1141160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141160 prefixEnd_1141160 := by exact prefixLift 1141160
  have htrace : WordTrace (prefixWord ++ tailWord_1141160) baseStart_1141160 baseEnd_1141160 := by
    simpa [prefixWord, tailWord_1141160, baseEnd_1141160] using wordTrace_append hprefix tailTrace_1141160
  have hstable : (prefixWord ++ tailWord_1141160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141160).length < 2 ^ (prefixWord ++ tailWord_1141160).sum := by decide
  have hdescent : baseEnd_1141160 < baseStart_1141160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141303 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 4, 2]
def baseStart_1141303 : Nat := 118140960795 + 1141303 * 2 ^ 59
def prefixEnd_1141303 : Nat := 4983230072969 + 3 ^ 40 * 1141303 * 2
def baseEnd_1141303 : Nat := 586037011418453380463749

theorem tailTrace_1141303 : CollatzResearch.WordTrace tailWord_1141303 prefixEnd_1141303 586037011418453380463749 := by
  unfold tailWord_1141303
  simp only [CollatzResearch.WordTrace]
  refine ⟨41626740184261624879212563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751160122841083252808375 41626740184261624879212563)
  ·
    refine ⟨62440110276392437318818845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41626740184261624879212563 62440110276392437318818845)
    ·
      refine ⟨23415041353647163994557067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62440110276392437318818845 23415041353647163994557067)
      ·
        refine ⟨35122562030470745991835601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23415041353647163994557067 35122562030470745991835601)
        ·
          refine ⟨26341921522853059493876701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35122562030470745991835601 26341921522853059493876701)
          ·
            refine ⟨9878220571069897310203763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26341921522853059493876701 9878220571069897310203763)
            ·
              refine ⟨14817330856604845965305645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9878220571069897310203763 14817330856604845965305645)
              ·
                refine ⟨5556499071226817236989617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14817330856604845965305645 5556499071226817236989617)
                ·
                  refine ⟨4167374303420112927742213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5556499071226817236989617 4167374303420112927742213)
                  ·
                    refine ⟨781382681891271173951665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167374303420112927742213 781382681891271173951665)
                    ·
                      refine ⟨586037011418453380463749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781382681891271173951665 586037011418453380463749)
                      ·
                        rfl

theorem cell23_1141303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_1141303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141303 prefixEnd_1141303 := by exact prefixLift 1141303
  have htrace : WordTrace (prefixWord ++ tailWord_1141303) baseStart_1141303 baseEnd_1141303 := by
    simpa [prefixWord, tailWord_1141303, baseEnd_1141303] using wordTrace_append hprefix tailTrace_1141303
  have hstable : (prefixWord ++ tailWord_1141303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141303).length < 2 ^ (prefixWord ++ tailWord_1141303).sum := by decide
  have hdescent : baseEnd_1141303 < baseStart_1141303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141326 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_1141326 : Nat := 118140960795 + 1141326 * 2 ^ 59
def prefixEnd_1141326 : Nat := 4983230072969 + 3 ^ 40 * 1141326 * 2
def baseEnd_1141326 : Nat := 65116535719278532275127

theorem tailTrace_1141326 : CollatzResearch.WordTrace tailWord_1141326 prefixEnd_1141326 65116535719278532275127 := by
  unfold tailWord_1141326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203447382897287475912479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27751719375452199871533221 5203447382897287475912479)
  ·
    refine ⟨7805171074345931213868719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5203447382897287475912479 7805171074345931213868719)
    ·
      refine ⟨11707756611518896820803079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7805171074345931213868719 11707756611518896820803079)
      ·
        refine ⟨17561634917278345231204619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707756611518896820803079 17561634917278345231204619)
        ·
          refine ⟨26342452375917517846806929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17561634917278345231204619 26342452375917517846806929)
          ·
            refine ⟨19756839281938138385105197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26342452375917517846806929 19756839281938138385105197)
            ·
              refine ⟨7408814730726801894414449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19756839281938138385105197 7408814730726801894414449)
              ·
                refine ⟨5556611048045101420810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7408814730726801894414449 5556611048045101420810837)
                ·
                  refine ⟨65116535719278532275127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5556611048045101420810837 65116535719278532275127)
                  ·
                    rfl

theorem cell23_1141326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_1141326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141326 prefixEnd_1141326 := by exact prefixLift 1141326
  have htrace : WordTrace (prefixWord ++ tailWord_1141326) baseStart_1141326 baseEnd_1141326 := by
    simpa [prefixWord, tailWord_1141326, baseEnd_1141326] using wordTrace_append hprefix tailTrace_1141326
  have hstable : (prefixWord ++ tailWord_1141326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141326).length < 2 ^ (prefixWord ++ tailWord_1141326).sum := by decide
  have hdescent : baseEnd_1141326 < baseStart_1141326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141347 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 1, 4]
def baseStart_1141347 : Nat := 118140960795 + 1141347 * 2 ^ 59
def prefixEnd_1141347 : Nat := 4983230072969 + 3 ^ 40 * 1141347 * 2
def baseEnd_1141347 : Nat := 195353201522417069437849

theorem tailTrace_1141347 : CollatzResearch.WordTrace tailWord_1141347 prefixEnd_1141347 195353201522417069437849 := by
  unfold tailWord_1141347
  simp only [CollatzResearch.WordTrace]
  refine ⟨41628344996102220393814295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27752229997401480262542863 41628344996102220393814295)
  ·
    refine ⟨62442517494153330590721443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41628344996102220393814295 62442517494153330590721443)
    ·
      refine ⟨93663776241229995886082165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62442517494153330590721443 93663776241229995886082165)
      ·
        refine ⟨8780979022615312114320203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93663776241229995886082165 8780979022615312114320203)
        ·
          refine ⟨13171468533922968171480305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8780979022615312114320203 13171468533922968171480305)
          ·
            refine ⟨9878601400442226128610229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13171468533922968171480305 9878601400442226128610229)
            ·
              refine ⟨926118881291458699557209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9878601400442226128610229 926118881291458699557209)
              ·
                refine ⟨694589160968594024667907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926118881291458699557209 694589160968594024667907)
                ·
                  refine ⟨1041883741452891037001861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694589160968594024667907 1041883741452891037001861)
                  ·
                    refine ⟨195353201522417069437849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1041883741452891037001861 195353201522417069437849)
                    ·
                      rfl

theorem cell23_1141347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 4].length) (baseStart_1141347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141347 prefixEnd_1141347 := by exact prefixLift 1141347
  have htrace : WordTrace (prefixWord ++ tailWord_1141347) baseStart_1141347 baseEnd_1141347 := by
    simpa [prefixWord, tailWord_1141347, baseEnd_1141347] using wordTrace_append hprefix tailTrace_1141347
  have hstable : (prefixWord ++ tailWord_1141347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141347).length < 2 ^ (prefixWord ++ tailWord_1141347).sum := by decide
  have hdescent : baseEnd_1141347 < baseStart_1141347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141363 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 5, 2]
def baseStart_1141363 : Nat := 118140960795 + 1141363 * 2 ^ 59
def prefixEnd_1141363 : Nat := 4983230072969 + 3 ^ 40 * 1141363 * 2
def baseEnd_1141363 : Nat := 586067820257723145713473

theorem tailTrace_1141363 : CollatzResearch.WordTrace tailWord_1141363 prefixEnd_1141363 586067820257723145713473 := by
  unfold tailWord_1141363
  simp only [CollatzResearch.WordTrace]
  refine ⟨41628928564044255126396743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27752619042696170084264495 41628928564044255126396743)
  ·
    refine ⟨62443392846066382689595115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41628928564044255126396743 62443392846066382689595115)
    ·
      refine ⟨93665089269099574034392673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62443392846066382689595115 93665089269099574034392673)
      ·
        refine ⟨70248816951824680525794505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93665089269099574034392673 70248816951824680525794505)
        ·
          refine ⟨52686612713868510394345879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70248816951824680525794505 52686612713868510394345879)
          ·
            refine ⟨79029919070802765591518819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52686612713868510394345879 79029919070802765591518819)
            ·
              refine ⟨118544878606204148387278229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79029919070802765591518819 118544878606204148387278229)
              ·
                refine ⟨5556791184665819455653667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118544878606204148387278229 5556791184665819455653667)
                ·
                  refine ⟨8335186776998729183480501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556791184665819455653667 8335186776998729183480501)
                  ·
                    refine ⟨781423760343630860951297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8335186776998729183480501 781423760343630860951297)
                    ·
                      refine ⟨586067820257723145713473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781423760343630860951297 586067820257723145713473)
                      ·
                        rfl

theorem cell23_1141363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5, 2].length) (baseStart_1141363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141363 prefixEnd_1141363 := by exact prefixLift 1141363
  have htrace : WordTrace (prefixWord ++ tailWord_1141363) baseStart_1141363 baseEnd_1141363 := by
    simpa [prefixWord, tailWord_1141363, baseEnd_1141363] using wordTrace_append hprefix tailTrace_1141363
  have hstable : (prefixWord ++ tailWord_1141363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141363).length < 2 ^ (prefixWord ++ tailWord_1141363).sum := by decide
  have hdescent : baseEnd_1141363 < baseStart_1141363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141393 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_1141393 : Nat := 118140960795 + 1141393 * 2 ^ 59
def prefixEnd_1141393 : Nat := 4983230072969 + 3 ^ 40 * 1141393 * 2
def baseEnd_1141393 : Nat := 586083224677358028338335

theorem tailTrace_1141393 : CollatzResearch.WordTrace tailWord_1141393 prefixEnd_1141393 586083224677358028338335 := by
  unfold tailWord_1141393
  simp only [CollatzResearch.WordTrace]
  refine ⟨41630022753935570249988833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27753348502623713499992555 41630022753935570249988833)
  ·
    refine ⟨31222517065451677687491625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41630022753935570249988833 31222517065451677687491625)
    ·
      refine ⟨23416887799088758265618719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31222517065451677687491625 23416887799088758265618719)
      ·
        refine ⟨35125331698633137398428079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23416887799088758265618719 35125331698633137398428079)
        ·
          refine ⟨52687997547949706097642119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35125331698633137398428079 52687997547949706097642119)
          ·
            refine ⟨79031996321924559146463179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52687997547949706097642119 79031996321924559146463179)
            ·
              refine ⟨118547994482886838719694769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79031996321924559146463179 118547994482886838719694769)
              ·
                refine ⟨88910995862165129039771077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118547994482886838719694769 88910995862165129039771077)
                ·
                  refine ⟨16670811724155961694957077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88910995862165129039771077 16670811724155961694957077)
                  ·
                    refine ⟨781444299569810704451113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16670811724155961694957077 781444299569810704451113)
                    ·
                      refine ⟨586083224677358028338335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781444299569810704451113 586083224677358028338335)
                      ·
                        rfl

theorem cell23_1141393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_1141393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141393 prefixEnd_1141393 := by exact prefixLift 1141393
  have htrace : WordTrace (prefixWord ++ tailWord_1141393) baseStart_1141393 baseEnd_1141393 := by
    simpa [prefixWord, tailWord_1141393, baseEnd_1141393] using wordTrace_append hprefix tailTrace_1141393
  have hstable : (prefixWord ++ tailWord_1141393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141393).length < 2 ^ (prefixWord ++ tailWord_1141393).sum := by decide
  have hdescent : baseEnd_1141393 < baseStart_1141393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141404 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1141404 : Nat := 118140960795 + 1141404 * 2 ^ 59
def prefixEnd_1141404 : Nat := 4983230072969 + 3 ^ 40 * 1141404 * 2
def baseEnd_1141404 : Nat := 586088872964557485300785

theorem tailTrace_1141404 : CollatzResearch.WordTrace tailWord_1141404 prefixEnd_1141404 586088872964557485300785 := by
  unfold tailWord_1141404
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815211978447859564319633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27753615971263812752426177 20815211978447859564319633)
  ·
    refine ⟨15611408983835894673239725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20815211978447859564319633 15611408983835894673239725)
    ·
      refine ⟨5854278368938460502464897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15611408983835894673239725 5854278368938460502464897)
      ·
        refine ⟨4390708776703845376848673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5854278368938460502464897 4390708776703845376848673)
        ·
          refine ⟨3293031582527884032636505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4390708776703845376848673 3293031582527884032636505)
          ·
            refine ⟨2469773686895913024477379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293031582527884032636505 2469773686895913024477379)
            ·
              refine ⟨3704660530343869536716069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469773686895913024477379 3704660530343869536716069)
              ·
                refine ⟨694623849439475538134263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3704660530343869536716069 694623849439475538134263)
                ·
                  refine ⟨1041935774159213307201395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694623849439475538134263 1041935774159213307201395)
                  ·
                    refine ⟨1562903661238819960802093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1041935774159213307201395 1562903661238819960802093)
                    ·
                      refine ⟨586088872964557485300785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1562903661238819960802093 586088872964557485300785)
                      ·
                        rfl

theorem cell23_1141404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1141404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141404 prefixEnd_1141404 := by exact prefixLift 1141404
  have htrace : WordTrace (prefixWord ++ tailWord_1141404) baseStart_1141404 baseEnd_1141404 := by
    simpa [prefixWord, tailWord_1141404, baseEnd_1141404] using wordTrace_append hprefix tailTrace_1141404
  have hstable : (prefixWord ++ tailWord_1141404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141404).length < 2 ^ (prefixWord ++ tailWord_1141404).sum := by decide
  have hdescent : baseEnd_1141404 < baseStart_1141404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141423 : List Nat := [1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_1141423 : Nat := 118140960795 + 1141423 * 2 ^ 59
def prefixEnd_1141423 : Nat := 4983230072969 + 3 ^ 40 * 1141423 * 2
def baseEnd_1141423 : Nat := 586098629096992910963197

theorem tailTrace_1141423 : CollatzResearch.WordTrace tailWord_1141423 prefixEnd_1141423 586098629096992910963197 := by
  unfold tailWord_1141423
  simp only [CollatzResearch.WordTrace]
  refine ⟨41631116943826885373580923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27754077962551256915720615 41631116943826885373580923)
  ·
    refine ⟨62446675415740328060371385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41631116943826885373580923 62446675415740328060371385)
    ·
      refine ⟨46835006561805246045278539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62446675415740328060371385 46835006561805246045278539)
      ·
        refine ⟨70252509842707869067917809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46835006561805246045278539 70252509842707869067917809)
        ·
          refine ⟨52689382382030901800938357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70252509842707869067917809 52689382382030901800938357)
          ·
            refine ⟨4939629598315397043837971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52689382382030901800938357 4939629598315397043837971)
            ·
              refine ⟨7409444397473095565756957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939629598315397043837971 7409444397473095565756957)
              ·
                refine ⟨2778541649052410837158859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7409444397473095565756957 2778541649052410837158859)
                ·
                  refine ⟨4167812473578616255738289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778541649052410837158859 4167812473578616255738289)
                  ·
                    refine ⟨3125859355183962191803717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4167812473578616255738289 3125859355183962191803717)
                    ·
                      refine ⟨586098629096992910963197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3125859355183962191803717 586098629096992910963197)
                      ·
                        rfl

theorem cell23_1141423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_1141423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141423 prefixEnd_1141423 := by exact prefixLift 1141423
  have htrace : WordTrace (prefixWord ++ tailWord_1141423) baseStart_1141423 baseEnd_1141423 := by
    simpa [prefixWord, tailWord_1141423, baseEnd_1141423] using wordTrace_append hprefix tailTrace_1141423
  have hstable : (prefixWord ++ tailWord_1141423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141423).length < 2 ^ (prefixWord ++ tailWord_1141423).sum := by decide
  have hdescent : baseEnd_1141423 < baseStart_1141423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141427 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 3, 2, 2]
def baseStart_1141427 : Nat := 118140960795 + 1141427 * 2 ^ 59
def prefixEnd_1141427 : Nat := 4983230072969 + 3 ^ 40 * 1141427 * 2
def baseEnd_1141427 : Nat := 586100683019610895313179

theorem tailTrace_1141427 : CollatzResearch.WordTrace tailWord_1141427 prefixEnd_1141427 586100683019610895313179 := by
  unfold tailWord_1141427
  simp only [CollatzResearch.WordTrace]
  refine ⟨41631262835812394056726535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27754175223874929371151023 41631262835812394056726535)
  ·
    refine ⟨62446894253718591085089803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41631262835812394056726535 62446894253718591085089803)
    ·
      refine ⟨93670341380577886627634705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62446894253718591085089803 93670341380577886627634705)
      ·
        refine ⟨70252756035433414970726029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93670341380577886627634705 70252756035433414970726029)
        ·
          refine ⟨26344783513287530614022261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70252756035433414970726029 26344783513287530614022261)
          ·
            refine ⟨2469823454370705995064587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26344783513287530614022261 2469823454370705995064587)
            ·
              refine ⟨3704735181556058992596881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469823454370705995064587 3704735181556058992596881)
              ·
                refine ⟨2778551386167044244447661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704735181556058992596881 2778551386167044244447661)
                ·
                  refine ⟨1041956769812641591667873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2778551386167044244447661 1041956769812641591667873)
                  ·
                    refine ⟨781467577359481193750905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041956769812641591667873 781467577359481193750905)
                    ·
                      refine ⟨586100683019610895313179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781467577359481193750905 586100683019610895313179)
                      ·
                        rfl

theorem cell23_1141427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 3, 2, 2].length) (baseStart_1141427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141427 prefixEnd_1141427 := by exact prefixLift 1141427
  have htrace : WordTrace (prefixWord ++ tailWord_1141427) baseStart_1141427 baseEnd_1141427 := by
    simpa [prefixWord, tailWord_1141427, baseEnd_1141427] using wordTrace_append hprefix tailTrace_1141427
  have hstable : (prefixWord ++ tailWord_1141427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141427).length < 2 ^ (prefixWord ++ tailWord_1141427).sum := by decide
  have hdescent : baseEnd_1141427 < baseStart_1141427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141441 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1141441 : Nat := 118140960795 + 1141441 * 2 ^ 59
def prefixEnd_1141441 : Nat := 4983230072969 + 3 ^ 40 * 1141441 * 2
def baseEnd_1141441 : Nat := 195369290582924613512705

theorem tailTrace_1141441 : CollatzResearch.WordTrace tailWord_1141441 prefixEnd_1141441 195369290582924613512705 := by
  unfold tailWord_1141441
  simp only [CollatzResearch.WordTrace]
  refine ⟨41631773457761674447736177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27754515638507782965157451 41631773457761674447736177)
  ·
    refine ⟨31223830093321255835802133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41631773457761674447736177 31223830093321255835802133)
    ·
      refine ⟨1463617035624433867303225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31223830093321255835802133 1463617035624433867303225)
      ·
        refine ⟨1097712776718325400477419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463617035624433867303225 1097712776718325400477419)
        ·
          refine ⟨1646569165077488100716129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097712776718325400477419 1646569165077488100716129)
          ·
            refine ⟨1234926873808116075537097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646569165077488100716129 1234926873808116075537097)
            ·
              refine ⟨926195155356087056652823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234926873808116075537097 926195155356087056652823)
              ·
                refine ⟨1389292733034130584979235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926195155356087056652823 1389292733034130584979235)
                ·
                  refine ⟨2083939099551195877468853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389292733034130584979235 2083939099551195877468853)
                  ·
                    refine ⟨195369290582924613512705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2083939099551195877468853 195369290582924613512705)
                    ·
                      rfl

theorem cell23_1141441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1141441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141441 prefixEnd_1141441 := by exact prefixLift 1141441
  have htrace : WordTrace (prefixWord ++ tailWord_1141441) baseStart_1141441 baseEnd_1141441 := by
    simpa [prefixWord, tailWord_1141441, baseEnd_1141441] using wordTrace_append hprefix tailTrace_1141441
  have hstable : (prefixWord ++ tailWord_1141441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141441).length < 2 ^ (prefixWord ++ tailWord_1141441).sum := by decide
  have hdescent : baseEnd_1141441 < baseStart_1141441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141444 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1141444 : Nat := 118140960795 + 1141444 * 2 ^ 59
def prefixEnd_1141444 : Nat := 4983230072969 + 3 ^ 40 * 1141444 * 2
def baseEnd_1141444 : Nat := 586109412190737328800601

theorem tailTrace_1141444 : CollatzResearch.WordTrace tailWord_1141444 prefixEnd_1141444 586109412190737328800601 := by
  unfold tailWord_1141444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815941438375402980047693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27754588584500537306730257 20815941438375402980047693)
  ·
    refine ⟨7805978039390776117517885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20815941438375402980047693 7805978039390776117517885)
    ·
      refine ⟨2927241764771541044069207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7805978039390776117517885 2927241764771541044069207)
      ·
        refine ⟨4390862647157311566103811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927241764771541044069207 4390862647157311566103811)
        ·
          refine ⟨6586293970735967349155717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390862647157311566103811 6586293970735967349155717)
          ·
            refine ⟨1234930119512993877966697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6586293970735967349155717 1234930119512993877966697)
            ·
              refine ⟨926197589634745408475023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1234930119512993877966697 926197589634745408475023)
              ·
                refine ⟨1389296384452118112712535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926197589634745408475023 1389296384452118112712535)
                ·
                  refine ⟨2083944576678177169068803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389296384452118112712535 2083944576678177169068803)
                  ·
                    refine ⟨3125916865017265753603205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2083944576678177169068803 3125916865017265753603205)
                    ·
                      refine ⟨586109412190737328800601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3125916865017265753603205 586109412190737328800601)
                      ·
                        rfl

theorem cell23_1141444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1141444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141444 prefixEnd_1141444 := by exact prefixLift 1141444
  have htrace : WordTrace (prefixWord ++ tailWord_1141444) baseStart_1141444 baseEnd_1141444 := by
    simpa [prefixWord, tailWord_1141444, baseEnd_1141444] using wordTrace_append hprefix tailTrace_1141444
  have hstable : (prefixWord ++ tailWord_1141444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141444).length < 2 ^ (prefixWord ++ tailWord_1141444).sum := by decide
  have hdescent : baseEnd_1141444 < baseStart_1141444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141461 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1141461 : Nat := 118140960795 + 1141461 * 2 ^ 59
def prefixEnd_1141461 : Nat := 4983230072969 + 3 ^ 40 * 1141461 * 2
def baseEnd_1141461 : Nat := 586118141361863762288023

theorem tailTrace_1141461 : CollatzResearch.WordTrace tailWord_1141461 prefixEnd_1141461 586118141361863762288023 := by
  unfold tailWord_1141461
  simp only [CollatzResearch.WordTrace]
  refine ⟨41632502917689217863464237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27755001945126145242309491 41632502917689217863464237)
  ·
    refine ⟨15612188594133456698799089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41632502917689217863464237 15612188594133456698799089)
    ·
      refine ⟨11709141445600092524099317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15612188594133456698799089 11709141445600092524099317)
      ·
        refine ⟨1097732010525008674134311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11709141445600092524099317 1097732010525008674134311)
        ·
          refine ⟨1646598015787513011201467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097732010525008674134311 1646598015787513011201467)
          ·
            refine ⟨2469897023681269516802201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646598015787513011201467 2469897023681269516802201)
            ·
              refine ⟨1852422767760952137601651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469897023681269516802201 1852422767760952137601651)
              ·
                refine ⟨2778634151641428206402477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852422767760952137601651 2778634151641428206402477)
                ·
                  refine ⟨1041987806865535577400929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2778634151641428206402477 1041987806865535577400929)
                  ·
                    refine ⟨781490855149151683050697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1041987806865535577400929 781490855149151683050697)
                    ·
                      refine ⟨586118141361863762288023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781490855149151683050697 586118141361863762288023)
                      ·
                        rfl

theorem cell23_1141461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1141461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141461 prefixEnd_1141461 := by exact prefixLift 1141461
  have htrace : WordTrace (prefixWord ++ tailWord_1141461) baseStart_1141461 baseEnd_1141461 := by
    simpa [prefixWord, tailWord_1141461, baseEnd_1141461] using wordTrace_append hprefix tailTrace_1141461
  have hstable : (prefixWord ++ tailWord_1141461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141461).length < 2 ^ (prefixWord ++ tailWord_1141461).sum := by decide
  have hdescent : baseEnd_1141461 < baseStart_1141461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141477 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1141477 : Nat := 118140960795 + 1141477 * 2 ^ 59
def prefixEnd_1141477 : Nat := 4983230072969 + 3 ^ 40 * 1141477 * 2
def baseEnd_1141477 : Nat := 586126357052335699687949

theorem tailTrace_1141477 : CollatzResearch.WordTrace tailWord_1141477 prefixEnd_1141477 586126357052335699687949 := by
  unfold tailWord_1141477
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633086485631252596046685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27755390990420835064031123 41633086485631252596046685)
  ·
    refine ⟨15612407432111719723517507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41633086485631252596046685 15612407432111719723517507)
    ·
      refine ⟨23418611148167579585276261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15612407432111719723517507 23418611148167579585276261)
      ·
        refine ⟨4390989590281421172239299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23418611148167579585276261 4390989590281421172239299)
        ·
          refine ⟨6586484385422131758358949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390989590281421172239299 6586484385422131758358949)
          ·
            refine ⟨1234965822266649704692303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6586484385422131758358949 1234965822266649704692303)
            ·
              refine ⟨1852448733399974557038455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234965822266649704692303 1852448733399974557038455)
              ·
                refine ⟨2778673100099961835557683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852448733399974557038455 2778673100099961835557683)
                ·
                  refine ⟨4168009650149942753336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778673100099961835557683 4168009650149942753336525)
                  ·
                    refine ⟨1563003618806228532501197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4168009650149942753336525 1563003618806228532501197)
                    ·
                      refine ⟨586126357052335699687949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563003618806228532501197 586126357052335699687949)
                      ·
                        rfl

theorem cell23_1141477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1141477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141477 prefixEnd_1141477 := by exact prefixLift 1141477
  have htrace : WordTrace (prefixWord ++ tailWord_1141477) baseStart_1141477 baseEnd_1141477 := by
    simpa [prefixWord, tailWord_1141477, baseEnd_1141477] using wordTrace_append hprefix tailTrace_1141477
  have hstable : (prefixWord ++ tailWord_1141477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141477).length < 2 ^ (prefixWord ++ tailWord_1141477).sum := by decide
  have hdescent : baseEnd_1141477 < baseStart_1141477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141487 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 1, 3, 2]
def baseStart_1141487 : Nat := 118140960795 + 1141487 * 2 ^ 59
def prefixEnd_1141487 : Nat := 4983230072969 + 3 ^ 40 * 1141487 * 2
def baseEnd_1141487 : Nat := 586131491858880660562903

theorem tailTrace_1141487 : CollatzResearch.WordTrace tailWord_1141487 prefixEnd_1141487 586131491858880660562903 := by
  unfold tailWord_1141487
  simp only [CollatzResearch.WordTrace]
  refine ⟨41633451215595024303910715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27755634143730016202607143 41633451215595024303910715)
  ·
    refine ⟨62450176823392536455866073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41633451215595024303910715 62450176823392536455866073)
    ·
      refine ⟨46837632617544402341899555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62450176823392536455866073 46837632617544402341899555)
      ·
        refine ⟨70256448926316603512849333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46837632617544402341899555 70256448926316603512849333)
        ·
          refine ⟨6586542086842181579329625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70256448926316603512849333 6586542086842181579329625)
          ·
            refine ⟨4939906565131636184497219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6586542086842181579329625 4939906565131636184497219)
            ·
              refine ⟨7409859847697454276745829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939906565131636184497219 7409859847697454276745829)
              ·
                refine ⟨1389348721443272676889843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7409859847697454276745829 1389348721443272676889843)
                ·
                  refine ⟨2084023082164909015334765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389348721443272676889843 2084023082164909015334765)
                  ·
                    refine ⟨781508655811840880750537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084023082164909015334765 781508655811840880750537)
                    ·
                      refine ⟨586131491858880660562903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781508655811840880750537 586131491858880660562903)
                      ·
                        rfl

theorem cell23_1141487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 3, 2].length) (baseStart_1141487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141487 prefixEnd_1141487 := by exact prefixLift 1141487
  have htrace : WordTrace (prefixWord ++ tailWord_1141487) baseStart_1141487 baseEnd_1141487 := by
    simpa [prefixWord, tailWord_1141487, baseEnd_1141487] using wordTrace_append hprefix tailTrace_1141487
  have hstable : (prefixWord ++ tailWord_1141487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141487).length < 2 ^ (prefixWord ++ tailWord_1141487).sum := by decide
  have hdescent : baseEnd_1141487 < baseStart_1141487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141503 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3]
def baseStart_1141503 : Nat := 118140960795 + 1141503 * 2 ^ 59
def prefixEnd_1141503 : Nat := 4983230072969 + 3 ^ 40 * 1141503 * 2
def baseEnd_1141503 : Nat := 586139707549352597962829

theorem tailTrace_1141503 : CollatzResearch.WordTrace tailWord_1141503 prefixEnd_1141503 586139707549352597962829 := by
  unfold tailWord_1141503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41634034783537059036493163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27756023189024706024328775 41634034783537059036493163)
  ·
    refine ⟨62451052175305588554739745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41634034783537059036493163 62451052175305588554739745)
    ·
      refine ⟨46838289131479191416054809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62451052175305588554739745 46838289131479191416054809)
      ·
        refine ⟨35128716848609393562041107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46838289131479191416054809 35128716848609393562041107)
        ·
          refine ⟨52693075272914090343061661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35128716848609393562041107 52693075272914090343061661)
          ·
            refine ⟨19759903227342783878648123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52693075272914090343061661 19759903227342783878648123)
            ·
              refine ⟨29639854841014175817972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19759903227342783878648123 29639854841014175817972185)
              ·
                refine ⟨22229891130760631863479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29639854841014175817972185 22229891130760631863479139)
                ·
                  refine ⟨33344836696140947795218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22229891130760631863479139 33344836696140947795218709)
                  ·
                    refine ⟨1563039220131606927900877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33344836696140947795218709 1563039220131606927900877)
                    ·
                      refine ⟨586139707549352597962829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563039220131606927900877 586139707549352597962829)
                      ·
                        rfl

theorem cell23_1141503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_1141503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141503 prefixEnd_1141503 := by exact prefixLift 1141503
  have htrace : WordTrace (prefixWord ++ tailWord_1141503) baseStart_1141503 baseEnd_1141503 := by
    simpa [prefixWord, tailWord_1141503, baseEnd_1141503] using wordTrace_append hprefix tailTrace_1141503
  have hstable : (prefixWord ++ tailWord_1141503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141503).length < 2 ^ (prefixWord ++ tailWord_1141503).sum := by decide
  have hdescent : baseEnd_1141503 < baseStart_1141503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141513 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_1141513 : Nat := 118140960795 + 1141513 * 2 ^ 59
def prefixEnd_1141513 : Nat := 4983230072969 + 3 ^ 40 * 1141513 * 2
def baseEnd_1141513 : Nat := 586144842355897558837783

theorem tailTrace_1141513 : CollatzResearch.WordTrace tailWord_1141513 prefixEnd_1141513 586144842355897558837783 := by
  unfold tailWord_1141513
  simp only [CollatzResearch.WordTrace]
  refine ⟨41634399513500830744357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27756266342333887162904795 41634399513500830744357193)
  ·
    refine ⟨31225799635125623058267895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41634399513500830744357193 31225799635125623058267895)
    ·
      refine ⟨46838699452688434587401843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31225799635125623058267895 46838699452688434587401843)
      ·
        refine ⟨70258049179032651881102765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46838699452688434587401843 70258049179032651881102765)
        ·
          refine ⟨26346768442137244455413537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70258049179032651881102765 26346768442137244455413537)
          ·
            refine ⟨19760076331602933341560153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26346768442137244455413537 19760076331602933341560153)
            ·
              refine ⟨14820057248702200006170115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19760076331602933341560153 14820057248702200006170115)
              ·
                refine ⟨22230085873053300009255173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14820057248702200006170115 22230085873053300009255173)
                ·
                  refine ⟨4168141101197493751735345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22230085873053300009255173 4168141101197493751735345)
                  ·
                    refine ⟨3126105825898120313801509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4168141101197493751735345 3126105825898120313801509)
                    ·
                      refine ⟨586144842355897558837783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3126105825898120313801509 586144842355897558837783)
                      ·
                        rfl

theorem cell23_1141513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_1141513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141513 prefixEnd_1141513 := by exact prefixLift 1141513
  have htrace : WordTrace (prefixWord ++ tailWord_1141513) baseStart_1141513 baseEnd_1141513 := by
    simpa [prefixWord, tailWord_1141513, baseEnd_1141513] using wordTrace_append hprefix tailTrace_1141513
  have hstable : (prefixWord ++ tailWord_1141513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141513).length < 2 ^ (prefixWord ++ tailWord_1141513).sum := by decide
  have hdescent : baseEnd_1141513 < baseStart_1141513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141580 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1141580 : Nat := 118140960795 + 1141580 * 2 ^ 59
def prefixEnd_1141580 : Nat := 4983230072969 + 3 ^ 40 * 1141580 * 2
def baseEnd_1141580 : Nat := 586179245559748796699975

theorem tailTrace_1141580 : CollatzResearch.WordTrace tailWord_1141580 prefixEnd_1141580 586179245559748796699975 := by
  unfold tailWord_1141580
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818421602129050593523097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27757895469505400791364129 20818421602129050593523097)
  ·
    refine ⟨15613816201596787945142323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20818421602129050593523097 15613816201596787945142323)
    ·
      refine ⟨23420724302395181917713485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15613816201596787945142323 23420724302395181917713485)
      ·
        refine ⟨8782771613398193219142557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23420724302395181917713485 8782771613398193219142557)
        ·
          refine ⟨3293539355024322457178459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8782771613398193219142557 3293539355024322457178459)
          ·
            refine ⟨4940309032536483685767689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293539355024322457178459 4940309032536483685767689)
            ·
              refine ⟨3705231774402362764325767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940309032536483685767689 3705231774402362764325767)
              ·
                refine ⟨5557847661603544146488651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705231774402362764325767 5557847661603544146488651)
                ·
                  refine ⟨8336771492405316219732977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557847661603544146488651 8336771492405316219732977)
                  ·
                    refine ⟨6252578619303987164799733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8336771492405316219732977 6252578619303987164799733)
                    ·
                      refine ⟨586179245559748796699975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6252578619303987164799733 586179245559748796699975)
                      ·
                        rfl

theorem cell23_1141580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1141580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141580 prefixEnd_1141580 := by exact prefixLift 1141580
  have htrace : WordTrace (prefixWord ++ tailWord_1141580) baseStart_1141580 baseEnd_1141580 := by
    simpa [prefixWord, tailWord_1141580, baseEnd_1141580] using wordTrace_append hprefix tailTrace_1141580
  have hstable : (prefixWord ++ tailWord_1141580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141580).length < 2 ^ (prefixWord ++ tailWord_1141580).sum := by decide
  have hdescent : baseEnd_1141580 < baseStart_1141580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141607 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1141607 : Nat := 118140960795 + 1141607 * 2 ^ 59
def prefixEnd_1141607 : Nat := 4983230072969 + 3 ^ 40 * 1141607 * 2
def baseEnd_1141607 : Nat := 586193109537420191062351

theorem tailTrace_1141607 : CollatzResearch.WordTrace tailWord_1141607 prefixEnd_1141607 586193109537420191062351 := by
  unfold tailWord_1141607
  simp only [CollatzResearch.WordTrace]
  refine ⟨41637827975160284798279075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27758551983440189865519383 41637827975160284798279075)
  ·
    refine ⟨62456741962740427197418613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41637827975160284798279075 62456741962740427197418613)
    ·
      refine ⟨5855319559006915049757995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62456741962740427197418613 5855319559006915049757995)
      ·
        refine ⟨8782979338510372574636993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855319559006915049757995 8782979338510372574636993)
        ·
          refine ⟨6587234503882779430977745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8782979338510372574636993 6587234503882779430977745)
          ·
            refine ⟨4940425877912084573233309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587234503882779430977745 4940425877912084573233309)
            ·
              refine ⟨1852659704217031714962491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4940425877912084573233309 1852659704217031714962491)
              ·
                refine ⟨2778989556325547572443737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852659704217031714962491 2778989556325547572443737)
                ·
                  refine ⟨2084242167244160679332803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778989556325547572443737 2084242167244160679332803)
                  ·
                    refine ⟨3126363250866241018999205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2084242167244160679332803 3126363250866241018999205)
                    ·
                      refine ⟨586193109537420191062351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3126363250866241018999205 586193109537420191062351)
                      ·
                        rfl

theorem cell23_1141607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1141607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141607 prefixEnd_1141607 := by exact prefixLift 1141607
  have htrace : WordTrace (prefixWord ++ tailWord_1141607) baseStart_1141607 baseEnd_1141607 := by
    simpa [prefixWord, tailWord_1141607, baseEnd_1141607] using wordTrace_append hprefix tailTrace_1141607
  have hstable : (prefixWord ++ tailWord_1141607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141607).length < 2 ^ (prefixWord ++ tailWord_1141607).sum := by decide
  have hdescent : baseEnd_1141607 < baseStart_1141607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141667 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 5, 2]
def baseStart_1141667 : Nat := 118140960795 + 1141667 * 2 ^ 59
def prefixEnd_1141667 : Nat := 4983230072969 + 3 ^ 40 * 1141667 * 2
def baseEnd_1141667 : Nat := 586223918376689956312075

theorem tailTrace_1141667 : CollatzResearch.WordTrace tailWord_1141667 prefixEnd_1141667 586223918376689956312075 := by
  unfold tailWord_1141667
  simp only [CollatzResearch.WordTrace]
  refine ⟨41640016354942915045463255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27760010903295276696975503 41640016354942915045463255)
  ·
    refine ⟨62460024532414372568194883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41640016354942915045463255 62460024532414372568194883)
    ·
      refine ⟨93690036798621558852292325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62460024532414372568194883 93690036798621558852292325)
      ·
        refine ⟨17566881899741542284804811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93690036798621558852292325 17566881899741542284804811)
        ·
          refine ⟨26350322849612313427207217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17566881899741542284804811 26350322849612313427207217)
          ·
            refine ⟨19762742137209235070405413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26350322849612313427207217 19762742137209235070405413)
            ·
              refine ⟨3705514150726731575701015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19762742137209235070405413 3705514150726731575701015)
              ·
                refine ⟨5558271226090097363551523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705514150726731575701015 5558271226090097363551523)
                ·
                  refine ⟨8337406839135146045327285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5558271226090097363551523 8337406839135146045327285)
                  ·
                    refine ⟨781631891168919941749433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8337406839135146045327285 781631891168919941749433)
                    ·
                      refine ⟨586223918376689956312075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781631891168919941749433 586223918376689956312075)
                      ·
                        rfl

theorem cell23_1141667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_1141667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141667 prefixEnd_1141667 := by exact prefixLift 1141667
  have htrace : WordTrace (prefixWord ++ tailWord_1141667) baseStart_1141667 baseEnd_1141667 := by
    simpa [prefixWord, tailWord_1141667, baseEnd_1141667] using wordTrace_append hprefix tailTrace_1141667
  have hstable : (prefixWord ++ tailWord_1141667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141667).length < 2 ^ (prefixWord ++ tailWord_1141667).sum := by decide
  have hdescent : baseEnd_1141667 < baseStart_1141667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141714 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1141714 : Nat := 118140960795 + 1141714 * 2 ^ 59
def prefixEnd_1141714 : Nat := 4983230072969 + 3 ^ 40 * 1141714 * 2
def baseEnd_1141714 : Nat := 586248051967451272424359

theorem tailTrace_1141714 : CollatzResearch.WordTrace tailWord_1141714 prefixEnd_1141714 586248051967451272424359 := by
  unfold tailWord_1141714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410432646443160518106049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27761153723848428048282797 10410432646443160518106049)
  ·
    refine ⟨7807824484832370388579537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10410432646443160518106049 7807824484832370388579537)
    ·
      refine ⟨5855868363624277791434653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7807824484832370388579537 5855868363624277791434653)
      ·
        refine ⟨2195950636359104171787995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5855868363624277791434653 2195950636359104171787995)
        ·
          refine ⟨3293925954538656257681993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195950636359104171787995 3293925954538656257681993)
          ·
            refine ⟨2470444465903992193261495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293925954538656257681993 2470444465903992193261495)
            ·
              refine ⟨3705666698855988289892243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470444465903992193261495 3705666698855988289892243)
              ·
                refine ⟨5558500048283982434838365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705666698855988289892243 5558500048283982434838365)
                ·
                  refine ⟨2084437518106493413064387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5558500048283982434838365 2084437518106493413064387)
                  ·
                    refine ⟨3126656277159740119596581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2084437518106493413064387 3126656277159740119596581)
                    ·
                      refine ⟨586248051967451272424359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3126656277159740119596581 586248051967451272424359)
                      ·
                        rfl

theorem cell23_1141714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1141714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141714 prefixEnd_1141714 := by exact prefixLift 1141714
  have htrace : WordTrace (prefixWord ++ tailWord_1141714) baseStart_1141714 baseEnd_1141714 := by
    simpa [prefixWord, tailWord_1141714, baseEnd_1141714] using wordTrace_append hprefix tailTrace_1141714
  have hstable : (prefixWord ++ tailWord_1141714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141714).length < 2 ^ (prefixWord ++ tailWord_1141714).sum := by decide
  have hdescent : baseEnd_1141714 < baseStart_1141714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141718 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1141718 : Nat := 118140960795 + 1141718 * 2 ^ 59
def prefixEnd_1141718 : Nat := 4983230072969 + 3 ^ 40 * 1141718 * 2
def baseEnd_1141718 : Nat := 586250105890069256774341

theorem tailTrace_1141718 : CollatzResearch.WordTrace tailWord_1141718 prefixEnd_1141718 586250105890069256774341 := by
  unfold tailWord_1141718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602617279859884422223113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27761250985172100503713205 2602617279859884422223113)
  ·
    refine ⟨1951962959894913316667335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2602617279859884422223113 1951962959894913316667335)
    ·
      refine ⟨2927944439842369975001003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951962959894913316667335 2927944439842369975001003)
      ·
        refine ⟨4391916659763554962501505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927944439842369975001003 4391916659763554962501505)
        ·
          refine ⟨3293937494822666221876129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4391916659763554962501505 3293937494822666221876129)
          ·
            refine ⟨2470453121116999666407097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293937494822666221876129 2470453121116999666407097)
            ·
              refine ⟨1852839840837749749805323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470453121116999666407097 1852839840837749749805323)
              ·
                refine ⟨2779259761256624624707985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852839840837749749805323 2779259761256624624707985)
                ·
                  refine ⟨2084444820942468468530989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779259761256624624707985 2084444820942468468530989)
                  ·
                    refine ⟨781666807853425675699121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084444820942468468530989 781666807853425675699121)
                    ·
                      refine ⟨586250105890069256774341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781666807853425675699121 586250105890069256774341)
                      ·
                        rfl

theorem cell23_1141718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1141718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141718 prefixEnd_1141718 := by exact prefixLift 1141718
  have htrace : WordTrace (prefixWord ++ tailWord_1141718) baseStart_1141718 baseEnd_1141718 := by
    simpa [prefixWord, tailWord_1141718, baseEnd_1141718] using wordTrace_append hprefix tailTrace_1141718
  have hstable : (prefixWord ++ tailWord_1141718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141718).length < 2 ^ (prefixWord ++ tailWord_1141718).sum := by decide
  have hdescent : baseEnd_1141718 < baseStart_1141718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141720 : List Nat := [2, 1, 2, 2, 2, 3, 2, 9]
def baseStart_1141720 : Nat := 118140960795 + 1141720 * 2 ^ 59
def prefixEnd_1141720 : Nat := 4983230072969 + 3 ^ 40 * 1141720 * 2
def baseEnd_1141720 : Nat := 21713004920421416627753

theorem tailTrace_1141720 : CollatzResearch.WordTrace tailWord_1141720 prefixEnd_1141720 21713004920421416627753 := by
  unfold tailWord_1141720
  simp only [CollatzResearch.WordTrace]
  refine ⟨20820974711875452548571307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27761299615833936731428409 20820974711875452548571307)
  ·
    refine ⟨31231462067813178822856961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20820974711875452548571307 31231462067813178822856961)
    ·
      refine ⟨23423596550859884117142721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31231462067813178822856961 23423596550859884117142721)
      ·
        refine ⟨17567697413144913087857041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23423596550859884117142721 17567697413144913087857041)
        ·
          refine ⟨13175773059858684815892781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17567697413144913087857041 13175773059858684815892781)
          ·
            refine ⟨4940914897447006805959793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13175773059858684815892781 4940914897447006805959793)
            ·
              refine ⟨3705686173085255104469845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940914897447006805959793 3705686173085255104469845)
              ·
                refine ⟨21713004920421416627753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3705686173085255104469845 21713004920421416627753)
                ·
                  rfl

theorem cell23_1141720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 9].length) (baseStart_1141720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141720 prefixEnd_1141720 := by exact prefixLift 1141720
  have htrace : WordTrace (prefixWord ++ tailWord_1141720) baseStart_1141720 baseEnd_1141720 := by
    simpa [prefixWord, tailWord_1141720, baseEnd_1141720] using wordTrace_append hprefix tailTrace_1141720
  have hstable : (prefixWord ++ tailWord_1141720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141720).length < 2 ^ (prefixWord ++ tailWord_1141720).sum := by decide
  have hdescent : baseEnd_1141720 < baseStart_1141720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141742 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_1141742 : Nat := 118140960795 + 1141742 * 2 ^ 59
def prefixEnd_1141742 : Nat := 4983230072969 + 3 ^ 40 * 1141742 * 2
def baseEnd_1141742 : Nat := 586262429425777162874231

theorem tailTrace_1141742 : CollatzResearch.WordTrace tailWord_1141742 prefixEnd_1141742 586262429425777162874231 := by
  unfold tailWord_1141742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205343978708900356805435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27761834553114135236295653 5205343978708900356805435)
  ·
    refine ⟨7808015968063350535208153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5205343978708900356805435 7808015968063350535208153)
    ·
      refine ⟨5856011976047512901406115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7808015968063350535208153 5856011976047512901406115)
      ·
        refine ⟨8784017964071269352109173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856011976047512901406115 8784017964071269352109173)
        ·
          refine ⟨823501684131681501760235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8784017964071269352109173 823501684131681501760235)
          ·
            refine ⟨1235252526197522252640353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823501684131681501760235 1235252526197522252640353)
            ·
              refine ⟨926439394648141689480265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235252526197522252640353 926439394648141689480265)
              ·
                refine ⟨694829545986106267110199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926439394648141689480265 694829545986106267110199)
                ·
                  refine ⟨1042244318979159400665299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694829545986106267110199 1042244318979159400665299)
                  ·
                    refine ⟨1563366478468739100997949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1042244318979159400665299 1563366478468739100997949)
                    ·
                      refine ⟨586262429425777162874231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563366478468739100997949 586262429425777162874231)
                      ·
                        rfl

theorem cell23_1141742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_1141742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141742 prefixEnd_1141742 := by exact prefixLift 1141742
  have htrace : WordTrace (prefixWord ++ tailWord_1141742) baseStart_1141742 baseEnd_1141742 := by
    simpa [prefixWord, tailWord_1141742, baseEnd_1141742] using wordTrace_append hprefix tailTrace_1141742
  have hstable : (prefixWord ++ tailWord_1141742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141742).length < 2 ^ (prefixWord ++ tailWord_1141742).sum := by decide
  have hdescent : baseEnd_1141742 < baseStart_1141742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141787 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 8, 2]
def baseStart_1141787 : Nat := 118140960795 + 1141787 * 2 ^ 59
def prefixEnd_1141787 : Nat := 4983230072969 + 3 ^ 40 * 1141787 * 2
def baseEnd_1141787 : Nat := 586285536055229486811523

theorem tailTrace_1141787 : CollatzResearch.WordTrace tailWord_1141787 prefixEnd_1141787 586285536055229486811523 := by
  unfold tailWord_1141787
  simp only [CollatzResearch.WordTrace]
  refine ⟨41644393114508175539831615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27762928743005450359887743 41644393114508175539831615)
  ·
    refine ⟨62466589671762263309747423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41644393114508175539831615 62466589671762263309747423)
    ·
      refine ⟨93699884507643394964621135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62466589671762263309747423 93699884507643394964621135)
      ·
        refine ⟨140549826761465092446931703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93699884507643394964621135 140549826761465092446931703)
        ·
          refine ⟨210824740142197638670397555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140549826761465092446931703 210824740142197638670397555)
          ·
            refine ⟨316237110213296458005596333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210824740142197638670397555 316237110213296458005596333)
            ·
              refine ⟨118588916329986171752098625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316237110213296458005596333 118588916329986171752098625)
              ·
                refine ⟨88941687247489628814073969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118588916329986171752098625 88941687247489628814073969)
                ·
                  refine ⟨66706265435617221610555477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88941687247489628814073969 66706265435617221610555477)
                  ·
                    refine ⟨781714048073639315748697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66706265435617221610555477 781714048073639315748697)
                    ·
                      refine ⟨586285536055229486811523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781714048073639315748697 586285536055229486811523)
                      ·
                        rfl

theorem cell23_1141787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8, 2].length) (baseStart_1141787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141787 prefixEnd_1141787 := by exact prefixLift 1141787
  have htrace : WordTrace (prefixWord ++ tailWord_1141787) baseStart_1141787 baseEnd_1141787 := by
    simpa [prefixWord, tailWord_1141787, baseEnd_1141787] using wordTrace_append hprefix tailTrace_1141787
  have hstable : (prefixWord ++ tailWord_1141787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141787).length < 2 ^ (prefixWord ++ tailWord_1141787).sum := by decide
  have hdescent : baseEnd_1141787 < baseStart_1141787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141791 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 1, 3, 2]
def baseStart_1141791 : Nat := 118140960795 + 1141791 * 2 ^ 59
def prefixEnd_1141791 : Nat := 4983230072969 + 3 ^ 40 * 1141791 * 2
def baseEnd_1141791 : Nat := 586287589977847471161505

theorem tailTrace_1141791 : CollatzResearch.WordTrace tailWord_1141791 prefixEnd_1141791 586287589977847471161505 := by
  unfold tailWord_1141791
  simp only [CollatzResearch.WordTrace]
  refine ⟨41644539006493684222977227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27763026004329122815318151 41644539006493684222977227)
  ·
    refine ⟨62466808509740526334465841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41644539006493684222977227 62466808509740526334465841)
    ·
      refine ⟨46850106382305394750849381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62466808509740526334465841 46850106382305394750849381)
      ·
        refine ⟨8784394946682261515784259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46850106382305394750849381 8784394946682261515784259)
        ·
          refine ⟨13176592420023392273676389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784394946682261515784259 13176592420023392273676389)
          ·
            refine ⟨2470611078754386051314323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13176592420023392273676389 2470611078754386051314323)
            ·
              refine ⟨3705916618131579076971485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470611078754386051314323 3705916618131579076971485)
              ·
                refine ⟨1389718731799342153864307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3705916618131579076971485 1389718731799342153864307)
                ·
                  refine ⟨2084578097699013230796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389718731799342153864307 2084578097699013230796461)
                  ·
                    refine ⟨781716786637129961548673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084578097699013230796461 781716786637129961548673)
                    ·
                      refine ⟨586287589977847471161505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781716786637129961548673 586287589977847471161505)
                      ·
                        rfl

theorem cell23_1141791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_1141791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141791 prefixEnd_1141791 := by exact prefixLift 1141791
  have htrace : WordTrace (prefixWord ++ tailWord_1141791) baseStart_1141791 baseEnd_1141791 := by
    simpa [prefixWord, tailWord_1141791, baseEnd_1141791] using wordTrace_append hprefix tailTrace_1141791
  have hstable : (prefixWord ++ tailWord_1141791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141791).length < 2 ^ (prefixWord ++ tailWord_1141791).sum := by decide
  have hdescent : baseEnd_1141791 < baseStart_1141791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141814 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1141814 : Nat := 118140960795 + 1141814 * 2 ^ 59
def prefixEnd_1141814 : Nat := 4983230072969 + 3 ^ 40 * 1141814 * 2
def baseEnd_1141814 : Nat := 195433133344300293724633

theorem tailTrace_1141814 : CollatzResearch.WordTrace tailWord_1141814 prefixEnd_1141814 195433133344300293724633 := by
  unfold tailWord_1141814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602836117838147446941531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27763585256940239434042997 2602836117838147446941531)
  ·
    refine ⟨3904254176757221170412297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602836117838147446941531 3904254176757221170412297)
    ·
      refine ⟨2928190632567915877809223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3904254176757221170412297 2928190632567915877809223)
      ·
        refine ⟨4392285948851873816713835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928190632567915877809223 4392285948851873816713835)
        ·
          refine ⟨6588428923277810725070753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392285948851873816713835 6588428923277810725070753)
          ·
            refine ⟨4941321692458358043803065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6588428923277810725070753 4941321692458358043803065)
            ·
              refine ⟨3705991269343768532852299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4941321692458358043803065 3705991269343768532852299)
              ·
                refine ⟨5558986904015652799278449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705991269343768532852299 5558986904015652799278449)
                ·
                  refine ⟨4169240178011739599458837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558986904015652799278449 4169240178011739599458837)
                  ·
                    refine ⟨195433133344300293724633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4169240178011739599458837 195433133344300293724633)
                    ·
                      rfl

theorem cell23_1141814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1141814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141814 prefixEnd_1141814 := by exact prefixLift 1141814
  have htrace : WordTrace (prefixWord ++ tailWord_1141814) baseStart_1141814 baseEnd_1141814 := by
    simpa [prefixWord, tailWord_1141814, baseEnd_1141814] using wordTrace_append hprefix tailTrace_1141814
  have hstable : (prefixWord ++ tailWord_1141814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141814).length < 2 ^ (prefixWord ++ tailWord_1141814).sum := by decide
  have hdescent : baseEnd_1141814 < baseStart_1141814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141821 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1141821 : Nat := 118140960795 + 1141821 * 2 ^ 59
def prefixEnd_1141821 : Nat := 4983230072969 + 3 ^ 40 * 1141821 * 2
def baseEnd_1141821 : Nat := 586302994397482353786367

theorem tailTrace_1141821 : CollatzResearch.WordTrace tailWord_1141821 prefixEnd_1141821 586302994397482353786367 := by
  unfold tailWord_1141821
  simp only [CollatzResearch.WordTrace]
  refine ⟨41645633196384999346569317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27763755464256666231046211 41645633196384999346569317)
  ·
    refine ⟨7808556224322187377481747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41645633196384999346569317 7808556224322187377481747)
    ·
      refine ⟨11712834336483281066222621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7808556224322187377481747 11712834336483281066222621)
      ·
        refine ⟨4392312876181230399833483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11712834336483281066222621 4392312876181230399833483)
        ·
          refine ⟨6588469314271845599750225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4392312876181230399833483 6588469314271845599750225)
          ·
            refine ⟨4941351985703884199812669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6588469314271845599750225 4941351985703884199812669)
            ·
              refine ⟨1853006994638956574929751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4941351985703884199812669 1853006994638956574929751)
              ·
                refine ⟨2779510491958434862394627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853006994638956574929751 2779510491958434862394627)
                ·
                  refine ⟨4169265737937652293591941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779510491958434862394627 4169265737937652293591941)
                  ·
                    refine ⟨781737325863309805048489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169265737937652293591941 781737325863309805048489)
                    ·
                      refine ⟨586302994397482353786367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 781737325863309805048489 586302994397482353786367)
                      ·
                        rfl

theorem cell23_1141821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1141821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141821 prefixEnd_1141821 := by exact prefixLift 1141821
  have htrace : WordTrace (prefixWord ++ tailWord_1141821) baseStart_1141821 baseEnd_1141821 := by
    simpa [prefixWord, tailWord_1141821, baseEnd_1141821] using wordTrace_append hprefix tailTrace_1141821
  have hstable : (prefixWord ++ tailWord_1141821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141821).length < 2 ^ (prefixWord ++ tailWord_1141821).sum := by decide
  have hdescent : baseEnd_1141821 < baseStart_1141821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141857 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1141857 : Nat := 118140960795 + 1141857 * 2 ^ 59
def prefixEnd_1141857 : Nat := 4983230072969 + 3 ^ 40 * 1141857 * 2
def baseEnd_1141857 : Nat := 195440493233681404312067

theorem tailTrace_1141857 : CollatzResearch.WordTrace tailWord_1141857 prefixEnd_1141857 195440493233681404312067 := by
  unfold tailWord_1141857
  simp only [CollatzResearch.WordTrace]
  refine ⟨41646946224254577494879825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27764630816169718329919883 41646946224254577494879825)
  ·
    refine ⟨31235209668190933121159869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41646946224254577494879825 31235209668190933121159869)
    ·
      refine ⟨11713203625571599920434951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31235209668190933121159869 11713203625571599920434951)
      ·
        refine ⟨17569805438357399880652427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713203625571599920434951 17569805438357399880652427)
        ·
          refine ⟨26354708157536099820978641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17569805438357399880652427 26354708157536099820978641)
          ·
            refine ⟨19766031118152074865733981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26354708157536099820978641 19766031118152074865733981)
            ·
              refine ⟨7412261669307028074650243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19766031118152074865733981 7412261669307028074650243)
              ·
                refine ⟨11118392503960542111975365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7412261669307028074650243 11118392503960542111975365)
                ·
                  refine ⟨2084698594492601645995381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11118392503960542111975365 2084698594492601645995381)
                  ·
                    refine ⟨195440493233681404312067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2084698594492601645995381 195440493233681404312067)
                    ·
                      rfl

theorem cell23_1141857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1141857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141857 prefixEnd_1141857 := by exact prefixLift 1141857
  have htrace : WordTrace (prefixWord ++ tailWord_1141857) baseStart_1141857 baseEnd_1141857 := by
    simpa [prefixWord, tailWord_1141857, baseEnd_1141857] using wordTrace_append hprefix tailTrace_1141857
  have hstable : (prefixWord ++ tailWord_1141857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141857).length < 2 ^ (prefixWord ++ tailWord_1141857).sum := by decide
  have hdescent : baseEnd_1141857 < baseStart_1141857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141861 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 5]
def baseStart_1141861 : Nat := 118140960795 + 1141861 * 2 ^ 59
def prefixEnd_1141861 : Nat := 4983230072969 + 3 ^ 40 * 1141861 * 2
def baseEnd_1141861 : Nat := 65147059291518021920687

theorem tailTrace_1141861 : CollatzResearch.WordTrace tailWord_1141861 prefixEnd_1141861 65147059291518021920687 := by
  unfold tailWord_1141861
  simp only [CollatzResearch.WordTrace]
  refine ⟨41647092116240086178025437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27764728077493390785350291 41647092116240086178025437)
  ·
    refine ⟨15617659543590032316759539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41647092116240086178025437 15617659543590032316759539)
    ·
      refine ⟨23426489315385048475139309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15617659543590032316759539 23426489315385048475139309)
      ·
        refine ⟨8784933493269393178177241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23426489315385048475139309 8784933493269393178177241)
        ·
          refine ⟨6588700119952044883632931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8784933493269393178177241 6588700119952044883632931)
          ·
            refine ⟨9883050179928067325449397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6588700119952044883632931 9883050179928067325449397)
            ·
              refine ⟨926535954368256311760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9883050179928067325449397 926535954368256311760881)
              ·
                refine ⟨694901965776192233820661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926535954368256311760881 694901965776192233820661)
                ·
                  refine ⟨65147059291518021920687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 694901965776192233820661 65147059291518021920687)
                  ·
                    rfl

theorem cell23_1141861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_1141861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141861 prefixEnd_1141861 := by exact prefixLift 1141861
  have htrace : WordTrace (prefixWord ++ tailWord_1141861) baseStart_1141861 baseEnd_1141861 := by
    simpa [prefixWord, tailWord_1141861, baseEnd_1141861] using wordTrace_append hprefix tailTrace_1141861
  have hstable : (prefixWord ++ tailWord_1141861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141861).length < 2 ^ (prefixWord ++ tailWord_1141861).sum := by decide
  have hdescent : baseEnd_1141861 < baseStart_1141861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141942 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1141942 : Nat := 118140960795 + 1141942 * 2 ^ 59
def prefixEnd_1141942 : Nat := 4983230072969 + 3 ^ 40 * 1141942 * 2
def baseEnd_1141942 : Nat := 195455041852225460124437

theorem tailTrace_1141942 : CollatzResearch.WordTrace tailWord_1141942 prefixEnd_1141942 195455041852225460124437 := by
  unfold tailWord_1141942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603127901809164813232755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27766697619297758007816053 2603127901809164813232755)
  ·
    refine ⟨3904691852713747219849133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2603127901809164813232755 3904691852713747219849133)
    ·
      refine ⟨1464259444767655207443425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3904691852713747219849133 1464259444767655207443425)
      ·
        refine ⟨1098194583575741405582569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1464259444767655207443425 1098194583575741405582569)
        ·
          refine ⟨823645937681806054186927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1098194583575741405582569 823645937681806054186927)
          ·
            refine ⟨1235468906522709081280391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823645937681806054186927 1235468906522709081280391)
            ·
              refine ⟨1853203359784063621920587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235468906522709081280391 1853203359784063621920587)
              ·
                refine ⟨2779805039676095432880881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853203359784063621920587 2779805039676095432880881)
                ·
                  refine ⟨2084853779757071574660661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779805039676095432880881 2084853779757071574660661)
                  ·
                    refine ⟨195455041852225460124437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2084853779757071574660661 195455041852225460124437)
                    ·
                      rfl

theorem cell23_1141942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1141942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141942 prefixEnd_1141942 := by exact prefixLift 1141942
  have htrace : WordTrace (prefixWord ++ tailWord_1141942) baseStart_1141942 baseEnd_1141942 := by
    simpa [prefixWord, tailWord_1141942, baseEnd_1141942] using wordTrace_append hprefix tailTrace_1141942
  have hstable : (prefixWord ++ tailWord_1141942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141942).length < 2 ^ (prefixWord ++ tailWord_1141942).sum := by decide
  have hdescent : baseEnd_1141942 < baseStart_1141942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141948 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1141948 : Nat := 118140960795 + 1141948 * 2 ^ 59
def prefixEnd_1141948 : Nat := 4983230072969 + 3 ^ 40 * 1141948 * 2
def baseEnd_1141948 : Nat := 586368206440603356898283

theorem tailTrace_1141948 : CollatzResearch.WordTrace tailWord_1141948 prefixEnd_1141948 586368206440603356898283 := by
  unfold tailWord_1141948
  simp only [CollatzResearch.WordTrace]
  refine ⟨20825132633462450018221249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27766843511283266690961665 20825132633462450018221249)
  ·
    refine ⟨15618849475096837513665937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20825132633462450018221249 15618849475096837513665937)
    ·
      refine ⟨11714137106322628135249453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15618849475096837513665937 11714137106322628135249453)
      ·
        refine ⟨4392801414870985550718545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11714137106322628135249453 4392801414870985550718545)
        ·
          refine ⟨3294601061153239163038909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4392801414870985550718545 3294601061153239163038909)
          ·
            refine ⟨1235475397932464686139591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3294601061153239163038909 1235475397932464686139591)
            ·
              refine ⟨1853213096898697029209387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235475397932464686139591 1853213096898697029209387)
              ·
                refine ⟨2779819645348045543814081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853213096898697029209387 2779819645348045543814081)
                ·
                  refine ⟨2084864734011034157860561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779819645348045543814081 2084864734011034157860561)
                  ·
                    refine ⟨1563648550508275618395421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084864734011034157860561 1563648550508275618395421)
                    ·
                      refine ⟨586368206440603356898283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563648550508275618395421 586368206440603356898283)
                      ·
                        rfl

theorem cell23_1141948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1141948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141948 prefixEnd_1141948 := by exact prefixLift 1141948
  have htrace : WordTrace (prefixWord ++ tailWord_1141948) baseStart_1141948 baseEnd_1141948 := by
    simpa [prefixWord, tailWord_1141948, baseEnd_1141948] using wordTrace_append hprefix tailTrace_1141948
  have hstable : (prefixWord ++ tailWord_1141948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141948).length < 2 ^ (prefixWord ++ tailWord_1141948).sum := by decide
  have hdescent : baseEnd_1141948 < baseStart_1141948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141957 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_1141957 : Nat := 118140960795 + 1141957 * 2 ^ 59
def prefixEnd_1141957 : Nat := 4983230072969 + 3 ^ 40 * 1141957 * 2
def baseEnd_1141957 : Nat := 586372827766493821685741

theorem tailTrace_1141957 : CollatzResearch.WordTrace tailWord_1141957 prefixEnd_1141957 586372827766493821685741 := by
  unfold tailWord_1141957
  simp only [CollatzResearch.WordTrace]
  refine ⟨41650593523892294573520125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27767062349261529715680083 41650593523892294573520125)
  ·
    refine ⟨15618972571459610465070047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41650593523892294573520125 15618972571459610465070047)
    ·
      refine ⟨23428458857189415697605071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15618972571459610465070047 23428458857189415697605071)
      ·
        refine ⟨35142688285784123546407607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23428458857189415697605071 35142688285784123546407607)
        ·
          refine ⟨52714032428676185319611411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35142688285784123546407607 52714032428676185319611411)
          ·
            refine ⟨79071048643014277979417117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52714032428676185319611411 79071048643014277979417117)
            ·
              refine ⟨29651643241130354242281419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79071048643014277979417117 29651643241130354242281419)
              ·
                refine ⟨44477464861695531363422129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29651643241130354242281419 44477464861695531363422129)
                ·
                  refine ⟨33358098646271648522566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44477464861695531363422129 33358098646271648522566597)
                  ·
                    refine ⟨6254643496175934097981237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33358098646271648522566597 6254643496175934097981237)
                    ·
                      refine ⟨586372827766493821685741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6254643496175934097981237 586372827766493821685741)
                      ·
                        rfl

theorem cell23_1141957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_1141957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1141957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1141957 prefixEnd_1141957 := by exact prefixLift 1141957
  have htrace : WordTrace (prefixWord ++ tailWord_1141957) baseStart_1141957 baseEnd_1141957 := by
    simpa [prefixWord, tailWord_1141957, baseEnd_1141957] using wordTrace_append hprefix tailTrace_1141957
  have hstable : (prefixWord ++ tailWord_1141957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141957).length < 2 ^ (prefixWord ++ tailWord_1141957).sum := by decide
  have hdescent : baseEnd_1141957 < baseStart_1141957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142007 : List Nat := [1, 1, 3, 1, 1, 1, 2, 13]
def baseStart_1142007 : Nat := 118140960795 + 1142007 * 2 ^ 59
def prefixEnd_1142007 : Nat := 4983230072969 + 3 ^ 40 * 1142007 * 2
def baseEnd_1142007 : Nat := 21718463029600689854093

theorem tailTrace_1142007 : CollatzResearch.WordTrace tailWord_1142007 prefixEnd_1142007 21718463029600689854093 := by
  unfold tailWord_1142007
  simp only [CollatzResearch.WordTrace]
  refine ⟨41652417173711153112840275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27768278115807435408560183 41652417173711153112840275)
  ·
    refine ⟨62478625760566729669260413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41652417173711153112840275 62478625760566729669260413)
    ·
      refine ⟨23429484660212523625972655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62478625760566729669260413 23429484660212523625972655)
      ·
        refine ⟨35144226990318785438958983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23429484660212523625972655 35144226990318785438958983)
        ·
          refine ⟨52716340485478178158438475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35144226990318785438958983 52716340485478178158438475)
          ·
            refine ⟨79074510728217267237657713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52716340485478178158438475 79074510728217267237657713)
            ·
              refine ⟨59305883046162950428243285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79074510728217267237657713 59305883046162950428243285)
              ·
                refine ⟨21718463029600689854093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 59305883046162950428243285 21718463029600689854093)
                ·
                  rfl

theorem cell23_1142007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 13].length) (baseStart_1142007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142007 prefixEnd_1142007 := by exact prefixLift 1142007
  have htrace : WordTrace (prefixWord ++ tailWord_1142007) baseStart_1142007 baseEnd_1142007 := by
    simpa [prefixWord, tailWord_1142007, baseEnd_1142007] using wordTrace_append hprefix tailTrace_1142007
  have hstable : (prefixWord ++ tailWord_1142007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142007).length < 2 ^ (prefixWord ++ tailWord_1142007).sum := by decide
  have hdescent : baseEnd_1142007 < baseStart_1142007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142012 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_1142012 : Nat := 118140960795 + 1142012 * 2 ^ 59
def prefixEnd_1142012 : Nat := 4983230072969 + 3 ^ 40 * 1142012 * 2
def baseEnd_1142012 : Nat := 586401069202491106497989

theorem tailTrace_1142012 : CollatzResearch.WordTrace tailWord_1142012 prefixEnd_1142012 586401069202491106497989 := by
  unfold tailWord_1142012
  simp only [CollatzResearch.WordTrace]
  refine ⟨20826299769346519483386145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27768399692462025977848193 20826299769346519483386145)
  ·
    refine ⟨15619724827009889612539609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20826299769346519483386145 15619724827009889612539609)
    ·
      refine ⟨11714793620257417209404707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15619724827009889612539609 11714793620257417209404707)
      ·
        refine ⟨17572190430386125814107061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11714793620257417209404707 17572190430386125814107061)
        ·
          refine ⟨1647392852848699295072537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17572190430386125814107061 1647392852848699295072537)
          ·
            refine ⟨1235544639636524471304403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647392852848699295072537 1235544639636524471304403)
            ·
              refine ⟨1853316959454786706956605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235544639636524471304403 1853316959454786706956605)
              ·
                refine ⟨694993859795545015108727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1853316959454786706956605 694993859795545015108727)
                ·
                  refine ⟨1042490789693317522663091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 694993859795545015108727 1042490789693317522663091)
                  ·
                    refine ⟨1563736184539976283994637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1042490789693317522663091 1563736184539976283994637)
                    ·
                      refine ⟨586401069202491106497989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563736184539976283994637 586401069202491106497989)
                      ·
                        rfl

theorem cell23_1142012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_1142012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142012 prefixEnd_1142012 := by exact prefixLift 1142012
  have htrace : WordTrace (prefixWord ++ tailWord_1142012) baseStart_1142012 baseEnd_1142012 := by
    simpa [prefixWord, tailWord_1142012, baseEnd_1142012] using wordTrace_append hprefix tailTrace_1142012
  have hstable : (prefixWord ++ tailWord_1142012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142012).length < 2 ^ (prefixWord ++ tailWord_1142012).sum := by decide
  have hdescent : baseEnd_1142012 < baseStart_1142012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142021 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_1142021 : Nat := 118140960795 + 1142021 * 2 ^ 59
def prefixEnd_1142021 : Nat := 4983230072969 + 3 ^ 40 * 1142021 * 2
def baseEnd_1142021 : Nat := 586405690528381571285447

theorem tailTrace_1142021 : CollatzResearch.WordTrace tailWord_1142021 prefixEnd_1142021 586405690528381571285447 := by
  unfold tailWord_1142021
  simp only [CollatzResearch.WordTrace]
  refine ⟨41652927795660433503849917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27768618530440289002566611 41652927795660433503849917)
  ·
    refine ⟨15619847923372662563943719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41652927795660433503849917 15619847923372662563943719)
    ·
      refine ⟨23429771885058993845915579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15619847923372662563943719 23429771885058993845915579)
      ·
        refine ⟨35144657827588490768873369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23429771885058993845915579 35144657827588490768873369)
        ·
          refine ⟨26358493370691368076655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35144657827588490768873369 26358493370691368076655027)
          ·
            refine ⟨39537740056037052114982541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26358493370691368076655027 39537740056037052114982541)
            ·
              refine ⟨14826652521013894543118453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39537740056037052114982541 14826652521013894543118453)
              ·
                refine ⟨1389998673845052613417355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14826652521013894543118453 1389998673845052613417355)
                ·
                  refine ⟨2084998010767578920126033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389998673845052613417355 2084998010767578920126033)
                  ·
                    refine ⟨1563748508075684190094525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2084998010767578920126033 1563748508075684190094525)
                    ·
                      refine ⟨586405690528381571285447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563748508075684190094525 586405690528381571285447)
                      ·
                        rfl

theorem cell23_1142021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_1142021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142021 prefixEnd_1142021 := by exact prefixLift 1142021
  have htrace : WordTrace (prefixWord ++ tailWord_1142021) baseStart_1142021 baseEnd_1142021 := by
    simpa [prefixWord, tailWord_1142021, baseEnd_1142021] using wordTrace_append hprefix tailTrace_1142021
  have hstable : (prefixWord ++ tailWord_1142021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142021).length < 2 ^ (prefixWord ++ tailWord_1142021).sum := by decide
  have hdescent : baseEnd_1142021 < baseStart_1142021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142045 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1142045 : Nat := 118140960795 + 1142045 * 2 ^ 59
def prefixEnd_1142045 : Nat := 4983230072969 + 3 ^ 40 * 1142045 * 2
def baseEnd_1142045 : Nat := 195472671354696492461779

theorem tailTrace_1142045 : CollatzResearch.WordTrace tailWord_1142045 prefixEnd_1142045 195472671354696492461779 := by
  unfold tailWord_1142045
  simp only [CollatzResearch.WordTrace]
  refine ⟨41653803147573485602723589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27769202098382323735149059 41653803147573485602723589)
  ·
    refine ⟨7810088090170028550510673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41653803147573485602723589 7810088090170028550510673)
    ·
      refine ⟨5857566067627521412883005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7810088090170028550510673 5857566067627521412883005)
      ·
        refine ⟨2196587275360320529831127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5857566067627521412883005 2196587275360320529831127)
        ·
          refine ⟨3294880913040480794746691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196587275360320529831127 3294880913040480794746691)
          ·
            refine ⟨4942321369560721192120037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294880913040480794746691 4942321369560721192120037)
            ·
              refine ⟨926685256792635223522507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4942321369560721192120037 926685256792635223522507)
              ·
                refine ⟨1390027885188952835283761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926685256792635223522507 1390027885188952835283761)
                ·
                  refine ⟨1042520913891714626462821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390027885188952835283761 1042520913891714626462821)
                  ·
                    refine ⟨195472671354696492461779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042520913891714626462821 195472671354696492461779)
                    ·
                      rfl

theorem cell23_1142045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1142045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142045 prefixEnd_1142045 := by exact prefixLift 1142045
  have htrace : WordTrace (prefixWord ++ tailWord_1142045) baseStart_1142045 baseEnd_1142045 := by
    simpa [prefixWord, tailWord_1142045, baseEnd_1142045] using wordTrace_append hprefix tailTrace_1142045
  have hstable : (prefixWord ++ tailWord_1142045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142045).length < 2 ^ (prefixWord ++ tailWord_1142045).sum := by decide
  have hdescent : baseEnd_1142045 < baseStart_1142045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142068 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1142068 : Nat := 118140960795 + 1142068 * 2 ^ 59
def prefixEnd_1142068 : Nat := 4983230072969 + 3 ^ 40 * 1142068 * 2
def baseEnd_1142068 : Nat := 586429824119142887397731

theorem tailTrace_1142068 : CollatzResearch.WordTrace tailWord_1142068 prefixEnd_1142068 586429824119142887397731 := by
  unfold tailWord_1142068
  simp only [CollatzResearch.WordTrace]
  refine ⟨20827321013245080265405429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27769761350993440353873905 20827321013245080265405429)
  ·
    refine ⟨1952561344991726274881759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20827321013245080265405429 1952561344991726274881759)
    ·
      refine ⟨2928842017487589412322639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952561344991726274881759 2928842017487589412322639)
      ·
        refine ⟨4393263026231384118483959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2928842017487589412322639 4393263026231384118483959)
        ·
          refine ⟨6589894539347076177725939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4393263026231384118483959 6589894539347076177725939)
          ·
            refine ⟨9884841809020614266588909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6589894539347076177725939 9884841809020614266588909)
            ·
              refine ⟨3706815678382730349970841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9884841809020614266588909 3706815678382730349970841)
              ·
                refine ⟨2780111758787047762478131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706815678382730349970841 2780111758787047762478131)
                ·
                  refine ⟨4170167638180571643717197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780111758787047762478131 4170167638180571643717197)
                  ·
                    refine ⟨1563812864317714366393949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4170167638180571643717197 1563812864317714366393949)
                    ·
                      refine ⟨586429824119142887397731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563812864317714366393949 586429824119142887397731)
                      ·
                        rfl

theorem cell23_1142068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1142068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142068 prefixEnd_1142068 := by exact prefixLift 1142068
  have htrace : WordTrace (prefixWord ++ tailWord_1142068) baseStart_1142068 baseEnd_1142068 := by
    simpa [prefixWord, tailWord_1142068, baseEnd_1142068] using wordTrace_append hprefix tailTrace_1142068
  have hstable : (prefixWord ++ tailWord_1142068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142068).length < 2 ^ (prefixWord ++ tailWord_1142068).sum := by decide
  have hdescent : baseEnd_1142068 < baseStart_1142068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142101 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1142101 : Nat := 118140960795 + 1142101 * 2 ^ 59
def prefixEnd_1142101 : Nat := 4983230072969 + 3 ^ 40 * 1142101 * 2
def baseEnd_1142101 : Nat := 195482256326913752761693

theorem tailTrace_1142101 : CollatzResearch.WordTrace tailWord_1142101 prefixEnd_1142101 195482256326913752761693 := by
  unfold tailWord_1142101
  simp only [CollatzResearch.WordTrace]
  refine ⟨41655845635370607166762157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27770563756913738111174771 41655845635370607166762157)
  ·
    refine ⟨15620942113263977687535809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41655845635370607166762157 15620942113263977687535809)
    ·
      refine ⟨11715706584947983265651857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15620942113263977687535809 11715706584947983265651857)
      ·
        refine ⟨8786779938710987449238893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11715706584947983265651857 8786779938710987449238893)
        ·
          refine ⟨3295042477016620293464585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8786779938710987449238893 3295042477016620293464585)
          ·
            refine ⟨2471281857762465220098439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295042477016620293464585 2471281857762465220098439)
            ·
              refine ⟨3706922786643697830147659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471281857762465220098439 3706922786643697830147659)
              ·
                refine ⟨5560384179965546745221489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3706922786643697830147659 5560384179965546745221489)
                ·
                  refine ⟨4170288134974160058916117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5560384179965546745221489 4170288134974160058916117)
                  ·
                    refine ⟨195482256326913752761693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4170288134974160058916117 195482256326913752761693)
                    ·
                      rfl

theorem cell23_1142101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1142101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142101 prefixEnd_1142101 := by exact prefixLift 1142101
  have htrace : WordTrace (prefixWord ++ tailWord_1142101) baseStart_1142101 baseEnd_1142101 := by
    simpa [prefixWord, tailWord_1142101, baseEnd_1142101] using wordTrace_append hprefix tailTrace_1142101
  have hstable : (prefixWord ++ tailWord_1142101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142101).length < 2 ^ (prefixWord ++ tailWord_1142101).sum := by decide
  have hdescent : baseEnd_1142101 < baseStart_1142101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142141 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1142141 : Nat := 118140960795 + 1142141 * 2 ^ 59
def prefixEnd_1142141 : Nat := 4983230072969 + 3 ^ 40 * 1142141 * 2
def baseEnd_1142141 : Nat := 586467308206921101784895

theorem tailTrace_1142141 : CollatzResearch.WordTrace tailWord_1142141 prefixEnd_1142141 586467308206921101784895 := by
  unfold tailWord_1142141
  simp only [CollatzResearch.WordTrace]
  refine ⟨41657304555225693998218277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27771536370150462665478851 41657304555225693998218277)
  ·
    refine ⟨7810744604104817624665927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41657304555225693998218277 7810744604104817624665927)
    ·
      refine ⟨11716116906157226436998891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810744604104817624665927 11716116906157226436998891)
      ·
        refine ⟨17574175359235839655498337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11716116906157226436998891 17574175359235839655498337)
        ·
          refine ⟨13180631519426879741623753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17574175359235839655498337 13180631519426879741623753)
          ·
            refine ⟨9885473639570159806217815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13180631519426879741623753 9885473639570159806217815)
            ·
              refine ⟨14828210459355239709326723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9885473639570159806217815 14828210459355239709326723)
              ·
                refine ⟨22242315689032859563990085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14828210459355239709326723 22242315689032859563990085)
                ·
                  refine ⟨4170434191693661168248141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22242315689032859563990085 4170434191693661168248141)
                  ·
                    refine ⟨1563912821885122938093053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4170434191693661168248141 1563912821885122938093053)
                    ·
                      refine ⟨586467308206921101784895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1563912821885122938093053 586467308206921101784895)
                      ·
                        rfl

theorem cell23_1142141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1142141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142141 prefixEnd_1142141 := by exact prefixLift 1142141
  have htrace : WordTrace (prefixWord ++ tailWord_1142141) baseStart_1142141 baseEnd_1142141 := by
    simpa [prefixWord, tailWord_1142141, baseEnd_1142141] using wordTrace_append hprefix tailTrace_1142141
  have hstable : (prefixWord ++ tailWord_1142141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142141).length < 2 ^ (prefixWord ++ tailWord_1142141).sum := by decide
  have hdescent : baseEnd_1142141 < baseStart_1142141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142148 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 5]
def baseStart_1142148 : Nat := 118140960795 + 1142148 * 2 ^ 59
def prefixEnd_1142148 : Nat := 4983230072969 + 3 ^ 40 * 1142148 * 2
def baseEnd_1142148 : Nat := 65163433619055841599707

theorem tailTrace_1142148 : CollatzResearch.WordTrace tailWord_1142148 prefixEnd_1142148 65163433619055841599707 := by
  unfold tailWord_1142148
  simp only [CollatzResearch.WordTrace]
  refine ⟨20828779933100167096861549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27771706577466889462482065 20828779933100167096861549)
  ·
    refine ⟨7810792474912562661323081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20828779933100167096861549 7810792474912562661323081)
    ·
      refine ⟨5858094356184421995992311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7810792474912562661323081 5858094356184421995992311)
      ·
        refine ⟨8787141534276632993988467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5858094356184421995992311 8787141534276632993988467)
        ·
          refine ⟨13180712301414949490982701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8787141534276632993988467 13180712301414949490982701)
          ·
            refine ⟨4942767113030606059118513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13180712301414949490982701 4942767113030606059118513)
            ·
              refine ⟨3707075334772954544338885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4942767113030606059118513 3707075334772954544338885)
              ·
                refine ⟨695076625269928977063541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3707075334772954544338885 695076625269928977063541)
                ·
                  refine ⟨65163433619055841599707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695076625269928977063541 65163433619055841599707)
                  ·
                    rfl

theorem cell23_1142148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_1142148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142148 prefixEnd_1142148 := by exact prefixLift 1142148
  have htrace : WordTrace (prefixWord ++ tailWord_1142148) baseStart_1142148 baseEnd_1142148 := by
    simpa [prefixWord, tailWord_1142148, baseEnd_1142148] using wordTrace_append hprefix tailTrace_1142148
  have hstable : (prefixWord ++ tailWord_1142148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142148).length < 2 ^ (prefixWord ++ tailWord_1142148).sum := by decide
  have hdescent : baseEnd_1142148 < baseStart_1142148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142191 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 5, 4]
def baseStart_1142191 : Nat := 118140960795 + 1142191 * 2 ^ 59
def prefixEnd_1142191 : Nat := 4983230072969 + 3 ^ 40 * 1142191 * 2
def baseEnd_1142191 : Nat := 195497660746548635386555

theorem tailTrace_1142191 : CollatzResearch.WordTrace tailWord_1142191 prefixEnd_1142191 195497660746548635386555 := by
  unfold tailWord_1142191
  simp only [CollatzResearch.WordTrace]
  refine ⟨41659128205044552537538427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27772752136696368358358951 41659128205044552537538427)
  ·
    refine ⟨62488692307566828806307641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41659128205044552537538427 62488692307566828806307641)
    ·
      refine ⟨46866519230675121604730731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62488692307566828806307641 46866519230675121604730731)
      ·
        refine ⟨70299778846012682407096097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46866519230675121604730731 70299778846012682407096097)
        ·
          refine ⟨52724834134509511805322073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70299778846012682407096097 52724834134509511805322073)
          ·
            refine ⟨39543625600882133853991555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52724834134509511805322073 39543625600882133853991555)
            ·
              refine ⟨59315438401323200780987333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39543625600882133853991555 59315438401323200780987333)
              ·
                refine ⟨11121644700248100146435125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59315438401323200780987333 11121644700248100146435125)
                ·
                  refine ⟨1042654190648259388728293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11121644700248100146435125 1042654190648259388728293)
                  ·
                    refine ⟨195497660746548635386555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042654190648259388728293 195497660746548635386555)
                    ·
                      rfl

theorem cell23_1142191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_1142191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142191 prefixEnd_1142191 := by exact prefixLift 1142191
  have htrace : WordTrace (prefixWord ++ tailWord_1142191) baseStart_1142191 baseEnd_1142191 := by
    simpa [prefixWord, tailWord_1142191, baseEnd_1142191] using wordTrace_append hprefix tailTrace_1142191
  have hstable : (prefixWord ++ tailWord_1142191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142191).length < 2 ^ (prefixWord ++ tailWord_1142191).sum := by decide
  have hdescent : baseEnd_1142191 < baseStart_1142191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142208 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_1142208 : Nat := 118140960795 + 1142208 * 2 ^ 59
def prefixEnd_1142208 : Nat := 4983230072969 + 3 ^ 40 * 1142208 * 2
def baseEnd_1142208 : Nat := 195500570470257446549029

theorem tailTrace_1142208 : CollatzResearch.WordTrace tailWord_1142208 prefixEnd_1142208 195500570470257446549029 := by
  unfold tailWord_1142208
  simp only [CollatzResearch.WordTrace]
  refine ⟨20829874122991482220453639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27773165497321976293938185 20829874122991482220453639)
  ·
    refine ⟨31244811184487223330680459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20829874122991482220453639 31244811184487223330680459)
    ·
      refine ⟨46867216776730834996020689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244811184487223330680459 46867216776730834996020689)
      ·
        refine ⟨35150412582548126247015517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46867216776730834996020689 35150412582548126247015517)
        ·
          refine ⟨13181404718455547342630819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35150412582548126247015517 13181404718455547342630819)
          ·
            refine ⟨19772107077683321013946229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13181404718455547342630819 19772107077683321013946229)
            ·
              refine ⟨1853635038532811345057459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19772107077683321013946229 1853635038532811345057459)
              ·
                refine ⟨2780452557799217017586189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853635038532811345057459 2780452557799217017586189)
                ·
                  refine ⟨1042669709174706381594821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2780452557799217017586189 1042669709174706381594821)
                  ·
                    refine ⟨195500570470257446549029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042669709174706381594821 195500570470257446549029)
                    ·
                      rfl

theorem cell23_1142208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_1142208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142208 prefixEnd_1142208 := by exact prefixLift 1142208
  have htrace : WordTrace (prefixWord ++ tailWord_1142208) baseStart_1142208 baseEnd_1142208 := by
    simpa [prefixWord, tailWord_1142208, baseEnd_1142208] using wordTrace_append hprefix tailTrace_1142208
  have hstable : (prefixWord ++ tailWord_1142208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142208).length < 2 ^ (prefixWord ++ tailWord_1142208).sum := by decide
  have hdescent : baseEnd_1142208 < baseStart_1142208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142231 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1142231 : Nat := 118140960795 + 1142231 * 2 ^ 59
def prefixEnd_1142231 : Nat := 4983230072969 + 3 ^ 40 * 1142231 * 2
def baseEnd_1142231 : Nat := 586513521465825749659481

theorem tailTrace_1142231 : CollatzResearch.WordTrace tailWord_1142231 prefixEnd_1142231 586513521465825749659481 := by
  unfold tailWord_1142231
  simp only [CollatzResearch.WordTrace]
  refine ⟨41660587124899639368994547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27773724749933092912663031 41660587124899639368994547)
  ·
    refine ⟨62490880687349459053491821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41660587124899639368994547 62490880687349459053491821)
    ·
      refine ⟨23434080257756047145059433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62490880687349459053491821 23434080257756047145059433)
      ·
        refine ⟨17575560193317035358794575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23434080257756047145059433 17575560193317035358794575)
        ·
          refine ⟨26363340289975553038191863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17575560193317035358794575 26363340289975553038191863)
          ·
            refine ⟨39545010434963329557287795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26363340289975553038191863 39545010434963329557287795)
            ·
              refine ⟨59317515652444994335931693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39545010434963329557287795 59317515652444994335931693)
              ·
                refine ⟨22244068369666872875974385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59317515652444994335931693 22244068369666872875974385)
                ·
                  refine ⟨16683051277250154656980789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22244068369666872875974385 16683051277250154656980789)
                  ·
                    refine ⟨1564036057242201999091949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16683051277250154656980789 1564036057242201999091949)
                    ·
                      refine ⟨586513521465825749659481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564036057242201999091949 586513521465825749659481)
                      ·
                        rfl

theorem cell23_1142231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1142231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142231 prefixEnd_1142231 := by exact prefixLift 1142231
  have htrace : WordTrace (prefixWord ++ tailWord_1142231) baseStart_1142231 baseEnd_1142231 := by
    simpa [prefixWord, tailWord_1142231, baseEnd_1142231] using wordTrace_append hprefix tailTrace_1142231
  have hstable : (prefixWord ++ tailWord_1142231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142231).length < 2 ^ (prefixWord ++ tailWord_1142231).sum := by decide
  have hdescent : baseEnd_1142231 < baseStart_1142231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142298 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_1142298 : Nat := 118140960795 + 1142298 * 2 ^ 59
def prefixEnd_1142298 : Nat := 4983230072969 + 3 ^ 40 * 1142298 * 2
def baseEnd_1142298 : Nat := 195515974889892329173891

theorem tailTrace_1142298 : CollatzResearch.WordTrace tailWord_1142298 prefixEnd_1142298 195515974889892329173891 := by
  unfold tailWord_1142298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415757703914227452920887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27775353877104606541122365 10415757703914227452920887)
  ·
    refine ⟨15623636555871341179381331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10415757703914227452920887 15623636555871341179381331)
    ·
      refine ⟨23435454833807011769071997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15623636555871341179381331 23435454833807011769071997)
      ·
        refine ⟨8788295562677629413401999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23435454833807011769071997 8788295562677629413401999)
        ·
          refine ⟨13182443344016444120102999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788295562677629413401999 13182443344016444120102999)
          ·
            refine ⟨19773665016024666180154499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13182443344016444120102999 19773665016024666180154499)
            ·
              refine ⟨29660497524036999270231749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19773665016024666180154499 29660497524036999270231749)
              ·
                refine ⟨5561343285756937363168453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29660497524036999270231749 5561343285756937363168453)
                ·
                  refine ⟨1042751866079425755594085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5561343285756937363168453 1042751866079425755594085)
                  ·
                    refine ⟨195515974889892329173891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042751866079425755594085 195515974889892329173891)
                    ·
                      rfl

theorem cell23_1142298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_1142298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142298 prefixEnd_1142298 := by exact prefixLift 1142298
  have htrace : WordTrace (prefixWord ++ tailWord_1142298) baseStart_1142298 baseEnd_1142298 := by
    simpa [prefixWord, tailWord_1142298, baseEnd_1142298] using wordTrace_append hprefix tailTrace_1142298
  have hstable : (prefixWord ++ tailWord_1142298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142298).length < 2 ^ (prefixWord ++ tailWord_1142298).sum := by decide
  have hdescent : baseEnd_1142298 < baseStart_1142298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142305 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1142305 : Nat := 118140960795 + 1142305 * 2 ^ 59
def prefixEnd_1142305 : Nat := 4983230072969 + 3 ^ 40 * 1142305 * 2
def baseEnd_1142305 : Nat := 586551519034258460134141

theorem tailTrace_1142305 : CollatzResearch.WordTrace tailWord_1142305 prefixEnd_1142305 586551519034258460134141 := by
  unfold tailWord_1142305
  simp only [CollatzResearch.WordTrace]
  refine ⟨41663286126631550007188369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27775524084421033338125579 41663286126631550007188369)
  ·
    refine ⟨31247464594973662505391277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41663286126631550007188369 31247464594973662505391277)
    ·
      refine ⟨11717799223115123439521729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31247464594973662505391277 11717799223115123439521729)
      ·
        refine ⟨8788349417336342579641297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11717799223115123439521729 8788349417336342579641297)
        ·
          refine ⟨6591262063002256934730973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8788349417336342579641297 6591262063002256934730973)
          ·
            refine ⟨2471723273625846350524115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6591262063002256934730973 2471723273625846350524115)
            ·
              refine ⟨3707584910438769525786173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471723273625846350524115 3707584910438769525786173)
              ·
                refine ⟨1390344341414538572169815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3707584910438769525786173 1390344341414538572169815)
                ·
                  refine ⟨2085516512121807858254723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390344341414538572169815 2085516512121807858254723)
                  ·
                    refine ⟨3128274768182711787382085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2085516512121807858254723 3128274768182711787382085)
                    ·
                      refine ⟨586551519034258460134141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3128274768182711787382085 586551519034258460134141)
                      ·
                        rfl

theorem cell23_1142305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1142305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142305 prefixEnd_1142305 := by exact prefixLift 1142305
  have htrace : WordTrace (prefixWord ++ tailWord_1142305) baseStart_1142305 baseEnd_1142305 := by
    simpa [prefixWord, tailWord_1142305, baseEnd_1142305] using wordTrace_append hprefix tailTrace_1142305
  have hstable : (prefixWord ++ tailWord_1142305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142305).length < 2 ^ (prefixWord ++ tailWord_1142305).sum := by decide
  have hdescent : baseEnd_1142305 < baseStart_1142305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142321 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1142321 : Nat := 118140960795 + 1142321 * 2 ^ 59
def prefixEnd_1142321 : Nat := 4983230072969 + 3 ^ 40 * 1142321 * 2
def baseEnd_1142321 : Nat := 586559734724730397534067

theorem tailTrace_1142321 : CollatzResearch.WordTrace tailWord_1142321 prefixEnd_1142321 586559734724730397534067 := by
  unfold tailWord_1142321
  simp only [CollatzResearch.WordTrace]
  refine ⟨41663869694573584739770817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27775913129715723159847211 41663869694573584739770817)
  ·
    refine ⟨31247902270930188554828113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41663869694573584739770817 31247902270930188554828113)
    ·
      refine ⟨23435926703197641416121085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31247902270930188554828113 23435926703197641416121085)
      ·
        refine ⟨8788472513699115531045407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23435926703197641416121085 8788472513699115531045407)
        ·
          refine ⟨13182708770548673296568111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788472513699115531045407 13182708770548673296568111)
          ·
            refine ⟨19774063155823009944852167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13182708770548673296568111 19774063155823009944852167)
            ·
              refine ⟨29661094733734514917278251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19774063155823009944852167 29661094733734514917278251)
              ·
                refine ⟨44491642100601772375917377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29661094733734514917278251 44491642100601772375917377)
                ·
                  refine ⟨33368731575451329281938033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44491642100601772375917377 33368731575451329281938033)
                  ·
                    refine ⟨25026548681588496961453525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33368731575451329281938033 25026548681588496961453525)
                    ·
                      refine ⟨586559734724730397534067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25026548681588496961453525 586559734724730397534067)
                      ·
                        rfl

theorem cell23_1142321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1142321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142321 prefixEnd_1142321 := by exact prefixLift 1142321
  have htrace : WordTrace (prefixWord ++ tailWord_1142321) baseStart_1142321 baseEnd_1142321 := by
    simpa [prefixWord, tailWord_1142321, baseEnd_1142321] using wordTrace_append hprefix tailTrace_1142321
  have hstable : (prefixWord ++ tailWord_1142321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142321).length < 2 ^ (prefixWord ++ tailWord_1142321).sum := by decide
  have hdescent : baseEnd_1142321 < baseStart_1142321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142332 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_1142332 : Nat := 118140960795 + 1142332 * 2 ^ 59
def prefixEnd_1142332 : Nat := 4983230072969 + 3 ^ 40 * 1142332 * 2
def baseEnd_1142332 : Nat := 195521794337309951498839

theorem tailTrace_1142332 : CollatzResearch.WordTrace tailWord_1142332 prefixEnd_1142332 195521794337309951498839 := by
  unfold tailWord_1142332
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832135448766866809210625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27776180598355822412280833 20832135448766866809210625)
  ·
    refine ⟨15624101586575150106907969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20832135448766866809210625 15624101586575150106907969)
    ·
      refine ⟨11718076189931362580180977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15624101586575150106907969 11718076189931362580180977)
      ·
        refine ⟨8788557142448521935135733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11718076189931362580180977 8788557142448521935135733)
        ·
          refine ⟨823927232104548931418975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8788557142448521935135733 823927232104548931418975)
          ·
            refine ⟨1235890848156823397128463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823927232104548931418975 1235890848156823397128463)
            ·
              refine ⟨1853836272235235095692695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235890848156823397128463 1853836272235235095692695)
              ·
                refine ⟨2780754408352852643539043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853836272235235095692695 2780754408352852643539043)
                ·
                  refine ⟨4171131612529278965308565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780754408352852643539043 4171131612529278965308565)
                  ·
                    refine ⟨195521794337309951498839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4171131612529278965308565 195521794337309951498839)
                    ·
                      rfl

theorem cell23_1142332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_1142332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142332 prefixEnd_1142332 := by exact prefixLift 1142332
  have htrace : WordTrace (prefixWord ++ tailWord_1142332) baseStart_1142332 baseEnd_1142332 := by
    simpa [prefixWord, tailWord_1142332, baseEnd_1142332] using wordTrace_append hprefix tailTrace_1142332
  have hstable : (prefixWord ++ tailWord_1142332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142332).length < 2 ^ (prefixWord ++ tailWord_1142332).sum := by decide
  have hdescent : baseEnd_1142332 < baseStart_1142332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142335 : List Nat := [1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_1142335 : Nat := 118140960795 + 1142335 * 2 ^ 59
def prefixEnd_1142335 : Nat := 4983230072969 + 3 ^ 40 * 1142335 * 2
def baseEnd_1142335 : Nat := 586566923453893342759003

theorem tailTrace_1142335 : CollatzResearch.WordTrace tailWord_1142335 prefixEnd_1142335 586566923453893342759003 := by
  unfold tailWord_1142335
  simp only [CollatzResearch.WordTrace]
  refine ⟨41664380316522865130780459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27776253544348576753853639 41664380316522865130780459)
  ·
    refine ⟨62496570474784297696170689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41664380316522865130780459 62496570474784297696170689)
    ·
      refine ⟨46872427856088223272128017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62496570474784297696170689 46872427856088223272128017)
      ·
        refine ⟨35154320892066167454096013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46872427856088223272128017 35154320892066167454096013)
        ·
          refine ⟨13182870334524812795286005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35154320892066167454096013 13182870334524812795286005)
          ·
            refine ⟨1235894093861701199558063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13182870334524812795286005 1235894093861701199558063)
            ·
              refine ⟨1853841140792551799337095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235894093861701199558063 1853841140792551799337095)
              ·
                refine ⟨2780761711188827699005643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853841140792551799337095 2780761711188827699005643)
                ·
                  refine ⟨4171142566783241548508465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780761711188827699005643 4171142566783241548508465)
                  ·
                    refine ⟨3128356925087431161381349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4171142566783241548508465 3128356925087431161381349)
                    ·
                      refine ⟨586566923453893342759003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3128356925087431161381349 586566923453893342759003)
                      ·
                        rfl

theorem cell23_1142335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_1142335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142335 prefixEnd_1142335 := by exact prefixLift 1142335
  have htrace : WordTrace (prefixWord ++ tailWord_1142335) baseStart_1142335 baseEnd_1142335 := by
    simpa [prefixWord, tailWord_1142335, baseEnd_1142335] using wordTrace_append hprefix tailTrace_1142335
  have hstable : (prefixWord ++ tailWord_1142335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142335).length < 2 ^ (prefixWord ++ tailWord_1142335).sum := by decide
  have hdescent : baseEnd_1142335 < baseStart_1142335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142361 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1142361 : Nat := 118140960795 + 1142361 * 2 ^ 59
def prefixEnd_1142361 : Nat := 4983230072969 + 3 ^ 40 * 1142361 * 2
def baseEnd_1142361 : Nat := 586580273950910241033883

theorem tailTrace_1142361 : CollatzResearch.WordTrace tailWord_1142361 prefixEnd_1142361 586580273950910241033883 := by
  unfold tailWord_1142361
  simp only [CollatzResearch.WordTrace]
  refine ⟨41665328614428671571226937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27776885742952447714151291 41665328614428671571226937)
  ·
    refine ⟨31248996460821503678420203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41665328614428671571226937 31248996460821503678420203)
    ·
      refine ⟨46873494691232255517630305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31248996460821503678420203 46873494691232255517630305)
      ·
        refine ⟨35155121018424191638222729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46873494691232255517630305 35155121018424191638222729)
        ·
          refine ⟨26366340763818143728667047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35155121018424191638222729 26366340763818143728667047)
          ·
            refine ⟨39549511145727215593000571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26366340763818143728667047 39549511145727215593000571)
            ·
              refine ⟨59324266718590823389500857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39549511145727215593000571 59324266718590823389500857)
              ·
                refine ⟨44493200038943117542125643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59324266718590823389500857 44493200038943117542125643)
                ·
                  refine ⟨66739800058414676313188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44493200038943117542125643 66739800058414676313188465)
                  ·
                    refine ⟨50054850043811007234891349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66739800058414676313188465 50054850043811007234891349)
                    ·
                      refine ⟨586580273950910241033883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50054850043811007234891349 586580273950910241033883)
                      ·
                        rfl

theorem cell23_1142361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1142361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142361 prefixEnd_1142361 := by exact prefixLift 1142361
  have htrace : WordTrace (prefixWord ++ tailWord_1142361) baseStart_1142361 baseEnd_1142361 := by
    simpa [prefixWord, tailWord_1142361, baseEnd_1142361] using wordTrace_append hprefix tailTrace_1142361
  have hstable : (prefixWord ++ tailWord_1142361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142361).length < 2 ^ (prefixWord ++ tailWord_1142361).sum := by decide
  have hdescent : baseEnd_1142361 < baseStart_1142361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142389 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1142389 : Nat := 118140960795 + 1142389 * 2 ^ 59
def prefixEnd_1142389 : Nat := 4983230072969 + 3 ^ 40 * 1142389 * 2
def baseEnd_1142389 : Nat := 586594651409236131483755

theorem tailTrace_1142389 : CollatzResearch.WordTrace tailWord_1142389 prefixEnd_1142389 586594651409236131483755 := by
  unfold tailWord_1142389
  simp only [CollatzResearch.WordTrace]
  refine ⟨41666349858327232353246221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27777566572218154902164147 41666349858327232353246221)
  ·
    refine ⟨15624881196872712132467333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41666349858327232353246221 15624881196872712132467333)
    ·
      refine ⟨2929665224413633524837625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15624881196872712132467333 2929665224413633524837625)
      ·
        refine ⟨2197248918310225143628219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929665224413633524837625 2197248918310225143628219)
        ·
          refine ⟨3295873377465337715442329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197248918310225143628219 3295873377465337715442329)
          ·
            refine ⟨2471905033099003286581747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295873377465337715442329 2471905033099003286581747)
            ·
              refine ⟨3707857549648504929872621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471905033099003286581747 3707857549648504929872621)
              ·
                refine ⟨1390446581118189348702233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3707857549648504929872621 1390446581118189348702233)
                ·
                  refine ⟨1042834935838642011526675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1390446581118189348702233 1042834935838642011526675)
                  ·
                    refine ⟨1564252403757963017290013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1042834935838642011526675 1564252403757963017290013)
                    ·
                      refine ⟨586594651409236131483755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564252403757963017290013 586594651409236131483755)
                      ·
                        rfl

theorem cell23_1142389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1142389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142389 prefixEnd_1142389 := by exact prefixLift 1142389
  have htrace : WordTrace (prefixWord ++ tailWord_1142389) baseStart_1142389 baseEnd_1142389 := by
    simpa [prefixWord, tailWord_1142389, baseEnd_1142389] using wordTrace_append hprefix tailTrace_1142389
  have hstable : (prefixWord ++ tailWord_1142389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142389).length < 2 ^ (prefixWord ++ tailWord_1142389).sum := by decide
  have hdescent : baseEnd_1142389 < baseStart_1142389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142395 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 4, 2]
def baseStart_1142395 : Nat := 118140960795 + 1142395 * 2 ^ 59
def prefixEnd_1142395 : Nat := 4983230072969 + 3 ^ 40 * 1142395 * 2
def baseEnd_1142395 : Nat := 586597732293163108008727

theorem tailTrace_1142395 : CollatzResearch.WordTrace tailWord_1142395 prefixEnd_1142395 586597732293163108008727 := by
  unfold tailWord_1142395
  simp only [CollatzResearch.WordTrace]
  refine ⟨41666568696305495377964639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27777712464203663585309759 41666568696305495377964639)
  ·
    refine ⟨62499853044458243066946959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41666568696305495377964639 62499853044458243066946959)
    ·
      refine ⟨93749779566687364600420439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62499853044458243066946959 93749779566687364600420439)
      ·
        refine ⟨140624669350031046900630659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93749779566687364600420439 140624669350031046900630659)
        ·
          refine ⟨210937004025046570350945989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140624669350031046900630659 210937004025046570350945989)
          ·
            refine ⟨39550688254696231940802373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210937004025046570350945989 39550688254696231940802373)
            ·
              refine ⟨7415754047755543488900445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39550688254696231940802373 7415754047755543488900445)
              ·
                refine ⟨2780907767908328808337667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7415754047755543488900445 2780907767908328808337667)
                ·
                  refine ⟨4171361651862493212506501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780907767908328808337667 4171361651862493212506501)
                  ·
                    refine ⟨782130309724217477344969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171361651862493212506501 782130309724217477344969)
                    ·
                      refine ⟨586597732293163108008727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782130309724217477344969 586597732293163108008727)
                      ·
                        rfl

theorem cell23_1142395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4, 2].length) (baseStart_1142395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142395 prefixEnd_1142395 := by exact prefixLift 1142395
  have htrace : WordTrace (prefixWord ++ tailWord_1142395) baseStart_1142395 baseEnd_1142395 := by
    simpa [prefixWord, tailWord_1142395, baseEnd_1142395] using wordTrace_append hprefix tailTrace_1142395
  have hstable : (prefixWord ++ tailWord_1142395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142395).length < 2 ^ (prefixWord ++ tailWord_1142395).sum := by decide
  have hdescent : baseEnd_1142395 < baseStart_1142395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142435 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 5]
def baseStart_1142435 : Nat := 118140960795 + 1142435 * 2 ^ 59
def prefixEnd_1142435 : Nat := 4983230072969 + 3 ^ 40 * 1142435 * 2
def baseEnd_1142435 : Nat := 65179807946593661278727

theorem tailTrace_1142435 : CollatzResearch.WordTrace tailWord_1142435 prefixEnd_1142435 65179807946593661278727 := by
  unfold tailWord_1142435
  simp only [CollatzResearch.WordTrace]
  refine ⟨41668027616160582209420759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27778685077440388139613839 41668027616160582209420759)
  ·
    refine ⟨62502041424240873314131139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41668027616160582209420759 62502041424240873314131139)
    ·
      refine ⟨93753062136361309971196709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62502041424240873314131139 93753062136361309971196709)
      ·
        refine ⟨17578699150567745619599383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93753062136361309971196709 17578699150567745619599383)
        ·
          refine ⟨26368048725851618429399075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17578699150567745619599383 26368048725851618429399075)
          ·
            refine ⟨39552073088777427644098613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26368048725851618429399075 39552073088777427644098613)
            ·
              refine ⟨3708006852072883841634245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39552073088777427644098613 3708006852072883841634245)
              ·
                refine ⟨695251284763665720306421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3708006852072883841634245 695251284763665720306421)
                ·
                  refine ⟨65179807946593661278727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695251284763665720306421 65179807946593661278727)
                  ·
                    rfl

theorem cell23_1142435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 5].length) (baseStart_1142435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142435 prefixEnd_1142435 := by exact prefixLift 1142435
  have htrace : WordTrace (prefixWord ++ tailWord_1142435) baseStart_1142435 baseEnd_1142435 := by
    simpa [prefixWord, tailWord_1142435, baseEnd_1142435] using wordTrace_append hprefix tailTrace_1142435
  have hstable : (prefixWord ++ tailWord_1142435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142435).length < 2 ^ (prefixWord ++ tailWord_1142435).sum := by decide
  have hdescent : baseEnd_1142435 < baseStart_1142435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142446 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1142446 : Nat := 118140960795 + 1142446 * 2 ^ 59
def prefixEnd_1142446 : Nat := 4983230072969 + 3 ^ 40 * 1142446 * 2
def baseEnd_1142446 : Nat := 586623919806542408470993

theorem tailTrace_1142446 : CollatzResearch.WordTrace tailWord_1142446 prefixEnd_1142446 586623919806542408470993 := by
  unfold tailWord_1142446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208553602390091386008899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27778952546080487392047461 5208553602390091386008899)
  ·
    refine ⟨7812830403585137079013349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208553602390091386008899 7812830403585137079013349)
    ·
      refine ⟨1464905700672213202315003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7812830403585137079013349 1464905700672213202315003)
      ·
        refine ⟨2197358551008319803472505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464905700672213202315003 2197358551008319803472505)
        ·
          refine ⟨1648018913256239852604379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197358551008319803472505 1648018913256239852604379)
          ·
            refine ⟨2472028369884359778906569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648018913256239852604379 2472028369884359778906569)
            ·
              refine ⟨1854021277413269834179927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472028369884359778906569 1854021277413269834179927)
              ·
                refine ⟨2781031916119904751269891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854021277413269834179927 2781031916119904751269891)
                ·
                  refine ⟨4171547874179857126904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781031916119904751269891 4171547874179857126904837)
                  ·
                    refine ⟨782165226408723211294657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171547874179857126904837 782165226408723211294657)
                    ·
                      refine ⟨586623919806542408470993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782165226408723211294657 586623919806542408470993)
                      ·
                        rfl

theorem cell23_1142446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1142446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142446 prefixEnd_1142446 := by exact prefixLift 1142446
  have htrace : WordTrace (prefixWord ++ tailWord_1142446) baseStart_1142446 baseEnd_1142446 := by
    simpa [prefixWord, tailWord_1142446, baseEnd_1142446] using wordTrace_append hprefix tailTrace_1142446
  have hstable : (prefixWord ++ tailWord_1142446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142446).length < 2 ^ (prefixWord ++ tailWord_1142446).sum := by decide
  have hdescent : baseEnd_1142446 < baseStart_1142446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142448 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_1142448 : Nat := 118140960795 + 1142448 * 2 ^ 59
def prefixEnd_1142448 : Nat := 4983230072969 + 3 ^ 40 * 1142448 * 2
def baseEnd_1142448 : Nat := 195541648922617133548661

theorem tailTrace_1142448 : CollatzResearch.WordTrace tailWord_1142448 prefixEnd_1142448 195541648922617133548661 := by
  unfold tailWord_1142448
  simp only [CollatzResearch.WordTrace]
  refine ⟨20834250882556742714821999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27779001176742323619762665 20834250882556742714821999)
  ·
    refine ⟨31251376323835114072232999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20834250882556742714821999 31251376323835114072232999)
    ·
      refine ⟨46877064485752671108349499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31251376323835114072232999 46877064485752671108349499)
      ·
        refine ⟨70315596728629006662524249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46877064485752671108349499 70315596728629006662524249)
        ·
          refine ⟨52736697546471754996893187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70315596728629006662524249 52736697546471754996893187)
          ·
            refine ⟨79105046319707632495339781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52736697546471754996893187 79105046319707632495339781)
            ·
              refine ⟨14832196184945181092876209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79105046319707632495339781 14832196184945181092876209)
              ·
                refine ⟨11124147138708885819657157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14832196184945181092876209 11124147138708885819657157)
                ·
                  refine ⟨2085777588507916091185717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11124147138708885819657157 2085777588507916091185717)
                  ·
                    refine ⟨195541648922617133548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2085777588507916091185717 195541648922617133548661)
                    ·
                      rfl

theorem cell23_1142448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_1142448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142448 prefixEnd_1142448 := by exact prefixLift 1142448
  have htrace : WordTrace (prefixWord ++ tailWord_1142448) baseStart_1142448 baseEnd_1142448 := by
    simpa [prefixWord, tailWord_1142448, baseEnd_1142448] using wordTrace_append hprefix tailTrace_1142448
  have hstable : (prefixWord ++ tailWord_1142448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142448).length < 2 ^ (prefixWord ++ tailWord_1142448).sum := by decide
  have hdescent : baseEnd_1142448 < baseStart_1142448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1142528 : Nat := 118140960795 + 1142528 * 2 ^ 59
def prefixEnd_1142528 : Nat := 4983230072969 + 3 ^ 40 * 1142528 * 2
def baseEnd_1142528 : Nat := 586666025220211087645615

theorem tailTrace_1142528 : CollatzResearch.WordTrace tailWord_1142528 prefixEnd_1142528 586666025220211087645615 := by
  unfold tailWord_1142528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20835709802411829546278119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27780946403215772728370825 20835709802411829546278119)
  ·
    refine ⟨31253564703617744319417179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20835709802411829546278119 31253564703617744319417179)
    ·
      refine ⟨46880347055426616479125769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31253564703617744319417179 46880347055426616479125769)
      ·
        refine ⟨35160260291569962359344327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46880347055426616479125769 35160260291569962359344327)
        ·
          refine ⟨52740390437354943539016491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35160260291569962359344327 52740390437354943539016491)
          ·
            refine ⟨79110585656032415308524737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52740390437354943539016491 79110585656032415308524737)
            ·
              refine ⟨59332939242024311481393553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79110585656032415308524737 59332939242024311481393553)
              ·
                refine ⟨44499704431518233611045165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59332939242024311481393553 44499704431518233611045165)
                ·
                  refine ⟨16687389161819337604141937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44499704431518233611045165 16687389161819337604141937)
                  ·
                    refine ⟨12515541871364503203106453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16687389161819337604141937 12515541871364503203106453)
                    ·
                      refine ⟨586666025220211087645615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12515541871364503203106453 586666025220211087645615)
                      ·
                        rfl

theorem cell23_1142528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1142528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142528 prefixEnd_1142528 := by exact prefixLift 1142528
  have htrace : WordTrace (prefixWord ++ tailWord_1142528) baseStart_1142528 baseEnd_1142528 := by
    simpa [prefixWord, tailWord_1142528, baseEnd_1142528] using wordTrace_append hprefix tailTrace_1142528
  have hstable : (prefixWord ++ tailWord_1142528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142528).length < 2 ^ (prefixWord ++ tailWord_1142528).sum := by decide
  have hdescent : baseEnd_1142528 < baseStart_1142528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142529 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1142529 : Nat := 118140960795 + 1142529 * 2 ^ 59
def prefixEnd_1142529 : Nat := 4983230072969 + 3 ^ 40 * 1142529 * 2
def baseEnd_1142529 : Nat := 195555512900288527911037

theorem tailTrace_1142529 : CollatzResearch.WordTrace tailWord_1142529 prefixEnd_1142529 195555512900288527911037 := by
  unfold tailWord_1142529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41671456077820036263342641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27780970718546690842228427 41671456077820036263342641)
  ·
    refine ⟨31253592058365027197506981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41671456077820036263342641 31253592058365027197506981)
    ·
      refine ⟨5860048510943442599532559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31253592058365027197506981 5860048510943442599532559)
      ·
        refine ⟨8790072766415163899298839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5860048510943442599532559 8790072766415163899298839)
        ·
          refine ⟨13185109149622745848948259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8790072766415163899298839 13185109149622745848948259)
          ·
            refine ⟨19777663724434118773422389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13185109149622745848948259 19777663724434118773422389)
            ·
              refine ⟨1854155974165698635008349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19777663724434118773422389 1854155974165698635008349)
              ·
                refine ⟨695308490312136988128131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1854155974165698635008349 695308490312136988128131)
                ·
                  refine ⟨1042962735468205482192197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695308490312136988128131 1042962735468205482192197)
                  ·
                    refine ⟨195555512900288527911037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042962735468205482192197 195555512900288527911037)
                    ·
                      rfl

theorem cell23_1142529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1142529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142529 prefixEnd_1142529 := by exact prefixLift 1142529
  have htrace : WordTrace (prefixWord ++ tailWord_1142529) baseStart_1142529 baseEnd_1142529 := by
    simpa [prefixWord, tailWord_1142529, baseEnd_1142529] using wordTrace_append hprefix tailTrace_1142529
  have hstable : (prefixWord ++ tailWord_1142529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142529).length < 2 ^ (prefixWord ++ tailWord_1142529).sum := by decide
  have hdescent : baseEnd_1142529 < baseStart_1142529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142546 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1142546 : Nat := 118140960795 + 1142546 * 2 ^ 59
def prefixEnd_1142546 : Nat := 4983230072969 + 3 ^ 40 * 1142546 * 2
def baseEnd_1142546 : Nat := 195558422623997339073511

theorem tailTrace_1142546 : CollatzResearch.WordTrace tailWord_1142546 prefixEnd_1142546 195558422623997339073511 := by
  unfold tailWord_1142546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418019029689612041677873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27781384079172298777807661 10418019029689612041677873)
  ·
    refine ⟨7813514272267209031258405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10418019029689612041677873 7813514272267209031258405)
    ·
      refine ⟨1465033926050101693360951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7813514272267209031258405 1465033926050101693360951)
      ·
        refine ⟨2197550889075152540041427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465033926050101693360951 2197550889075152540041427)
        ·
          refine ⟨3296326333612728810062141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197550889075152540041427 3296326333612728810062141)
          ·
            refine ⟨1236122375104773303773303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3296326333612728810062141 1236122375104773303773303)
            ·
              refine ⟨1854183562657159955659955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236122375104773303773303 1854183562657159955659955)
              ·
                refine ⟨2781275343985739933489933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854183562657159955659955 2781275343985739933489933)
                ·
                  refine ⟨1042978253994652475058725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2781275343985739933489933 1042978253994652475058725)
                  ·
                    refine ⟨195558422623997339073511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1042978253994652475058725 195558422623997339073511)
                    ·
                      rfl

theorem cell23_1142546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1142546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142546 prefixEnd_1142546 := by exact prefixLift 1142546
  have htrace : WordTrace (prefixWord ++ tailWord_1142546) baseStart_1142546 baseEnd_1142546 := by
    simpa [prefixWord, tailWord_1142546, baseEnd_1142546] using wordTrace_append hprefix tailTrace_1142546
  have hstable : (prefixWord ++ tailWord_1142546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142546).length < 2 ^ (prefixWord ++ tailWord_1142546).sum := by decide
  have hdescent : baseEnd_1142546 < baseStart_1142546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142572 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_1142572 : Nat := 118140960795 + 1142572 * 2 ^ 59
def prefixEnd_1142572 : Nat := 4983230072969 + 3 ^ 40 * 1142572 * 2
def baseEnd_1142572 : Nat := 195562872789669638498471

theorem tailTrace_1142572 : CollatzResearch.WordTrace tailWord_1142572 prefixEnd_1142572 195562872789669638498471 := by
  unfold tailWord_1142572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20836512208332127303578985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27782016277776169738105313 20836512208332127303578985)
  ·
    refine ⟨15627384156249095477684239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20836512208332127303578985 15627384156249095477684239)
    ·
      refine ⟨23441076234373643216526359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15627384156249095477684239 23441076234373643216526359)
      ·
        refine ⟨35161614351560464824789539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23441076234373643216526359 35161614351560464824789539)
        ·
          refine ⟨52742421527340697237184309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35161614351560464824789539 52742421527340697237184309)
          ·
            refine ⟨4944602018188190365986029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52742421527340697237184309 4944602018188190365986029)
            ·
              refine ⟨1854225756820571387244761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4944602018188190365986029 1854225756820571387244761)
              ·
                refine ⟨1390669317615428540433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854225756820571387244761 1390669317615428540433571)
                ·
                  refine ⟨2086003976423142810650357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390669317615428540433571 2086003976423142810650357)
                  ·
                    refine ⟨195562872789669638498471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2086003976423142810650357 195562872789669638498471)
                    ·
                      rfl

theorem cell23_1142572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_1142572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142572 prefixEnd_1142572 := by exact prefixLift 1142572
  have htrace : WordTrace (prefixWord ++ tailWord_1142572) baseStart_1142572 baseEnd_1142572 := by
    simpa [prefixWord, tailWord_1142572, baseEnd_1142572] using wordTrace_append hprefix tailTrace_1142572
  have hstable : (prefixWord ++ tailWord_1142572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142572).length < 2 ^ (prefixWord ++ tailWord_1142572).sum := by decide
  have hdescent : baseEnd_1142572 < baseStart_1142572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142575 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_1142575 : Nat := 118140960795 + 1142575 * 2 ^ 59
def prefixEnd_1142575 : Nat := 4983230072969 + 3 ^ 40 * 1142575 * 2
def baseEnd_1142575 : Nat := 586690158810972403757899

theorem tailTrace_1142575 : CollatzResearch.WordTrace tailWord_1142575 prefixEnd_1142575 586690158810972403757899 := by
  unfold tailWord_1142575
  simp only [CollatzResearch.WordTrace]
  refine ⟨41673133835653386119517179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27782089223768924079678119 41673133835653386119517179)
  ·
    refine ⟨62509700753480079179275769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41673133835653386119517179 62509700753480079179275769)
    ·
      refine ⟨46882275565110059384456827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62509700753480079179275769 46882275565110059384456827)
      ·
        refine ⟨70323413347665089076685241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46882275565110059384456827 70323413347665089076685241)
        ·
          refine ⟨52742560010748816807513931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70323413347665089076685241 52742560010748816807513931)
          ·
            refine ⟨79113840016123225211270897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52742560010748816807513931 79113840016123225211270897)
            ·
              refine ⟨59335380012092418908453173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79113840016123225211270897 59335380012092418908453173)
              ·
                refine ⟨5562691876133664272667485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59335380012092418908453173 5562691876133664272667485)
                ·
                  refine ⟨2086009453550124102250307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5562691876133664272667485 2086009453550124102250307)
                  ·
                    refine ⟨3129014180325186153375461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2086009453550124102250307 3129014180325186153375461)
                    ·
                      refine ⟨586690158810972403757899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3129014180325186153375461 586690158810972403757899)
                      ·
                        rfl

theorem cell23_1142575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_1142575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142575 prefixEnd_1142575 := by exact prefixLift 1142575
  have htrace : WordTrace (prefixWord ++ tailWord_1142575) baseStart_1142575 baseEnd_1142575 := by
    simpa [prefixWord, tailWord_1142575, baseEnd_1142575] using wordTrace_append hprefix tailTrace_1142575
  have hstable : (prefixWord ++ tailWord_1142575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142575).length < 2 ^ (prefixWord ++ tailWord_1142575).sum := by decide
  have hdescent : baseEnd_1142575 < baseStart_1142575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142626 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1142626 : Nat := 118140960795 + 1142626 * 2 ^ 59
def prefixEnd_1142626 : Nat := 4983230072969 + 3 ^ 40 * 1142626 * 2
def baseEnd_1142626 : Nat := 586716346324351704220165

theorem tailTrace_1142626 : CollatzResearch.WordTrace tailWord_1142626 prefixEnd_1142626 586716346324351704220165 := by
  unfold tailWord_1142626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418748489617155457405933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27783329305645747886415821 10418748489617155457405933)
  ·
    refine ⟨3907030683606433296527225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10418748489617155457405933 3907030683606433296527225)
    ·
      refine ⟨2930273012704824972395419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3907030683606433296527225 2930273012704824972395419)
      ·
        refine ⟨4395409519057237458593129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930273012704824972395419 4395409519057237458593129)
        ·
          refine ⟨3296557139292928093944847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4395409519057237458593129 3296557139292928093944847)
          ·
            refine ⟨4944835708939392140917271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296557139292928093944847 4944835708939392140917271)
            ·
              refine ⟨7417253563409088211375907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944835708939392140917271 7417253563409088211375907)
              ·
                refine ⟨11125880345113632317063861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7417253563409088211375907 11125880345113632317063861)
                ·
                  refine ⟨1043051282354403029724737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11125880345113632317063861 1043051282354403029724737)
                  ·
                    refine ⟨782288461765802272293553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1043051282354403029724737 782288461765802272293553)
                    ·
                      refine ⟨586716346324351704220165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782288461765802272293553 586716346324351704220165)
                      ·
                        rfl

theorem cell23_1142626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1142626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142626 prefixEnd_1142626 := by exact prefixLift 1142626
  have htrace : WordTrace (prefixWord ++ tailWord_1142626) baseStart_1142626 baseEnd_1142626 := by
    simpa [prefixWord, tailWord_1142626, baseEnd_1142626] using wordTrace_append hprefix tailTrace_1142626
  have hstable : (prefixWord ++ tailWord_1142626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142626).length < 2 ^ (prefixWord ++ tailWord_1142626).sum := by decide
  have hdescent : baseEnd_1142626 < baseStart_1142626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142632 : List Nat := [2, 1, 4, 2, 1, 1, 5, 7]
def baseStart_1142632 : Nat := 118140960795 + 1142632 * 2 ^ 59
def prefixEnd_1142632 : Nat := 4983230072969 + 3 ^ 40 * 1142632 * 2
def baseEnd_1142632 : Nat := 21730349155862173360931

theorem tailTrace_1142632 : CollatzResearch.WordTrace tailWord_1142632 prefixEnd_1142632 21730349155862173360931 := by
  unfold tailWord_1142632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20837606398223442427171075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27783475197631256569561433 20837606398223442427171075)
  ·
    refine ⟨31256409597335163640756613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20837606398223442427171075 31256409597335163640756613)
    ·
      refine ⟨5860576799500343182641865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31256409597335163640756613 5860576799500343182641865)
      ·
        refine ⟨4395432599625257386981399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5860576799500343182641865 4395432599625257386981399)
        ·
          refine ⟨6593148899437886080472099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395432599625257386981399 6593148899437886080472099)
          ·
            refine ⟨9889723349156829120708149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593148899437886080472099 9889723349156829120708149)
            ·
              refine ⟨927161563983452730066389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9889723349156829120708149 927161563983452730066389)
              ·
                refine ⟨21730349155862173360931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 927161563983452730066389 21730349155862173360931)
                ·
                  rfl

theorem cell23_1142632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 7].length) (baseStart_1142632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142632 prefixEnd_1142632 := by exact prefixLift 1142632
  have htrace : WordTrace (prefixWord ++ tailWord_1142632) baseStart_1142632 baseEnd_1142632 := by
    simpa [prefixWord, tailWord_1142632, baseEnd_1142632] using wordTrace_append hprefix tailTrace_1142632
  have hstable : (prefixWord ++ tailWord_1142632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142632).length < 2 ^ (prefixWord ++ tailWord_1142632).sum := by decide
  have hdescent : baseEnd_1142632 < baseStart_1142632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142659 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 3]
def baseStart_1142659 : Nat := 118140960795 + 1142659 * 2 ^ 59
def prefixEnd_1142659 : Nat := 4983230072969 + 3 ^ 40 * 1142659 * 2
def baseEnd_1142659 : Nat := 586733291185950075107513

theorem tailTrace_1142659 : CollatzResearch.WordTrace tailWord_1142659 prefixEnd_1142659 586733291185950075107513 := by
  unfold tailWord_1142659
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676197567349068465575031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27784131711566045643716687 41676197567349068465575031)
  ·
    refine ⟨62514296351023602698362547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41676197567349068465575031 62514296351023602698362547)
    ·
      refine ⟨93771444526535404047543821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62514296351023602698362547 93771444526535404047543821)
      ·
        refine ⟨35164291697450776517828933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93771444526535404047543821 35164291697450776517828933)
        ·
          refine ⟨6593304693272020597092925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35164291697450776517828933 6593304693272020597092925)
          ·
            refine ⟨2472489259977007723909847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6593304693272020597092925 2472489259977007723909847)
            ·
              refine ⟨3708733889965511585864771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472489259977007723909847 3708733889965511585864771)
              ·
                refine ⟨5563100834948267378797157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708733889965511585864771 5563100834948267378797157)
                ·
                  refine ⟨1043081406552800133524467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5563100834948267378797157 1043081406552800133524467)
                  ·
                    refine ⟨1564622109829200200286701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1043081406552800133524467 1564622109829200200286701)
                    ·
                      refine ⟨586733291185950075107513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564622109829200200286701 586733291185950075107513)
                      ·
                        rfl

theorem cell23_1142659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_1142659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142659 prefixEnd_1142659 := by exact prefixLift 1142659
  have htrace : WordTrace (prefixWord ++ tailWord_1142659) baseStart_1142659 baseEnd_1142659 := by
    simpa [prefixWord, tailWord_1142659, baseEnd_1142659] using wordTrace_append hprefix tailTrace_1142659
  have hstable : (prefixWord ++ tailWord_1142659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142659).length < 2 ^ (prefixWord ++ tailWord_1142659).sum := by decide
  have hdescent : baseEnd_1142659 < baseStart_1142659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142676 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1142676 : Nat := 118140960795 + 1142676 * 2 ^ 59
def prefixEnd_1142676 : Nat := 4983230072969 + 3 ^ 40 * 1142676 * 2
def baseEnd_1142676 : Nat := 586742020357076508594935

theorem tailTrace_1142676 : CollatzResearch.WordTrace tailWord_1142676 prefixEnd_1142676 586742020357076508594935 := by
  unfold tailWord_1142676
  simp only [CollatzResearch.WordTrace]
  refine ⟨20838408804143740184471941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27784545072191653579295921 20838408804143740184471941)
  ·
    refine ⟨3907201650776951284588489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20838408804143740184471941 3907201650776951284588489)
    ·
      refine ⟨2930401238082713463441367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3907201650776951284588489 2930401238082713463441367)
      ·
        refine ⟨4395601857124070195162051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930401238082713463441367 4395601857124070195162051)
        ·
          refine ⟨6593402785686105292743077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395601857124070195162051 6593402785686105292743077)
          ·
            refine ⟨1236263022316144742389327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6593402785686105292743077 1236263022316144742389327)
            ·
              refine ⟨1854394533474217113583991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236263022316144742389327 1854394533474217113583991)
              ·
                refine ⟨2781591800211325670375987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854394533474217113583991 2781591800211325670375987)
                ·
                  refine ⟨4172387700316988505563981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781591800211325670375987 4172387700316988505563981)
                  ·
                    refine ⟨1564645387618870689586493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4172387700316988505563981 1564645387618870689586493)
                    ·
                      refine ⟨586742020357076508594935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564645387618870689586493 586742020357076508594935)
                      ·
                        rfl

theorem cell23_1142676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1142676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142676 prefixEnd_1142676 := by exact prefixLift 1142676
  have htrace : WordTrace (prefixWord ++ tailWord_1142676) baseStart_1142676 baseEnd_1142676 := by
    simpa [prefixWord, tailWord_1142676, baseEnd_1142676] using wordTrace_append hprefix tailTrace_1142676
  have hstable : (prefixWord ++ tailWord_1142676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142676).length < 2 ^ (prefixWord ++ tailWord_1142676).sum := by decide
  have hdescent : baseEnd_1142676 < baseStart_1142676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142725 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_1142725 : Nat := 118140960795 + 1142725 * 2 ^ 59
def prefixEnd_1142725 : Nat := 4983230072969 + 3 ^ 40 * 1142725 * 2
def baseEnd_1142725 : Nat := 586767180909146816882209

theorem tailTrace_1142725 : CollatzResearch.WordTrace tailWord_1142725 prefixEnd_1142725 586767180909146816882209 := by
  unfold tailWord_1142725
  simp only [CollatzResearch.WordTrace]
  refine ⟨41678604785109961737477629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27785736523406641158318419 41678604785109961737477629)
  ·
    refine ⟨15629476794416235651554111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41678604785109961737477629 15629476794416235651554111)
    ·
      refine ⟨23444215191624353477331167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15629476794416235651554111 23444215191624353477331167)
      ·
        refine ⟨35166322787436530215996751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23444215191624353477331167 35166322787436530215996751)
        ·
          refine ⟨52749484181154795323995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35166322787436530215996751 52749484181154795323995127)
          ·
            refine ⟨79124226271732192985992691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52749484181154795323995127 79124226271732192985992691)
            ·
              refine ⟨118686339407598289478989037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79124226271732192985992691 118686339407598289478989037)
              ·
                refine ⟨44507377277849358554620889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118686339407598289478989037 44507377277849358554620889)
                ·
                  refine ⟨33380532958387018915965667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44507377277849358554620889 33380532958387018915965667)
                  ·
                    refine ⟨50070799437580528373948501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33380532958387018915965667 50070799437580528373948501)
                    ·
                      refine ⟨586767180909146816882209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50070799437580528373948501 586767180909146816882209)
                      ·
                        rfl

theorem cell23_1142725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_1142725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142725 prefixEnd_1142725 := by exact prefixLift 1142725
  have htrace : WordTrace (prefixWord ++ tailWord_1142725) baseStart_1142725 baseEnd_1142725 := by
    simpa [prefixWord, tailWord_1142725, baseEnd_1142725] using wordTrace_append hprefix tailTrace_1142725
  have hstable : (prefixWord ++ tailWord_1142725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142725).length < 2 ^ (prefixWord ++ tailWord_1142725).sum := by decide
  have hdescent : baseEnd_1142725 < baseStart_1142725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142762 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1142762 : Nat := 118140960795 + 1142762 * 2 ^ 59
def prefixEnd_1142762 : Nat := 4983230072969 + 3 ^ 40 * 1142762 * 2
def baseEnd_1142762 : Nat := 586786179693363172119539

theorem tailTrace_1142762 : CollatzResearch.WordTrace tailWord_1142762 prefixEnd_1142762 586786179693363172119539 := by
  unfold tailWord_1142762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419988571493979264143635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27786636190650611371049693 10419988571493979264143635)
  ·
    refine ⟨15629982857240968896215453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10419988571493979264143635 15629982857240968896215453)
    ·
      refine ⟨5861243571465363336080795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15629982857240968896215453 5861243571465363336080795)
      ·
        refine ⟨8791865357198045004121193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5861243571465363336080795 8791865357198045004121193)
        ·
          refine ⟨6593899017898533753090895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8791865357198045004121193 6593899017898533753090895)
          ·
            refine ⟨9890848526847800629636343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6593899017898533753090895 9890848526847800629636343)
            ·
              refine ⟨14836272790271700944454515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9890848526847800629636343 14836272790271700944454515)
              ·
                refine ⟨22254409185407551416681773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14836272790271700944454515 22254409185407551416681773)
                ·
                  refine ⟨8345403444527831781255665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22254409185407551416681773 8345403444527831781255665)
                  ·
                    refine ⟨6259052583395873835941749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8345403444527831781255665 6259052583395873835941749)
                    ·
                      refine ⟨586786179693363172119539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6259052583395873835941749 586786179693363172119539)
                      ·
                        rfl

theorem cell23_1142762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1142762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142762 prefixEnd_1142762 := by exact prefixLift 1142762
  have htrace : WordTrace (prefixWord ++ tailWord_1142762) baseStart_1142762 baseEnd_1142762 := by
    simpa [prefixWord, tailWord_1142762, baseEnd_1142762] using wordTrace_append hprefix tailTrace_1142762
  have hstable : (prefixWord ++ tailWord_1142762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142762).length < 2 ^ (prefixWord ++ tailWord_1142762).sum := by decide
  have hdescent : baseEnd_1142762 < baseStart_1142762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142789 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_1142789 : Nat := 118140960795 + 1142789 * 2 ^ 59
def prefixEnd_1142789 : Nat := 4983230072969 + 3 ^ 40 * 1142789 * 2
def baseEnd_1142789 : Nat := 586800043671034566481915

theorem tailTrace_1142789 : CollatzResearch.WordTrace tailWord_1142789 prefixEnd_1142789 586800043671034566481915 := by
  unfold tailWord_1142789
  simp only [CollatzResearch.WordTrace]
  refine ⟨41680939056878100667807421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27787292704585400445204947 41680939056878100667807421)
  ·
    refine ⟨15630352146329287750427783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41680939056878100667807421 15630352146329287750427783)
    ·
      refine ⟨23445528219493931625641675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15630352146329287750427783 23445528219493931625641675)
      ·
        refine ⟨35168292329240897438462513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23445528219493931625641675 35168292329240897438462513)
        ·
          refine ⟨26376219246930673078846885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35168292329240897438462513 26376219246930673078846885)
          ·
            refine ⟨4945541108799501202283791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26376219246930673078846885 4945541108799501202283791)
            ·
              refine ⟨7418311663199251803425687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4945541108799501202283791 7418311663199251803425687)
              ·
                refine ⟨11127467494798877705138531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418311663199251803425687 11127467494798877705138531)
                ·
                  refine ⟨16691201242198316557707797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127467494798877705138531 16691201242198316557707797)
                  ·
                    refine ⟨782400058228046088642553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16691201242198316557707797 782400058228046088642553)
                    ·
                      refine ⟨586800043671034566481915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782400058228046088642553 586800043671034566481915)
                      ·
                        rfl

theorem cell23_1142789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_1142789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142789 prefixEnd_1142789 := by exact prefixLift 1142789
  have htrace : WordTrace (prefixWord ++ tailWord_1142789) baseStart_1142789 baseEnd_1142789 := by
    simpa [prefixWord, tailWord_1142789, baseEnd_1142789] using wordTrace_append hprefix tailTrace_1142789
  have hstable : (prefixWord ++ tailWord_1142789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142789).length < 2 ^ (prefixWord ++ tailWord_1142789).sum := by decide
  have hdescent : baseEnd_1142789 < baseStart_1142789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
