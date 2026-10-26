import V185TrunkScan23Chunk0552

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3268520 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3268520 : Nat := 118140960795 + 3268520 * 2 ^ 59
def prefixEnd_3268520 : Nat := 4983230072969 + 3 ^ 40 * 3268520 * 2
def baseEnd_3268520 : Nat := 1678321788833657134168357

theorem tailTrace_3268520 : CollatzResearch.WordTrace tailWord_3268520 prefixEnd_3268520 1678321788833657134168357 := by
  unfold tailWord_3268520
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606359059358866809521507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79475145412478489079362009 59606359059358866809521507)
  ·
    refine ⟨89409538589038300214282261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59606359059358866809521507 89409538589038300214282261)
    ·
      refine ⟨4191072121361170322544481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89409538589038300214282261 4191072121361170322544481)
      ·
        refine ⟨3143304091020877741908361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191072121361170322544481 3143304091020877741908361)
        ·
          refine ⟨2357478068265658306431271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143304091020877741908361 2357478068265658306431271)
          ·
            refine ⟨3536217102398487459646907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357478068265658306431271 3536217102398487459646907)
            ·
              refine ⟨5304325653597731189470361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536217102398487459646907 5304325653597731189470361)
              ·
                refine ⟨3978244240198298392102771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304325653597731189470361 3978244240198298392102771)
                ·
                  refine ⟨5967366360297447588154157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978244240198298392102771 5967366360297447588154157)
                  ·
                    refine ⟨2237762385111542845557809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5967366360297447588154157 2237762385111542845557809)
                    ·
                      refine ⟨1678321788833657134168357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237762385111542845557809 1678321788833657134168357)
                      ·
                        rfl

theorem cell23_3268520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3268520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268520 prefixEnd_3268520 := by exact prefixLift 3268520
  have htrace : WordTrace (prefixWord ++ tailWord_3268520) baseStart_3268520 baseEnd_3268520 := by
    simpa [prefixWord, tailWord_3268520, baseEnd_3268520] using wordTrace_append hprefix tailTrace_3268520
  have hstable : (prefixWord ++ tailWord_3268520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268520).length < 2 ^ (prefixWord ++ tailWord_3268520).sum := by decide
  have hdescent : baseEnd_3268520 < baseStart_3268520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268555 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4]
def baseStart_3268555 : Nat := 118140960795 + 3268555 * 2 ^ 59
def prefixEnd_3268555 : Nat := 4983230072969 + 3 ^ 40 * 3268555 * 2
def baseEnd_3268555 : Nat := 1678339760656564497230695

theorem tailTrace_3268555 : CollatzResearch.WordTrace tailWord_3268555 prefixEnd_3268555 1678339760656564497230695 := by
  unfold tailWord_3268555
  simp only [CollatzResearch.WordTrace]
  refine ⟨119213994673590934596567119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79475996449060623064378079 119213994673590934596567119)
  ·
    refine ⟨178820992010386401894850679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119213994673590934596567119 178820992010386401894850679)
    ·
      refine ⟨268231488015579602842276019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178820992010386401894850679 268231488015579602842276019)
      ·
        refine ⟨402347232023369404263414029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268231488015579602842276019 402347232023369404263414029)
        ·
          refine ⟨150880212008763526598780261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402347232023369404263414029 150880212008763526598780261)
          ·
            refine ⟨28290039751643161237271299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150880212008763526598780261 28290039751643161237271299)
            ·
              refine ⟨42435059627464741855906949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28290039751643161237271299 42435059627464741855906949)
              ·
                refine ⟨7956573680149639097982553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42435059627464741855906949 7956573680149639097982553)
                ·
                  refine ⟨5967430260112229323486915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956573680149639097982553 5967430260112229323486915)
                  ·
                    refine ⟨8951145390168343985230373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967430260112229323486915 8951145390168343985230373)
                    ·
                      refine ⟨1678339760656564497230695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8951145390168343985230373 1678339760656564497230695)
                      ·
                        rfl

theorem cell23_3268555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 4].length) (baseStart_3268555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268555 prefixEnd_3268555 := by exact prefixLift 3268555
  have htrace : WordTrace (prefixWord ++ tailWord_3268555) baseStart_3268555 baseEnd_3268555 := by
    simpa [prefixWord, tailWord_3268555, baseEnd_3268555] using wordTrace_append hprefix tailTrace_3268555
  have hstable : (prefixWord ++ tailWord_3268555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268555).length < 2 ^ (prefixWord ++ tailWord_3268555).sum := by decide
  have hdescent : baseEnd_3268555 < baseStart_3268555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268589 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3268589 : Nat := 118140960795 + 3268589 * 2 ^ 59
def prefixEnd_3268589 : Nat := 4983230072969 + 3 ^ 40 * 3268589 * 2
def baseEnd_3268589 : Nat := 1678357218998817364205539

theorem tailTrace_3268589 : CollatzResearch.WordTrace tailWord_3268589 prefixEnd_3268589 1678357218998817364205539 := by
  unfold tailWord_3268589
  simp only [CollatzResearch.WordTrace]
  refine ⟨119215234755467758403304821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79476823170311838935536547 119215234755467758403304821)
  ·
    refine ⟨11176428258325102350309827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119215234755467758403304821 11176428258325102350309827)
    ·
      refine ⟨16764642387487653525464741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11176428258325102350309827 16764642387487653525464741)
      ·
        refine ⟨3143370447653935036024639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16764642387487653525464741 3143370447653935036024639)
        ·
          refine ⟨4715055671480902554036959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143370447653935036024639 4715055671480902554036959)
          ·
            refine ⟨7072583507221353831055439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715055671480902554036959 7072583507221353831055439)
            ·
              refine ⟨10608875260832030746583159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072583507221353831055439 10608875260832030746583159)
              ·
                refine ⟨15913312891248046119874739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608875260832030746583159 15913312891248046119874739)
                ·
                  refine ⟨23869969336872069179812109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913312891248046119874739 23869969336872069179812109)
                  ·
                    refine ⟨8951238501327025942429541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23869969336872069179812109 8951238501327025942429541)
                    ·
                      refine ⟨1678357218998817364205539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8951238501327025942429541 1678357218998817364205539)
                      ·
                        rfl

theorem cell23_3268589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3268589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268589 prefixEnd_3268589 := by exact prefixLift 3268589
  have htrace : WordTrace (prefixWord ++ tailWord_3268589) baseStart_3268589 baseEnd_3268589 := by
    simpa [prefixWord, tailWord_3268589, baseEnd_3268589] using wordTrace_append hprefix tailTrace_3268589
  have hstable : (prefixWord ++ tailWord_3268589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268589).length < 2 ^ (prefixWord ++ tailWord_3268589).sum := by decide
  have hdescent : baseEnd_3268589 < baseStart_3268589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268592 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_3268592 : Nat := 118140960795 + 3268592 * 2 ^ 59
def prefixEnd_3268592 : Nat := 4983230072969 + 3 ^ 40 * 3268592 * 2
def baseEnd_3268592 : Nat := 1678358759440780852468025

theorem tailTrace_3268592 : CollatzResearch.WordTrace tailWord_3268592 prefixEnd_3268592 1678358759440780852468025 := by
  unfold tailWord_3268592
  simp only [CollatzResearch.WordTrace]
  refine ⟨59607672087228444957832015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79476896116304593277109353 59607672087228444957832015)
  ·
    refine ⟨89411508130842667436748023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59607672087228444957832015 89411508130842667436748023)
    ·
      refine ⟨134117262196264001155122035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89411508130842667436748023 134117262196264001155122035)
      ·
        refine ⟨201175893294396001732683053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134117262196264001155122035 201175893294396001732683053)
        ·
          refine ⟨75440959985398500649756145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201175893294396001732683053 75440959985398500649756145)
          ·
            refine ⟨56580719989048875487317109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75440959985398500649756145 56580719989048875487317109)
            ·
              refine ⟨5304442498973332076935979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56580719989048875487317109 5304442498973332076935979)
              ·
                refine ⟨7956663748459998115403969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304442498973332076935979 7956663748459998115403969)
                ·
                  refine ⟨5967497811344998586552977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956663748459998115403969 5967497811344998586552977)
                  ·
                    refine ⟨4475623358508748939914733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967497811344998586552977 4475623358508748939914733)
                    ·
                      refine ⟨1678358759440780852468025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475623358508748939914733 1678358759440780852468025)
                      ·
                        rfl

theorem cell23_3268592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_3268592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268592 prefixEnd_3268592 := by exact prefixLift 3268592
  have htrace : WordTrace (prefixWord ++ tailWord_3268592) baseStart_3268592 baseEnd_3268592 := by
    simpa [prefixWord, tailWord_3268592, baseEnd_3268592] using wordTrace_append hprefix tailTrace_3268592
  have hstable : (prefixWord ++ tailWord_3268592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268592).length < 2 ^ (prefixWord ++ tailWord_3268592).sum := by decide
  have hdescent : baseEnd_3268592 < baseStart_3268592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268615 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3268615 : Nat := 118140960795 + 3268615 * 2 ^ 59
def prefixEnd_3268615 : Nat := 4983230072969 + 3 ^ 40 * 3268615 * 2
def baseEnd_3268615 : Nat := 1678370569495834262480419

theorem tailTrace_3268615 : CollatzResearch.WordTrace tailWord_3268615 prefixEnd_3268615 1678370569495834262480419 := by
  unfold tailWord_3268615
  simp only [CollatzResearch.WordTrace]
  refine ⟨119216183053373564843751299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79477455368915709895834199 119216183053373564843751299)
  ·
    refine ⟨178824274580060347265626949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119216183053373564843751299 178824274580060347265626949)
    ·
      refine ⟨33529551483761315112305053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178824274580060347265626949 33529551483761315112305053)
      ·
        refine ⟨12573581806410493167114395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33529551483761315112305053 12573581806410493167114395)
        ·
          refine ⟨18860372709615739750671593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12573581806410493167114395 18860372709615739750671593)
          ·
            refine ⟨14145279532211804813003695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18860372709615739750671593 14145279532211804813003695)
            ·
              refine ⟨21217919298317707219505543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145279532211804813003695 21217919298317707219505543)
              ·
                refine ⟨31826878947476560829258315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21217919298317707219505543 31826878947476560829258315)
                ·
                  refine ⟨47740318421214841243887473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31826878947476560829258315 47740318421214841243887473)
                  ·
                    refine ⟨35805238815911130932915605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47740318421214841243887473 35805238815911130932915605)
                    ·
                      refine ⟨1678370569495834262480419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35805238815911130932915605 1678370569495834262480419)
                      ·
                        rfl

theorem cell23_3268615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3268615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268615 prefixEnd_3268615 := by exact prefixLift 3268615
  have htrace : WordTrace (prefixWord ++ tailWord_3268615) baseStart_3268615 baseEnd_3268615 := by
    simpa [prefixWord, tailWord_3268615, baseEnd_3268615] using wordTrace_append hprefix tailTrace_3268615
  have hstable : (prefixWord ++ tailWord_3268615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268615).length < 2 ^ (prefixWord ++ tailWord_3268615).sum := by decide
  have hdescent : baseEnd_3268615 < baseStart_3268615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268629 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 6]
def baseStart_3268629 : Nat := 118140960795 + 3268629 * 2 ^ 59
def prefixEnd_3268629 : Nat := 4983230072969 + 3 ^ 40 * 3268629 * 2
def baseEnd_3268629 : Nat := 186486417580555245300595

theorem tailTrace_3268629 : CollatzResearch.WordTrace tailWord_3268629 prefixEnd_3268629 186486417580555245300595 := by
  unfold tailWord_3268629
  simp only [CollatzResearch.WordTrace]
  refine ⟨119216693675322845234760941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79477795783548563489840627 119216693675322845234760941)
  ·
    refine ⟨44706260128246066963035353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119216693675322845234760941 44706260128246066963035353)
    ·
      refine ⟨33529695096184550222276515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44706260128246066963035353 33529695096184550222276515)
      ·
        refine ⟨50294542644276825333414773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33529695096184550222276515 50294542644276825333414773)
        ·
          refine ⟨4715113372900952375007635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50294542644276825333414773 4715113372900952375007635)
          ·
            refine ⟨7072670059351428562511453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715113372900952375007635 7072670059351428562511453)
            ·
              refine ⟨2652251272256785710941795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7072670059351428562511453 2652251272256785710941795)
              ·
                refine ⟨3978376908385178566412693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652251272256785710941795 3978376908385178566412693)
                ·
                  refine ⟨186486417580555245300595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978376908385178566412693 186486417580555245300595)
                  ·
                    rfl

theorem cell23_3268629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_3268629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268629 prefixEnd_3268629 := by exact prefixLift 3268629
  have htrace : WordTrace (prefixWord ++ tailWord_3268629) baseStart_3268629 baseEnd_3268629 := by
    simpa [prefixWord, tailWord_3268629, baseEnd_3268629] using wordTrace_append hprefix tailTrace_3268629
  have hstable : (prefixWord ++ tailWord_3268629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268629).length < 2 ^ (prefixWord ++ tailWord_3268629).sum := by decide
  have hdescent : baseEnd_3268629 < baseStart_3268629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268632 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3268632 : Nat := 118140960795 + 3268632 * 2 ^ 59
def prefixEnd_3268632 : Nat := 4983230072969 + 3 ^ 40 * 3268632 * 2
def baseEnd_3268632 : Nat := 1678379298666960695967841

theorem tailTrace_3268632 : CollatzResearch.WordTrace tailWord_3268632 prefixEnd_3268632 1678379298666960695967841 := by
  unfold tailWord_3268632
  simp only [CollatzResearch.WordTrace]
  refine ⟨59608401547155988373560075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79477868729541317831413433 59608401547155988373560075)
  ·
    refine ⟨89412602320733982560340113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59608401547155988373560075 89412602320733982560340113)
    ·
      refine ⟨67059451740550486920255085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89412602320733982560340113 67059451740550486920255085)
      ·
        refine ⟨25147294402706432595095657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67059451740550486920255085 25147294402706432595095657)
        ·
          refine ⟨18860470802029824446321743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25147294402706432595095657 18860470802029824446321743)
          ·
            refine ⟨28290706203044736669482615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18860470802029824446321743 28290706203044736669482615)
            ·
              refine ⟨42436059304567105004223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28290706203044736669482615 42436059304567105004223923)
              ·
                refine ⟨63654088956850657506335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42436059304567105004223923 63654088956850657506335885)
                ·
                  refine ⟨23870283358818996564875957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63654088956850657506335885 23870283358818996564875957)
                  ·
                    refine ⟨2237839064889280927957121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23870283358818996564875957 2237839064889280927957121)
                    ·
                      refine ⟨1678379298666960695967841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237839064889280927957121 1678379298666960695967841)
                      ·
                        rfl

theorem cell23_3268632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3268632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268632 prefixEnd_3268632 := by exact prefixLift 3268632
  have htrace : WordTrace (prefixWord ++ tailWord_3268632) baseStart_3268632 baseEnd_3268632 := by
    simpa [prefixWord, tailWord_3268632, baseEnd_3268632] using wordTrace_append hprefix tailTrace_3268632
  have hstable : (prefixWord ++ tailWord_3268632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268632).length < 2 ^ (prefixWord ++ tailWord_3268632).sum := by decide
  have hdescent : baseEnd_3268632 < baseStart_3268632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268656 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 1, 1, 3]
def baseStart_3268656 : Nat := 118140960795 + 3268656 * 2 ^ 59
def prefixEnd_3268656 : Nat := 4983230072969 + 3 ^ 40 * 3268656 * 2
def baseEnd_3268656 : Nat := 1678391622202668602067731

theorem tailTrace_3268656 : CollatzResearch.WordTrace tailWord_3268656 prefixEnd_3268656 1678391622202668602067731 := by
  unfold tailWord_3268656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59608839223112514422996911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79478452297483352563995881 59608839223112514422996911)
  ·
    refine ⟨89413258834668771634495367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59608839223112514422996911 89413258834668771634495367)
    ·
      refine ⟨134119888252003157451743051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89413258834668771634495367 134119888252003157451743051)
      ·
        refine ⟨201179832378004736177614577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134119888252003157451743051 201179832378004736177614577)
        ·
          refine ⟨150884874283503552133210933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201179832378004736177614577 150884874283503552133210933)
          ·
            refine ⟨14145456964078458012488525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150884874283503552133210933 14145456964078458012488525)
            ·
              refine ⟨5304546361529421754683197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14145456964078458012488525 5304546361529421754683197)
              ·
                refine ⟨1989204885573533158006199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5304546361529421754683197 1989204885573533158006199)
                ·
                  refine ⟨2983807328360299737009299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989204885573533158006199 2983807328360299737009299)
                  ·
                    refine ⟨4475710992540449605513949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983807328360299737009299 4475710992540449605513949)
                    ·
                      refine ⟨1678391622202668602067731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475710992540449605513949 1678391622202668602067731)
                      ·
                        rfl

theorem cell23_3268656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 1, 3].length) (baseStart_3268656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268656 prefixEnd_3268656 := by exact prefixLift 3268656
  have htrace : WordTrace (prefixWord ++ tailWord_3268656) baseStart_3268656 baseEnd_3268656 := by
    simpa [prefixWord, tailWord_3268656, baseEnd_3268656] using wordTrace_append hprefix tailTrace_3268656
  have hstable : (prefixWord ++ tailWord_3268656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268656).length < 2 ^ (prefixWord ++ tailWord_3268656).sum := by decide
  have hdescent : baseEnd_3268656 < baseStart_3268656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268672 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_3268672 : Nat := 118140960795 + 3268672 * 2 ^ 59
def prefixEnd_3268672 : Nat := 4983230072969 + 3 ^ 40 * 3268672 * 2
def baseEnd_3268672 : Nat := 559466612631046846489219

theorem tailTrace_3268672 : CollatzResearch.WordTrace tailWord_3268672 prefixEnd_3268672 559466612631046846489219 := by
  unfold tailWord_3268672
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609131007083531789288135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79478841342778042385717513 59609131007083531789288135)
  ·
    refine ⟨89413696510625297683932203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59609131007083531789288135 89413696510625297683932203)
    ·
      refine ⟨134120544765937946525898305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89413696510625297683932203 134120544765937946525898305)
      ·
        refine ⟨100590408574453459894423729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134120544765937946525898305 100590408574453459894423729)
        ·
          refine ⟨75442806430840094920817797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100590408574453459894423729 75442806430840094920817797)
          ·
            refine ⟨14145526205782517797653337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75442806430840094920817797 14145526205782517797653337)
            ·
              refine ⟨10609144654336888348240003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14145526205782517797653337 10609144654336888348240003)
              ·
                refine ⟨15913716981505332522360005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609144654336888348240003 15913716981505332522360005)
                ·
                  refine ⟨2983821934032249847942501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15913716981505332522360005 2983821934032249847942501)
                  ·
                    refine ⟨559466612631046846489219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983821934032249847942501 559466612631046846489219)
                    ·
                      rfl

theorem cell23_3268672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_3268672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268672 prefixEnd_3268672 := by exact prefixLift 3268672
  have htrace : WordTrace (prefixWord ++ tailWord_3268672) baseStart_3268672 baseEnd_3268672 := by
    simpa [prefixWord, tailWord_3268672, baseEnd_3268672] using wordTrace_append hprefix tailTrace_3268672
  have hstable : (prefixWord ++ tailWord_3268672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268672).length < 2 ^ (prefixWord ++ tailWord_3268672).sum := by decide
  have hdescent : baseEnd_3268672 < baseStart_3268672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268675 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_3268675 : Nat := 118140960795 + 3268675 * 2 ^ 59
def prefixEnd_3268675 : Nat := 4983230072969 + 3 ^ 40 * 3268675 * 2
def baseEnd_3268675 : Nat := 1678401378335104027730143

theorem tailTrace_3268675 : CollatzResearch.WordTrace tailWord_3268675 prefixEnd_3268675 1678401378335104027730143 := by
  unfold tailWord_3268675
  simp only [CollatzResearch.WordTrace]
  refine ⟨119218371433156195090935479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79478914288770796727290319 119218371433156195090935479)
  ·
    refine ⟨178827557149734292636403219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119218371433156195090935479 178827557149734292636403219)
    ·
      refine ⟨268241335724601438954604829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178827557149734292636403219 268241335724601438954604829)
      ·
        refine ⟨100590500896725539607976811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268241335724601438954604829 100590500896725539607976811)
        ·
          refine ⟨150885751345088309411965217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100590500896725539607976811 150885751345088309411965217)
          ·
            refine ⟨113164313508816232058973913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150885751345088309411965217 113164313508816232058973913)
            ·
              refine ⟨84873235131612174044230435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113164313508816232058973913 84873235131612174044230435)
              ·
                refine ⟨127309852697418261066345653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84873235131612174044230435 127309852697418261066345653)
                ·
                  refine ⟨11935298690382961974969905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127309852697418261066345653 11935298690382961974969905)
                  ·
                    refine ⟨8951474017787221481227429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11935298690382961974969905 8951474017787221481227429)
                    ·
                      refine ⟨1678401378335104027730143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8951474017787221481227429 1678401378335104027730143)
                      ·
                        rfl

theorem cell23_3268675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_3268675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268675 prefixEnd_3268675 := by exact prefixLift 3268675
  have htrace : WordTrace (prefixWord ++ tailWord_3268675) baseStart_3268675 baseEnd_3268675 := by
    simpa [prefixWord, tailWord_3268675, baseEnd_3268675] using wordTrace_append hprefix tailTrace_3268675
  have hstable : (prefixWord ++ tailWord_3268675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268675).length < 2 ^ (prefixWord ++ tailWord_3268675).sum := by decide
  have hdescent : baseEnd_3268675 < baseStart_3268675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268682 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3268682 : Nat := 118140960795 + 3268682 * 2 ^ 59
def prefixEnd_3268682 : Nat := 4983230072969 + 3 ^ 40 * 3268682 * 2
def baseEnd_3268682 : Nat := 1678404972699685500342611

theorem tailTrace_3268682 : CollatzResearch.WordTrace tailWord_3268682 prefixEnd_3268682 1678404972699685500342611 := by
  unfold tailWord_3268682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29804656686032708821610075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79479084496087223524293533 29804656686032708821610075)
  ·
    refine ⟨44706985029049063232415113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29804656686032708821610075 44706985029049063232415113)
    ·
      refine ⟨33530238771786797424311335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44706985029049063232415113 33530238771786797424311335)
      ·
        refine ⟨50295358157680196136467003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33530238771786797424311335 50295358157680196136467003)
        ·
          refine ⟨75443037236520294204700505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50295358157680196136467003 75443037236520294204700505)
          ·
            refine ⟨56582277927390220653525379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75443037236520294204700505 56582277927390220653525379)
            ·
              refine ⟨84873416891085330980288069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56582277927390220653525379 84873416891085330980288069)
              ·
                refine ⟨15913765667078499558804013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84873416891085330980288069 15913765667078499558804013)
                ·
                  refine ⟨5967662125154437334551505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15913765667078499558804013 5967662125154437334551505)
                  ·
                    refine ⟨4475746593865828000913629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967662125154437334551505 4475746593865828000913629)
                    ·
                      refine ⟨1678404972699685500342611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475746593865828000913629 1678404972699685500342611)
                      ·
                        rfl

theorem cell23_3268682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3268682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268682 prefixEnd_3268682 := by exact prefixLift 3268682
  have htrace : WordTrace (prefixWord ++ tailWord_3268682) baseStart_3268682 baseEnd_3268682 := by
    simpa [prefixWord, tailWord_3268682, baseEnd_3268682] using wordTrace_append hprefix tailTrace_3268682
  have hstable : (prefixWord ++ tailWord_3268682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268682).length < 2 ^ (prefixWord ++ tailWord_3268682).sum := by decide
  have hdescent : baseEnd_3268682 < baseStart_3268682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268692 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3268692 : Nat := 118140960795 + 3268692 * 2 ^ 59
def prefixEnd_3268692 : Nat := 4983230072969 + 3 ^ 40 * 3268692 * 2
def baseEnd_3268692 : Nat := 1678410107506230461217565

theorem tailTrace_3268692 : CollatzResearch.WordTrace tailWord_3268692 prefixEnd_3268692 1678410107506230461217565 := by
  unfold tailWord_3268692
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609495737047303497152165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79479327649396404662869553 59609495737047303497152165)
  ·
    refine ⟨11176780450696369405716031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59609495737047303497152165 11176780450696369405716031)
    ·
      refine ⟨16765170676044554108574047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11176780450696369405716031 16765170676044554108574047)
      ·
        refine ⟨25147756014066831162861071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16765170676044554108574047 25147756014066831162861071)
        ·
          refine ⟨37721634021100246744291607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25147756014066831162861071 37721634021100246744291607)
          ·
            refine ⟨56582451031650370116437411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37721634021100246744291607 56582451031650370116437411)
            ·
              refine ⟨84873676547475555174656117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56582451031650370116437411 84873676547475555174656117)
              ·
                refine ⟨7956907176325833297624011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84873676547475555174656117 7956907176325833297624011)
                ·
                  refine ⟨11935360764488749946436017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7956907176325833297624011 11935360764488749946436017)
                  ·
                    refine ⟨8951520573366562459827013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11935360764488749946436017 8951520573366562459827013)
                    ·
                      refine ⟨1678410107506230461217565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8951520573366562459827013 1678410107506230461217565)
                      ·
                        rfl

theorem cell23_3268692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3268692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268692 prefixEnd_3268692 := by exact prefixLift 3268692
  have htrace : WordTrace (prefixWord ++ tailWord_3268692) baseStart_3268692 baseEnd_3268692 := by
    simpa [prefixWord, tailWord_3268692, baseEnd_3268692] using wordTrace_append hprefix tailTrace_3268692
  have hstable : (prefixWord ++ tailWord_3268692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268692).length < 2 ^ (prefixWord ++ tailWord_3268692).sum := by decide
  have hdescent : baseEnd_3268692 < baseStart_3268692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268716 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_3268716 : Nat := 118140960795 + 3268716 * 2 ^ 59
def prefixEnd_3268716 : Nat := 4983230072969 + 3 ^ 40 * 3268716 * 2
def baseEnd_3268716 : Nat := 1678422431041938367317455

theorem tailTrace_3268716 : CollatzResearch.WordTrace tailWord_3268716 prefixEnd_3268716 1678422431041938367317455 := by
  unfold tailWord_3268716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59609933413003829546589001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79479911217338439395452001 59609933413003829546589001)
  ·
    refine ⟨44707450059752872159941751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59609933413003829546589001 44707450059752872159941751)
    ·
      refine ⟨67061175089629308239912627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44707450059752872159941751 67061175089629308239912627)
      ·
        refine ⟨100591762634443962359868941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67061175089629308239912627 100591762634443962359868941)
        ·
          refine ⟨37721910987916485884950853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100591762634443962359868941 37721910987916485884950853)
          ·
            refine ⟨7072858310234341103428285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37721910987916485884950853 7072858310234341103428285)
            ·
              refine ⟨2652321866337877913785607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7072858310234341103428285 2652321866337877913785607)
              ·
                refine ⟨3978482799506816870678411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652321866337877913785607 3978482799506816870678411)
                ·
                  refine ⟨5967724199260225306017617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978482799506816870678411 5967724199260225306017617)
                  ·
                    refine ⟨4475793149445168979513213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967724199260225306017617 4475793149445168979513213)
                    ·
                      refine ⟨1678422431041938367317455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475793149445168979513213 1678422431041938367317455)
                      ·
                        rfl

theorem cell23_3268716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_3268716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268716 prefixEnd_3268716 := by exact prefixLift 3268716
  have htrace : WordTrace (prefixWord ++ tailWord_3268716) baseStart_3268716 baseEnd_3268716 := by
    simpa [prefixWord, tailWord_3268716, baseEnd_3268716] using wordTrace_append hprefix tailTrace_3268716
  have hstable : (prefixWord ++ tailWord_3268716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268716).length < 2 ^ (prefixWord ++ tailWord_3268716).sum := by decide
  have hdescent : baseEnd_3268716 < baseStart_3268716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268739 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 3, 3, 2]
def baseStart_3268739 : Nat := 118140960795 + 3268739 * 2 ^ 59
def prefixEnd_3268739 : Nat := 4983230072969 + 3 ^ 40 * 3268739 * 2
def baseEnd_3268739 : Nat := 1678434241096991777329849

theorem tailTrace_3268739 : CollatzResearch.WordTrace tailWord_3268739 prefixEnd_3268739 1678434241096991777329849 := by
  unfold tailWord_3268739
  simp only [CollatzResearch.WordTrace]
  refine ⟨119220705704924334021265271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79480470469949556014176847 119220705704924334021265271)
  ·
    refine ⟨178831058557386501031897907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119220705704924334021265271 178831058557386501031897907)
    ·
      refine ⟨268246587836079751547846861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178831058557386501031897907 268246587836079751547846861)
      ·
        refine ⟨100592470438529906830442573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268246587836079751547846861 100592470438529906830442573)
        ·
          refine ⟨37722176414448715061415965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100592470438529906830442573 37722176414448715061415965)
          ·
            refine ⟨14145816155418268148030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37722176414448715061415965 14145816155418268148030987)
            ·
              refine ⟨21218724233127402222046481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145816155418268148030987 21218724233127402222046481)
              ·
                refine ⟨15914043174845551666534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21218724233127402222046481 15914043174845551666534861)
                ·
                  refine ⟨5967766190567081874950573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15914043174845551666534861 5967766190567081874950573)
                  ·
                    refine ⟨2237912321462655703106465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5967766190567081874950573 2237912321462655703106465)
                    ·
                      refine ⟨1678434241096991777329849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237912321462655703106465 1678434241096991777329849)
                      ·
                        rfl

theorem cell23_3268739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_3268739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268739 prefixEnd_3268739 := by exact prefixLift 3268739
  have htrace : WordTrace (prefixWord ++ tailWord_3268739) baseStart_3268739 baseEnd_3268739 := by
    simpa [prefixWord, tailWord_3268739, baseEnd_3268739] using wordTrace_append hprefix tailTrace_3268739
  have hstable : (prefixWord ++ tailWord_3268739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268739).length < 2 ^ (prefixWord ++ tailWord_3268739).sum := by decide
  have hdescent : baseEnd_3268739 < baseStart_3268739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268746 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3268746 : Nat := 118140960795 + 3268746 * 2 ^ 59
def prefixEnd_3268746 : Nat := 4983230072969 + 3 ^ 40 * 3268746 * 2
def baseEnd_3268746 : Nat := 1678437835461573249942317

theorem tailTrace_3268746 : CollatzResearch.WordTrace tailWord_3268746 prefixEnd_3268746 1678437835461573249942317 := by
  unfold tailWord_3268746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29805240253974743554192523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79480640677265982811180061 29805240253974743554192523)
  ·
    refine ⟨44707860380962115331288785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29805240253974743554192523 44707860380962115331288785)
    ·
      refine ⟨33530895285721586498466589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44707860380962115331288785 33530895285721586498466589)
      ·
        refine ⟨12574085732145594936924971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33530895285721586498466589 12574085732145594936924971)
        ·
          refine ⟨18861128598218392405387457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574085732145594936924971 18861128598218392405387457)
          ·
            refine ⟨14145846448663794304040593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18861128598218392405387457 14145846448663794304040593)
            ·
              refine ⟨10609384836497845728030445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14145846448663794304040593 10609384836497845728030445)
              ·
                refine ⟨3978519313686692148011417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10609384836497845728030445 3978519313686692148011417)
                ·
                  refine ⟨2983889485265019111008563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978519313686692148011417 2983889485265019111008563)
                  ·
                    refine ⟨4475834227897528666512845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983889485265019111008563 4475834227897528666512845)
                    ·
                      refine ⟨1678437835461573249942317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4475834227897528666512845 1678437835461573249942317)
                      ·
                        rfl

theorem cell23_3268746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3268746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268746 prefixEnd_3268746 := by exact prefixLift 3268746
  have htrace : WordTrace (prefixWord ++ tailWord_3268746) baseStart_3268746 baseEnd_3268746 := by
    simpa [prefixWord, tailWord_3268746, baseEnd_3268746] using wordTrace_append hprefix tailTrace_3268746
  have hstable : (prefixWord ++ tailWord_3268746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268746).length < 2 ^ (prefixWord ++ tailWord_3268746).sum := by decide
  have hdescent : baseEnd_3268746 < baseStart_3268746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268786 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_3268786 : Nat := 118140960795 + 3268786 * 2 ^ 59
def prefixEnd_3268786 : Nat := 4983230072969 + 3 ^ 40 * 3268786 * 2
def baseEnd_3268786 : Nat := 1678458374687753093442133

theorem tailTrace_3268786 : CollatzResearch.WordTrace tailWord_3268786 prefixEnd_3268786 1678458374687753093442133 := by
  unfold tailWord_3268786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29805604983938515262056553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79481613290502707365484141 29805604983938515262056553)
  ·
    refine ⟨22354203737953886446542415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29805604983938515262056553 22354203737953886446542415)
    ·
      refine ⟨33531305606930829669813623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22354203737953886446542415 33531305606930829669813623)
      ·
        refine ⟨50296958410396244504720435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33531305606930829669813623 50296958410396244504720435)
        ·
          refine ⟨75445437615594366757080653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50296958410396244504720435 75445437615594366757080653)
          ·
            refine ⟨28292039105847887533905245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75445437615594366757080653 28292039105847887533905245)
            ·
              refine ⟨10609514664692957825214467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28292039105847887533905245 10609514664692957825214467)
              ·
                refine ⟨15914271997039436737821701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609514664692957825214467 15914271997039436737821701)
                ·
                  refine ⟨2983925999444894388341569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15914271997039436737821701 2983925999444894388341569)
                  ·
                    refine ⟨2237944499583670791256177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2983925999444894388341569 2237944499583670791256177)
                    ·
                      refine ⟨1678458374687753093442133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2237944499583670791256177 1678458374687753093442133)
                      ·
                        rfl

theorem cell23_3268786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_3268786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268786 prefixEnd_3268786 := by exact prefixLift 3268786
  have htrace : WordTrace (prefixWord ++ tailWord_3268786) baseStart_3268786 baseEnd_3268786 := by
    simpa [prefixWord, tailWord_3268786, baseEnd_3268786] using wordTrace_append hprefix tailTrace_3268786
  have hstable : (prefixWord ++ tailWord_3268786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268786).length < 2 ^ (prefixWord ++ tailWord_3268786).sum := by decide
  have hdescent : baseEnd_3268786 < baseStart_3268786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268792 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 7]
def baseStart_3268792 : Nat := 118140960795 + 3268792 * 2 ^ 59
def prefixEnd_3268792 : Nat := 4983230072969 + 3 ^ 40 * 3268792 * 2
def baseEnd_3268792 : Nat := 186495717285742229996345

theorem tailTrace_3268792 : CollatzResearch.WordTrace tailWord_3268792 prefixEnd_3268792 186495717285742229996345 := by
  unfold tailWord_3268792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59611319386866162036472315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79481759182488216048629753 59611319386866162036472315)
  ·
    refine ⟨89416979080299243054708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59611319386866162036472315 89416979080299243054708473)
    ·
      refine ⟨67062734310224432291031355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89416979080299243054708473 67062734310224432291031355)
      ·
        refine ⟨100594101465336648436547033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67062734310224432291031355 100594101465336648436547033)
        ·
          refine ⟨75445576099002486327410275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100594101465336648436547033 75445576099002486327410275)
          ·
            refine ⟨113168364148503729491115413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75445576099002486327410275 113168364148503729491115413)
            ·
              refine ⟨5304767069461112319896035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113168364148503729491115413 5304767069461112319896035)
              ·
                refine ⟨7957150604191668479844053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304767069461112319896035 7957150604191668479844053)
                ·
                  refine ⟨186495717285742229996345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7957150604191668479844053 186495717285742229996345)
                  ·
                    rfl

theorem cell23_3268792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_3268792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268792 prefixEnd_3268792 := by exact prefixLift 3268792
  have htrace : WordTrace (prefixWord ++ tailWord_3268792) baseStart_3268792 baseEnd_3268792 := by
    simpa [prefixWord, tailWord_3268792, baseEnd_3268792] using wordTrace_append hprefix tailTrace_3268792
  have hstable : (prefixWord ++ tailWord_3268792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268792).length < 2 ^ (prefixWord ++ tailWord_3268792).sum := by decide
  have hdescent : baseEnd_3268792 < baseStart_3268792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268832 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3268832 : Nat := 118140960795 + 3268832 * 2 ^ 59
def prefixEnd_3268832 : Nat := 4983230072969 + 3 ^ 40 * 3268832 * 2
def baseEnd_3268832 : Nat := 1678481994797859913466921

theorem tailTrace_3268832 : CollatzResearch.WordTrace tailWord_3268832 prefixEnd_3268832 1678481994797859913466921 := by
  unfold tailWord_3268832
  simp only [CollatzResearch.WordTrace]
  refine ⟨59612048846793705452200375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79482731795724940602933833 59612048846793705452200375)
  ·
    refine ⟨89418073270190558178300563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59612048846793705452200375 89418073270190558178300563)
    ·
      refine ⟨134127109905285837267450845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89418073270190558178300563 134127109905285837267450845)
      ·
        refine ⟨50297666214482188975294067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134127109905285837267450845 50297666214482188975294067)
        ·
          refine ⟨75446499321723283462941101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50297666214482188975294067 75446499321723283462941101)
          ·
            refine ⟨28292437245646231298602913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75446499321723283462941101 28292437245646231298602913)
            ·
              refine ⟨21219327934234673473952185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28292437245646231298602913 21219327934234673473952185)
              ·
                refine ⟨15914495950676005105464139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21219327934234673473952185 15914495950676005105464139)
                ·
                  refine ⟨23871743926014007658196209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15914495950676005105464139 23871743926014007658196209)
                  ·
                    refine ⟨17903807944510505743647157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23871743926014007658196209 17903807944510505743647157)
                    ·
                      refine ⟨1678481994797859913466921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17903807944510505743647157 1678481994797859913466921)
                      ·
                        rfl

theorem cell23_3268832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3268832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268832 prefixEnd_3268832 := by exact prefixLift 3268832
  have htrace : WordTrace (prefixWord ++ tailWord_3268832) baseStart_3268832 baseEnd_3268832 := by
    simpa [prefixWord, tailWord_3268832, baseEnd_3268832] using wordTrace_append hprefix tailTrace_3268832
  have hstable : (prefixWord ++ tailWord_3268832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268832).length < 2 ^ (prefixWord ++ tailWord_3268832).sum := by decide
  have hdescent : baseEnd_3268832 < baseStart_3268832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268839 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3268839 : Nat := 118140960795 + 3268839 * 2 ^ 59
def prefixEnd_3268839 : Nat := 4983230072969 + 3 ^ 40 * 3268839 * 2
def baseEnd_3268839 : Nat := 559495196387480462026463

theorem tailTrace_3268839 : CollatzResearch.WordTrace tailWord_3268839 prefixEnd_3268839 559495196387480462026463 := by
  unfold tailWord_3268839
  simp only [CollatzResearch.WordTrace]
  refine ⟨119224353004562051099905571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79482902003041367399937047 119224353004562051099905571)
  ·
    refine ⟨178836529506843076649858357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119224353004562051099905571 178836529506843076649858357)
    ·
      refine ⟨16765924641266538435924221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178836529506843076649858357 16765924641266538435924221)
      ·
        refine ⟨6287221740474951913471583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16765924641266538435924221 6287221740474951913471583)
        ·
          refine ⟨9430832610712427870207375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287221740474951913471583 9430832610712427870207375)
          ·
            refine ⟨14146248916068641805311063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430832610712427870207375 14146248916068641805311063)
            ·
              refine ⟨21219373374102962707966595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146248916068641805311063 21219373374102962707966595)
              ·
                refine ⟨31829060061154444061949893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21219373374102962707966595 31829060061154444061949893)
                ·
                  refine ⟨5967948761466458261615605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31829060061154444061949893 5967948761466458261615605)
                  ·
                    refine ⟨559495196387480462026463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5967948761466458261615605 559495196387480462026463)
                    ·
                      rfl

theorem cell23_3268839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3268839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268839 prefixEnd_3268839 := by exact prefixLift 3268839
  have htrace : WordTrace (prefixWord ++ tailWord_3268839) baseStart_3268839 baseEnd_3268839 := by
    simpa [prefixWord, tailWord_3268839, baseEnd_3268839] using wordTrace_append hprefix tailTrace_3268839
  have hstable : (prefixWord ++ tailWord_3268839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268839).length < 2 ^ (prefixWord ++ tailWord_3268839).sum := by decide
  have hdescent : baseEnd_3268839 < baseStart_3268839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268896 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3268896 : Nat := 118140960795 + 3268896 * 2 ^ 59
def prefixEnd_3268896 : Nat := 4983230072969 + 3 ^ 40 * 3268896 * 2
def baseEnd_3268896 : Nat := 1678514857559747663066627

theorem tailTrace_3268896 : CollatzResearch.WordTrace tailWord_3268896 prefixEnd_3268896 1678514857559747663066627 := by
  unfold tailWord_3268896
  simp only [CollatzResearch.WordTrace]
  refine ⟨59613215982677774917365271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79484287976903699889820361 59613215982677774917365271)
  ·
    refine ⟨89419823974016662376047907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59613215982677774917365271 89419823974016662376047907)
    ·
      refine ⟨134129735961024993564071861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89419823974016662376047907 134129735961024993564071861)
      ·
        refine ⟨12574662746346093146631737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134129735961024993564071861 12574662746346093146631737)
        ·
          refine ⟨9430997059759569859973803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12574662746346093146631737 9430997059759569859973803)
          ·
            refine ⟨14146495589639354789960705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430997059759569859973803 14146495589639354789960705)
            ·
              refine ⟨10609871692229516092470529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146495589639354789960705 10609871692229516092470529)
              ·
                refine ⟨7957403769172137069352897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10609871692229516092470529 7957403769172137069352897)
                ·
                  refine ⟨5968052826879102802014673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7957403769172137069352897 5968052826879102802014673)
                  ·
                    refine ⟨4476039620159327101511005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968052826879102802014673 4476039620159327101511005)
                    ·
                      refine ⟨1678514857559747663066627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476039620159327101511005 1678514857559747663066627)
                      ·
                        rfl

theorem cell23_3268896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3268896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268896 prefixEnd_3268896 := by exact prefixLift 3268896
  have htrace : WordTrace (prefixWord ++ tailWord_3268896) baseStart_3268896 baseEnd_3268896 := by
    simpa [prefixWord, tailWord_3268896, baseEnd_3268896] using wordTrace_append hprefix tailTrace_3268896
  have hstable : (prefixWord ++ tailWord_3268896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268896).length < 2 ^ (prefixWord ++ tailWord_3268896).sum := by decide
  have hdescent : baseEnd_3268896 < baseStart_3268896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268899 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 6]
def baseStart_3268899 : Nat := 118140960795 + 3268899 * 2 ^ 59
def prefixEnd_3268899 : Nat := 4983230072969 + 3 ^ 40 * 3268899 * 2
def baseEnd_3268899 : Nat := 186501822000190127925457

theorem tailTrace_3268899 : CollatzResearch.WordTrace tailWord_3268899 prefixEnd_3268899 186501822000190127925457 := by
  unfold tailWord_3268899
  simp only [CollatzResearch.WordTrace]
  refine ⟨119226541384344681347089751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79484360922896454231393167 119226541384344681347089751)
  ·
    refine ⟨178839812076517022020634627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119226541384344681347089751 178839812076517022020634627)
    ·
      refine ⟨268259718114775533030951941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178839812076517022020634627 268259718114775533030951941)
      ·
        refine ⟨50298697146520412443303489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268259718114775533030951941 50298697146520412443303489)
        ·
          refine ⟨37724022859890309332477617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50298697146520412443303489 37724022859890309332477617)
          ·
            refine ⟨28293017144917731999358213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37724022859890309332477617 28293017144917731999358213)
            ·
              refine ⟨5304940714672074749879665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28293017144917731999358213 5304940714672074749879665)
              ·
                refine ⟨3978705536004056062409749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304940714672074749879665 3978705536004056062409749)
                ·
                  refine ⟨186501822000190127925457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978705536004056062409749 186501822000190127925457)
                  ·
                    rfl

theorem cell23_3268899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 6].length) (baseStart_3268899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268899 prefixEnd_3268899 := by exact prefixLift 3268899
  have htrace : WordTrace (prefixWord ++ tailWord_3268899) baseStart_3268899 baseEnd_3268899 := by
    simpa [prefixWord, tailWord_3268899, baseEnd_3268899] using wordTrace_append hprefix tailTrace_3268899
  have hstable : (prefixWord ++ tailWord_3268899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268899).length < 2 ^ (prefixWord ++ tailWord_3268899).sum := by decide
  have hdescent : baseEnd_3268899 < baseStart_3268899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268910 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3268910 : Nat := 118140960795 + 3268910 * 2 ^ 59
def prefixEnd_3268910 : Nat := 4983230072969 + 3 ^ 40 * 3268910 * 2
def baseEnd_3268910 : Nat := 1678522046288910608291563

theorem tailTrace_3268910 : CollatzResearch.WordTrace tailWord_3268910 prefixEnd_3268910 1678522046288910608291563 := by
  unfold tailWord_3268910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903367823413103778217523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79484628391536553483826789 14903367823413103778217523)
  ·
    refine ⟨22355051735119655667326285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903367823413103778217523 22355051735119655667326285)
    ·
      refine ⟨8383144400669870875247357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22355051735119655667326285 8383144400669870875247357)
      ·
        refine ⟨3143679150251201578217759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8383144400669870875247357 3143679150251201578217759)
        ·
          refine ⟨4715518725376802367326639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143679150251201578217759 4715518725376802367326639)
          ·
            refine ⟨7073278088065203550989959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715518725376802367326639 7073278088065203550989959)
            ·
              refine ⟨10609917132097805326484939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073278088065203550989959 10609917132097805326484939)
              ·
                refine ⟨15914875698146707989727409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609917132097805326484939 15914875698146707989727409)
                ·
                  refine ⟨11936156773610030992295557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15914875698146707989727409 11936156773610030992295557)
                  ·
                    refine ⟨2238029395051880811055417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11936156773610030992295557 2238029395051880811055417)
                    ·
                      refine ⟨1678522046288910608291563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238029395051880811055417 1678522046288910608291563)
                      ·
                        rfl

theorem cell23_3268910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3268910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268910 prefixEnd_3268910 := by exact prefixLift 3268910
  have htrace : WordTrace (prefixWord ++ tailWord_3268910) baseStart_3268910 baseEnd_3268910 := by
    simpa [prefixWord, tailWord_3268910, baseEnd_3268910] using wordTrace_append hprefix tailTrace_3268910
  have hstable : (prefixWord ++ tailWord_3268910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268910).length < 2 ^ (prefixWord ++ tailWord_3268910).sum := by decide
  have hdescent : baseEnd_3268910 < baseStart_3268910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268916 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3268916 : Nat := 118140960795 + 3268916 * 2 ^ 59
def prefixEnd_3268916 : Nat := 4983230072969 + 3 ^ 40 * 3268916 * 2
def baseEnd_3268916 : Nat := 186502791908093064979615

theorem tailTrace_3268916 : CollatzResearch.WordTrace tailWord_3268916 prefixEnd_3268916 186502791908093064979615 := by
  unfold tailWord_3268916
  simp only [CollatzResearch.WordTrace]
  refine ⟨59613580712641546625229301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79484774283522062166972401 59613580712641546625229301)
  ·
    refine ⟨5588773191810144996115247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59613580712641546625229301 5588773191810144996115247)
    ·
      refine ⟨8383159787715217494172871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588773191810144996115247 8383159787715217494172871)
      ·
        refine ⟨12574739681572826241259307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383159787715217494172871 12574739681572826241259307)
        ·
          refine ⟨18862109522359239361888961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574739681572826241259307 18862109522359239361888961)
          ·
            refine ⟨14146582141769429521416721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18862109522359239361888961 14146582141769429521416721)
            ·
              refine ⟨10609936606327072141062541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14146582141769429521416721 10609936606327072141062541)
              ·
                refine ⟨3978726227372652052898453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10609936606327072141062541 3978726227372652052898453)
                ·
                  refine ⟨186502791908093064979615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978726227372652052898453 186502791908093064979615)
                  ·
                    rfl

theorem cell23_3268916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3268916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268916 prefixEnd_3268916 := by exact prefixLift 3268916
  have htrace : WordTrace (prefixWord ++ tailWord_3268916) baseStart_3268916 baseEnd_3268916 := by
    simpa [prefixWord, tailWord_3268916, baseEnd_3268916] using wordTrace_append hprefix tailTrace_3268916
  have hstable : (prefixWord ++ tailWord_3268916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268916).length < 2 ^ (prefixWord ++ tailWord_3268916).sum := by decide
  have hdescent : baseEnd_3268916 < baseStart_3268916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268969 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_3268969 : Nat := 118140960795 + 3268969 * 2 ^ 59
def prefixEnd_3268969 : Nat := 4983230072969 + 3 ^ 40 * 3268969 * 2
def baseEnd_3268969 : Nat := 1678552341647525877453791

theorem tailTrace_3268969 : CollatzResearch.WordTrace tailWord_3268969 prefixEnd_3268969 1678552341647525877453791 := by
  unfold tailWord_3268969
  simp only [CollatzResearch.WordTrace]
  refine ⟨119229094494091083302137961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79486062996060722201425307 119229094494091083302137961)
  ·
    refine ⟨89421820870568312476603471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119229094494091083302137961 89421820870568312476603471)
    ·
      refine ⟨134132731305852468714905207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89421820870568312476603471 134132731305852468714905207)
      ·
        refine ⟨201199096958778703072357811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134132731305852468714905207 201199096958778703072357811)
        ·
          refine ⟨301798645438168054608536717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201199096958778703072357811 301798645438168054608536717)
          ·
            refine ⟨113174492039313020478201269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301798645438168054608536717 113174492039313020478201269)
            ·
              refine ⟨10610108628685595669831369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113174492039313020478201269 10610108628685595669831369)
              ·
                refine ⟨7957581471514196752373527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10610108628685595669831369 7957581471514196752373527)
                ·
                  refine ⟨11936372207271295128560291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7957581471514196752373527 11936372207271295128560291)
                  ·
                    refine ⟨17904558310906942692840437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11936372207271295128560291 17904558310906942692840437)
                    ·
                      refine ⟨1678552341647525877453791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17904558310906942692840437 1678552341647525877453791)
                      ·
                        rfl

theorem cell23_3268969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_3268969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268969 prefixEnd_3268969 := by exact prefixLift 3268969
  have htrace : WordTrace (prefixWord ++ tailWord_3268969) baseStart_3268969 baseEnd_3268969 := by
    simpa [prefixWord, tailWord_3268969, baseEnd_3268969] using wordTrace_append hprefix tailTrace_3268969
  have hstable : (prefixWord ++ tailWord_3268969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268969).length < 2 ^ (prefixWord ++ tailWord_3268969).sum := by decide
  have hdescent : baseEnd_3268969 < baseStart_3268969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268976 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_3268976 : Nat := 118140960795 + 3268976 * 2 ^ 59
def prefixEnd_3268976 : Nat := 4983230072969 + 3 ^ 40 * 3268976 * 2
def baseEnd_3268976 : Nat := 559518645337369116688753

theorem tailTrace_3268976 : CollatzResearch.WordTrace tailWord_3268976 prefixEnd_3268976 559518645337369116688753 := by
  unfold tailWord_3268976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59614674902532861748821391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79486233203377148998428521 59614674902532861748821391)
  ·
    refine ⟨89422012353799292623232087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59614674902532861748821391 89422012353799292623232087)
    ·
      refine ⟨134133018530698938934848131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89422012353799292623232087 134133018530698938934848131)
      ·
        refine ⟨201199527796048408402272197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134133018530698938934848131 201199527796048408402272197)
        ·
          refine ⟨37724911461759076575426037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201199527796048408402272197 37724911461759076575426037)
          ·
            refine ⟨3536710449539913428946191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37724911461759076575426037 3536710449539913428946191)
            ·
              refine ⟨5305065674309870143419287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536710449539913428946191 5305065674309870143419287)
              ·
                refine ⟨7957598511464805215128931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305065674309870143419287 7957598511464805215128931)
                ·
                  refine ⟨11936397767197207822693397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7957598511464805215128931 11936397767197207822693397)
                  ·
                    refine ⟨559518645337369116688753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11936397767197207822693397 559518645337369116688753)
                    ·
                      rfl

theorem cell23_3268976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_3268976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268976 prefixEnd_3268976 := by exact prefixLift 3268976
  have htrace : WordTrace (prefixWord ++ tailWord_3268976) baseStart_3268976 baseEnd_3268976 := by
    simpa [prefixWord, tailWord_3268976, baseEnd_3268976] using wordTrace_append hprefix tailTrace_3268976
  have hstable : (prefixWord ++ tailWord_3268976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268976).length < 2 ^ (prefixWord ++ tailWord_3268976).sum := by decide
  have hdescent : baseEnd_3268976 < baseStart_3268976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268989 : List Nat := [1, 4, 1, 1, 2, 4, 1, 9]
def baseStart_3268989 : Nat := 118140960795 + 3268989 * 2 ^ 59
def prefixEnd_3268989 : Nat := 4983230072969 + 3 ^ 40 * 3268989 * 2
def baseEnd_3268989 : Nat := 62168985602245029600137

theorem tailTrace_3268989 : CollatzResearch.WordTrace tailWord_3268989 prefixEnd_3268989 62168985602245029600137 := by
  unfold tailWord_3268989
  simp only [CollatzResearch.WordTrace]
  refine ⟨119229823954018626717866021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79486549302679084478577347 119229823954018626717866021)
  ·
    refine ⟨22355591991378492509599879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119229823954018626717866021 22355591991378492509599879)
    ·
      refine ⟨33533387987067738764399819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355591991378492509599879 33533387987067738764399819)
      ·
        refine ⟨50300081980601608146599729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33533387987067738764399819 50300081980601608146599729)
        ·
          refine ⟨37725061485451206109949797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50300081980601608146599729 37725061485451206109949797)
          ·
            refine ⟨7073449028522101145615587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37725061485451206109949797 7073449028522101145615587)
            ·
              refine ⟨10610173542783151718423381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073449028522101145615587 10610173542783151718423381)
              ·
                refine ⟨62168985602245029600137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10610173542783151718423381 62168985602245029600137)
                ·
                  rfl

theorem cell23_3268989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 9].length) (baseStart_3268989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3268989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3268989 prefixEnd_3268989 := by exact prefixLift 3268989
  have htrace : WordTrace (prefixWord ++ tailWord_3268989) baseStart_3268989 baseEnd_3268989 := by
    simpa [prefixWord, tailWord_3268989, baseEnd_3268989] using wordTrace_append hprefix tailTrace_3268989
  have hstable : (prefixWord ++ tailWord_3268989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268989).length < 2 ^ (prefixWord ++ tailWord_3268989).sum := by decide
  have hdescent : baseEnd_3268989 < baseStart_3268989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269006 : List Nat := [4, 1, 1, 4, 1, 3, 9]
def baseStart_3269006 : Nat := 118140960795 + 3269006 * 2 ^ 59
def prefixEnd_3269006 : Nat := 4983230072969 + 3 ^ 40 * 3269006 * 2
def baseEnd_3269006 : Nat := 20723102968293113983841

theorem tailTrace_3269006 : CollatzResearch.WordTrace tailWord_3269006 prefixEnd_3269006 20723102968293113983841 := by
  unfold tailWord_3269006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14903805499369629827654359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79486962663304692414156581 14903805499369629827654359)
  ·
    refine ⟨22355708249054444741481539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14903805499369629827654359 22355708249054444741481539)
    ·
      refine ⟨33533562373581667112222309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22355708249054444741481539 33533562373581667112222309)
      ·
        refine ⟨6287542945046562583541683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33533562373581667112222309 6287542945046562583541683)
        ·
          refine ⟨9431314417569843875312525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287542945046562583541683 9431314417569843875312525)
          ·
            refine ⟨3536742906588691453242197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9431314417569843875312525 3536742906588691453242197)
            ·
              refine ⟨20723102968293113983841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3536742906588691453242197 20723102968293113983841)
              ·
                rfl

theorem cell23_3269006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 9].length) (baseStart_3269006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269006 prefixEnd_3269006 := by exact prefixLift 3269006
  have htrace : WordTrace (prefixWord ++ tailWord_3269006) baseStart_3269006 baseEnd_3269006 := by
    simpa [prefixWord, tailWord_3269006, baseEnd_3269006] using wordTrace_append hprefix tailTrace_3269006
  have hstable : (prefixWord ++ tailWord_3269006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269006).length < 2 ^ (prefixWord ++ tailWord_3269006).sum := by decide
  have hdescent : baseEnd_3269006 < baseStart_3269006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269017 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 1, 2, 2]
def baseStart_3269017 : Nat := 118140960795 + 3269017 * 2 ^ 59
def prefixEnd_3269017 : Nat := 4983230072969 + 3 ^ 40 * 3269017 * 2
def baseEnd_3269017 : Nat := 1678576988718941689653571

theorem tailTrace_3269017 : CollatzResearch.WordTrace tailWord_3269017 prefixEnd_3269017 1678576988718941689653571 := by
  unfold tailWord_3269017
  simp only [CollatzResearch.WordTrace]
  refine ⟨119230845197917187499885305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79487230131944791666590203 119230845197917187499885305)
  ·
    refine ⟨89423133898437890624913979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119230845197917187499885305 89423133898437890624913979)
    ·
      refine ⟨134134700847656835937370969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89423133898437890624913979 134134700847656835937370969)
      ·
        refine ⟨100601025635742626953028227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134134700847656835937370969 100601025635742626953028227)
        ·
          refine ⟨150901538453613940429542341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100601025635742626953028227 150901538453613940429542341)
          ·
            refine ⟨28294038460052613830539189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150901538453613940429542341 28294038460052613830539189)
            ·
              refine ⟨2652566105629932546613049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28294038460052613830539189 2652566105629932546613049)
              ·
                refine ⟨1989424579222449409959787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652566105629932546613049 1989424579222449409959787)
                ·
                  refine ⟨2984136868833674114939681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989424579222449409959787 2984136868833674114939681)
                  ·
                    refine ⟨2238102651625255586204761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984136868833674114939681 2238102651625255586204761)
                    ·
                      refine ⟨1678576988718941689653571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238102651625255586204761 1678576988718941689653571)
                      ·
                        rfl

theorem cell23_3269017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_3269017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269017 prefixEnd_3269017 := by exact prefixLift 3269017
  have htrace : WordTrace (prefixWord ++ tailWord_3269017) baseStart_3269017 baseEnd_3269017 := by
    simpa [prefixWord, tailWord_3269017, baseEnd_3269017] using wordTrace_append hprefix tailTrace_3269017
  have hstable : (prefixWord ++ tailWord_3269017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269017).length < 2 ^ (prefixWord ++ tailWord_3269017).sum := by decide
  have hdescent : baseEnd_3269017 < baseStart_3269017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269034 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3269034 : Nat := 118140960795 + 3269034 * 2 ^ 59
def prefixEnd_3269034 : Nat := 4983230072969 + 3 ^ 40 * 3269034 * 2
def baseEnd_3269034 : Nat := 1678585717890068123140993

theorem tailTrace_3269034 : CollatzResearch.WordTrace tailWord_3269034 prefixEnd_3269034 1678585717890068123140993 := by
  unfold tailWord_3269034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807866309713899850813539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79487643492570399602169437 29807866309713899850813539)
  ·
    refine ⟨44711799464570849776220309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29807866309713899850813539 44711799464570849776220309)
    ·
      refine ⟨2095865599901758583260327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44711799464570849776220309 2095865599901758583260327)
      ·
        refine ⟨3143798399852637874890491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095865599901758583260327 3143798399852637874890491)
        ·
          refine ⟨4715697599778956812335737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143798399852637874890491 4715697599778956812335737)
          ·
            refine ⟨3536773199834217609251803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715697599778956812335737 3536773199834217609251803)
            ·
              refine ⟨5305159799751326413877705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536773199834217609251803 5305159799751326413877705)
              ·
                refine ⟨3978869849813494810408279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305159799751326413877705 3978869849813494810408279)
                ·
                  refine ⟨5968304774720242215612419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978869849813494810408279 5968304774720242215612419)
                  ·
                    refine ⟨8952457162080363323418629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968304774720242215612419 8952457162080363323418629)
                    ·
                      refine ⟨1678585717890068123140993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8952457162080363323418629 1678585717890068123140993)
                      ·
                        rfl

theorem cell23_3269034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3269034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269034 prefixEnd_3269034 := by exact prefixLift 3269034
  have htrace : WordTrace (prefixWord ++ tailWord_3269034) baseStart_3269034 baseEnd_3269034 := by
    simpa [prefixWord, tailWord_3269034, baseEnd_3269034] using wordTrace_append hprefix tailTrace_3269034
  have hstable : (prefixWord ++ tailWord_3269034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269034).length < 2 ^ (prefixWord ++ tailWord_3269034).sum := by decide
  have hdescent : baseEnd_3269034 < baseStart_3269034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269037 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3269037 : Nat := 118140960795 + 3269037 * 2 ^ 59
def prefixEnd_3269037 : Nat := 4983230072969 + 3 ^ 40 * 3269037 * 2
def baseEnd_3269037 : Nat := 1678587258332031611403479

theorem tailTrace_3269037 : CollatzResearch.WordTrace tailWord_3269037 prefixEnd_3269037 1678587258332031611403479 := by
  unfold tailWord_3269037
  simp only [CollatzResearch.WordTrace]
  refine ⟨119231574657844730915613365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79487716438563153943742243 119231574657844730915613365)
  ·
    refine ⟨11177960124172943523338753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119231574657844730915613365 11177960124172943523338753)
    ·
      refine ⟨8383470093129707642504065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11177960124172943523338753 8383470093129707642504065)
      ·
        refine ⟨6287602569847280731878049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8383470093129707642504065 6287602569847280731878049)
        ·
          refine ⟨4715701927385460548908537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6287602569847280731878049 4715701927385460548908537)
          ·
            refine ⟨3536776445539095411681403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715701927385460548908537 3536776445539095411681403)
            ·
              refine ⟨5305164668308643117522105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536776445539095411681403 5305164668308643117522105)
              ·
                refine ⟨3978873501231482338141579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305164668308643117522105 3978873501231482338141579)
                ·
                  refine ⟨5968310251847223507212369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978873501231482338141579 5968310251847223507212369)
                  ·
                    refine ⟨4476232688885417630409277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968310251847223507212369 4476232688885417630409277)
                    ·
                      refine ⟨1678587258332031611403479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476232688885417630409277 1678587258332031611403479)
                      ·
                        rfl

theorem cell23_3269037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3269037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269037 prefixEnd_3269037 := by exact prefixLift 3269037
  have htrace : WordTrace (prefixWord ++ tailWord_3269037) baseStart_3269037 baseEnd_3269037 := by
    simpa [prefixWord, tailWord_3269037, baseEnd_3269037] using wordTrace_append hprefix tailTrace_3269037
  have hstable : (prefixWord ++ tailWord_3269037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269037).length < 2 ^ (prefixWord ++ tailWord_3269037).sum := by decide
  have hdescent : baseEnd_3269037 < baseStart_3269037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269073 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_3269073 : Nat := 118140960795 + 3269073 * 2 ^ 59
def prefixEnd_3269073 : Nat := 4983230072969 + 3 ^ 40 * 3269073 * 2
def baseEnd_3269073 : Nat := 1678605743635593470553313

theorem tailTrace_3269073 : CollatzResearch.WordTrace tailWord_3269073 prefixEnd_3269073 1678605743635593470553313 := by
  unfold tailWord_3269073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119232887685714309063923873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79488591790476206042615915 119232887685714309063923873)
  ·
    refine ⟨89424665764285731797942905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119232887685714309063923873 89424665764285731797942905)
    ·
      refine ⟨67068499323214298848457179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89424665764285731797942905 67068499323214298848457179)
      ·
        refine ⟨100602748984821448272685769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67068499323214298848457179 100602748984821448272685769)
        ·
          refine ⟨75452061738616086204514327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100602748984821448272685769 75452061738616086204514327)
          ·
            refine ⟨113178092607924129306771491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75452061738616086204514327 113178092607924129306771491)
            ·
              refine ⟨169767138911886193960157237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113178092607924129306771491 169767138911886193960157237)
              ·
                refine ⟨15915669272989330683764741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169767138911886193960157237 15915669272989330683764741)
                ·
                  refine ⟨2984187988685499503205889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15915669272989330683764741 2984187988685499503205889)
                  ·
                    refine ⟨2238140991514124627404417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984187988685499503205889 2238140991514124627404417)
                    ·
                      refine ⟨1678605743635593470553313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238140991514124627404417 1678605743635593470553313)
                      ·
                        rfl

theorem cell23_3269073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_3269073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269073 prefixEnd_3269073 := by exact prefixLift 3269073
  have htrace : WordTrace (prefixWord ++ tailWord_3269073) baseStart_3269073 baseEnd_3269073 := by
    simpa [prefixWord, tailWord_3269073, baseEnd_3269073] using wordTrace_append hprefix tailTrace_3269073
  have hstable : (prefixWord ++ tailWord_3269073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269073).length < 2 ^ (prefixWord ++ tailWord_3269073).sum := by decide
  have hdescent : baseEnd_3269073 < baseStart_3269073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269096 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 7]
def baseStart_3269096 : Nat := 118140960795 + 3269096 * 2 ^ 59
def prefixEnd_3269096 : Nat := 4983230072969 + 3 ^ 40 * 3269096 * 2
def baseEnd_3269096 : Nat := 186513061521182986729523

theorem tailTrace_3269096 : CollatzResearch.WordTrace tailWord_3269096 prefixEnd_3269096 186513061521182986729523 := by
  unfold tailWord_3269096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59616863282315491996005571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79489151043087322661340761 59616863282315491996005571)
  ·
    refine ⟨89425294923473237994008357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59616863282315491996005571 89425294923473237994008357)
    ·
      refine ⟨16767242798151232123876567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89425294923473237994008357 16767242798151232123876567)
      ·
        refine ⟨25150864197226848185814851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16767242798151232123876567 25150864197226848185814851)
        ·
          refine ⟨37726296295840272278722277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25150864197226848185814851 37726296295840272278722277)
          ·
            refine ⟨7073680555470051052260427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37726296295840272278722277 7073680555470051052260427)
            ·
              refine ⟨10610520833205076578390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073680555470051052260427 10610520833205076578390641)
              ·
                refine ⟨7957890624903807433792981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10610520833205076578390641 7957890624903807433792981)
                ·
                  refine ⟨186513061521182986729523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7957890624903807433792981 186513061521182986729523)
                  ·
                    rfl

theorem cell23_3269096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_3269096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269096 prefixEnd_3269096 := by exact prefixLift 3269096
  have htrace : WordTrace (prefixWord ++ tailWord_3269096) baseStart_3269096 baseEnd_3269096 := by
    simpa [prefixWord, tailWord_3269096, baseEnd_3269096] using wordTrace_append hprefix tailTrace_3269096
  have hstable : (prefixWord ++ tailWord_3269096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269096).length < 2 ^ (prefixWord ++ tailWord_3269096).sum := by decide
  have hdescent : baseEnd_3269096 < baseStart_3269096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269124 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3269124 : Nat := 118140960795 + 3269124 * 2 ^ 59
def prefixEnd_3269124 : Nat := 4983230072969 + 3 ^ 40 * 3269124 * 2
def baseEnd_3269124 : Nat := 1678631931148972771015579

theorem tailTrace_3269124 : CollatzResearch.WordTrace tailWord_3269124 prefixEnd_3269124 1678631931148972771015579 := by
  unfold tailWord_3269124
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617373904264772387015213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79489831872353029849353617 59617373904264772387015213)
  ·
    refine ⟨22356515214099289645130705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59617373904264772387015213 22356515214099289645130705)
    ·
      refine ⟨16767386410574467233848029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22356515214099289645130705 16767386410574467233848029)
      ·
        refine ⟨6287769903965425212693011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16767386410574467233848029 6287769903965425212693011)
        ·
          refine ⟨9431654855948137819039517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287769903965425212693011 9431654855948137819039517)
          ·
            refine ⟨3536870570980551682139819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9431654855948137819039517 3536870570980551682139819)
            ·
              refine ⟨5305305856470827523209729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3536870570980551682139819 5305305856470827523209729)
              ·
                refine ⟨3978979392353120642407297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305305856470827523209729 3978979392353120642407297)
                ·
                  refine ⟨2984234544264840481805473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978979392353120642407297 2984234544264840481805473)
                  ·
                    refine ⟨2238175908198630361354105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2984234544264840481805473 2238175908198630361354105)
                    ·
                      refine ⟨1678631931148972771015579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238175908198630361354105 1678631931148972771015579)
                      ·
                        rfl

theorem cell23_3269124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3269124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269124 prefixEnd_3269124 := by exact prefixLift 3269124
  have htrace : WordTrace (prefixWord ++ tailWord_3269124) baseStart_3269124 baseEnd_3269124 := by
    simpa [prefixWord, tailWord_3269124, baseEnd_3269124] using wordTrace_append hprefix tailTrace_3269124
  have hstable : (prefixWord ++ tailWord_3269124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269124).length < 2 ^ (prefixWord ++ tailWord_3269124).sum := by decide
  have hdescent : baseEnd_3269124 < baseStart_3269124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269140 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3269140 : Nat := 118140960795 + 3269140 * 2 ^ 59
def prefixEnd_3269140 : Nat := 4983230072969 + 3 ^ 40 * 3269140 * 2
def baseEnd_3269140 : Nat := 1678640146839444708415505

theorem tailTrace_3269140 : CollatzResearch.WordTrace tailWord_3269140 prefixEnd_3269140 1678640146839444708415505 := by
  unfold tailWord_3269140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617665688235789753306437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79490220917647719671075249 59617665688235789753306437)
  ·
    refine ⟨11178312316544210578744957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59617665688235789753306437 11178312316544210578744957)
    ·
      refine ⟨4191867118704078967029359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11178312316544210578744957 4191867118704078967029359)
      ·
        refine ⟨6287800678056118450544039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191867118704078967029359 6287800678056118450544039)
        ·
          refine ⟨9431701017084177675816059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287800678056118450544039 9431701017084177675816059)
          ·
            refine ⟨14147551525626266513724089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431701017084177675816059 14147551525626266513724089)
            ·
              refine ⟨10610663644219699885293067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14147551525626266513724089 10610663644219699885293067)
              ·
                refine ⟨15915995466329549827939601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610663644219699885293067 15915995466329549827939601)
                ·
                  refine ⟨11936996599747162370954701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15915995466329549827939601 11936996599747162370954701)
                  ·
                    refine ⟨4476373724905185889108013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11936996599747162370954701 4476373724905185889108013)
                    ·
                      refine ⟨1678640146839444708415505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476373724905185889108013 1678640146839444708415505)
                      ·
                        rfl

theorem cell23_3269140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3269140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269140 prefixEnd_3269140 := by exact prefixLift 3269140
  have htrace : WordTrace (prefixWord ++ tailWord_3269140) baseStart_3269140 baseEnd_3269140 := by
    simpa [prefixWord, tailWord_3269140, baseEnd_3269140] using wordTrace_append hprefix tailTrace_3269140
  have hstable : (prefixWord ++ tailWord_3269140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269140).length < 2 ^ (prefixWord ++ tailWord_3269140).sum := by decide
  have hdescent : baseEnd_3269140 < baseStart_3269140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269146 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3269146 : Nat := 118140960795 + 3269146 * 2 ^ 59
def prefixEnd_3269146 : Nat := 4983230072969 + 3 ^ 40 * 3269146 * 2
def baseEnd_3269146 : Nat := 1678643227723371684940477

theorem tailTrace_3269146 : CollatzResearch.WordTrace tailWord_3269146 prefixEnd_3269146 1678643227723371684940477 := by
  unfold tailWord_3269146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29808887553612460632832823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79490366809633228354220861 29808887553612460632832823)
  ·
    refine ⟨44713331330418690949249235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29808887553612460632832823 44713331330418690949249235)
    ·
      refine ⟨67069996995628036423873853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713331330418690949249235 67069996995628036423873853)
      ·
        refine ⟨25151248873360513658952695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67069996995628036423873853 25151248873360513658952695)
        ·
          refine ⟨37726873310040770488429043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25151248873360513658952695 37726873310040770488429043)
          ·
            refine ⟨56590309965061155732643565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37726873310040770488429043 56590309965061155732643565)
            ·
              refine ⟨21221366236897933399741337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56590309965061155732643565 21221366236897933399741337)
              ·
                refine ⟨15916024677673450049806003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21221366236897933399741337 15916024677673450049806003)
                ·
                  refine ⟨23874037016510175074709005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15916024677673450049806003 23874037016510175074709005)
                  ·
                    refine ⟨8952763881191315653015877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23874037016510175074709005 8952763881191315653015877)
                    ·
                      refine ⟨1678643227723371684940477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8952763881191315653015877 1678643227723371684940477)
                      ·
                        rfl

theorem cell23_3269146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3269146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269146 prefixEnd_3269146 := by exact prefixLift 3269146
  have htrace : WordTrace (prefixWord ++ tailWord_3269146) baseStart_3269146 baseEnd_3269146 := by
    simpa [prefixWord, tailWord_3269146, baseEnd_3269146] using wordTrace_append hprefix tailTrace_3269146
  have hstable : (prefixWord ++ tailWord_3269146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269146).length < 2 ^ (prefixWord ++ tailWord_3269146).sum := by decide
  have hdescent : baseEnd_3269146 < baseStart_3269146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269183 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_3269183 : Nat := 118140960795 + 3269183 * 2 ^ 59
def prefixEnd_3269183 : Nat := 4983230072969 + 3 ^ 40 * 3269183 * 2
def baseEnd_3269183 : Nat := 1678662226507588040177807

theorem tailTrace_3269183 : CollatzResearch.WordTrace tailWord_3269183 prefixEnd_3269183 1678662226507588040177807 := by
  unfold tailWord_3269183
  simp only [CollatzResearch.WordTrace]
  refine ⟨119236899715315797850428203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79491266476877198566952135 119236899715315797850428203)
  ·
    refine ⟨178855349572973696775642305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119236899715315797850428203 178855349572973696775642305)
    ·
      refine ⟨134141512179730272581731729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178855349572973696775642305 134141512179730272581731729)
      ·
        refine ⟨100606134134797704436298797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134141512179730272581731729 100606134134797704436298797)
        ·
          refine ⟨37727300300549139163612049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100606134134797704436298797 37727300300549139163612049)
          ·
            refine ⟨28295475225411854372709037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37727300300549139163612049 28295475225411854372709037)
            ·
              refine ⟨10610803209529445389765889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28295475225411854372709037 10610803209529445389765889)
              ·
                refine ⟨7958102407147084042324417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10610803209529445389765889 7958102407147084042324417)
                ·
                  refine ⟨5968576805360313031743313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958102407147084042324417 5968576805360313031743313)
                  ·
                    refine ⟨4476432604020234773807485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968576805360313031743313 4476432604020234773807485)
                    ·
                      refine ⟨1678662226507588040177807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476432604020234773807485 1678662226507588040177807)
                      ·
                        rfl

theorem cell23_3269183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_3269183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269183 prefixEnd_3269183 := by exact prefixLift 3269183
  have htrace : WordTrace (prefixWord ++ tailWord_3269183) baseStart_3269183 baseEnd_3269183 := by
    simpa [prefixWord, tailWord_3269183, baseEnd_3269183] using wordTrace_append hprefix tailTrace_3269183
  have hstable : (prefixWord ++ tailWord_3269183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269183).length < 2 ^ (prefixWord ++ tailWord_3269183).sum := by decide
  have hdescent : baseEnd_3269183 < baseStart_3269183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269253 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_3269253 : Nat := 118140960795 + 3269253 * 2 ^ 59
def prefixEnd_3269253 : Nat := 4983230072969 + 3 ^ 40 * 3269253 * 2
def baseEnd_3269253 : Nat := 1678698170153402766302485

theorem tailTrace_3269253 : CollatzResearch.WordTrace tailWord_3269253 prefixEnd_3269253 1678698170153402766302485 := by
  unfold tailWord_3269253
  simp only [CollatzResearch.WordTrace]
  refine ⟨119239452825062199805476413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79492968550041466536984275 119239452825062199805476413)
  ·
    refine ⟨44714794809398324927053655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119239452825062199805476413 44714794809398324927053655)
    ·
      refine ⟨67072192214097487390580483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44714794809398324927053655 67072192214097487390580483)
      ·
        refine ⟨100608288321146231085870725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67072192214097487390580483 100608288321146231085870725)
        ·
          refine ⟨18864054060214918328600761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100608288321146231085870725 18864054060214918328600761)
          ·
            refine ⟨14148040545161188746450571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18864054060214918328600761 14148040545161188746450571)
            ·
              refine ⟨21222060817741783119675857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14148040545161188746450571 21222060817741783119675857)
              ·
                refine ⟨15916545613306337339756893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21222060817741783119675857 15916545613306337339756893)
                ·
                  refine ⟨5968704604989876502408835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15916545613306337339756893 5968704604989876502408835)
                  ·
                    refine ⟨8953056907484814753613253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5968704604989876502408835 8953056907484814753613253)
                    ·
                      refine ⟨1678698170153402766302485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8953056907484814753613253 1678698170153402766302485)
                      ·
                        rfl

theorem cell23_3269253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_3269253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269253 prefixEnd_3269253 := by exact prefixLift 3269253
  have htrace : WordTrace (prefixWord ++ tailWord_3269253) baseStart_3269253 baseEnd_3269253 := by
    simpa [prefixWord, tailWord_3269253, baseEnd_3269253] using wordTrace_append hprefix tailTrace_3269253
  have hstable : (prefixWord ++ tailWord_3269253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269253).length < 2 ^ (prefixWord ++ tailWord_3269253).sum := by decide
  have hdescent : baseEnd_3269253 < baseStart_3269253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269273 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_3269273 : Nat := 118140960795 + 3269273 * 2 ^ 59
def prefixEnd_3269273 : Nat := 4983230072969 + 3 ^ 40 * 3269273 * 2
def baseEnd_3269273 : Nat := 1678708439766492688052393

theorem tailTrace_3269273 : CollatzResearch.WordTrace tailWord_3269273 prefixEnd_3269273 1678708439766492688052393 := by
  unfold tailWord_3269273
  simp only [CollatzResearch.WordTrace]
  refine ⟨119240182284989743221204473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79493454856659828814136315 119240182284989743221204473)
  ·
    refine ⟨89430136713742307415903355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119240182284989743221204473 89430136713742307415903355)
    ·
      refine ⟨134145205070613461123855033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89430136713742307415903355 134145205070613461123855033)
      ·
        refine ⟨100608903802960095842891275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134145205070613461123855033 100608903802960095842891275)
        ·
          refine ⟨150913355704440143764336913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100608903802960095842891275 150913355704440143764336913)
          ·
            refine ⟨113185016778330107823252685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150913355704440143764336913 113185016778330107823252685)
            ·
              refine ⟨42444381291873790433719757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113185016778330107823252685 42444381291873790433719757)
              ·
                refine ⟨15916642984452671412644909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42444381291873790433719757 15916642984452671412644909)
                ·
                  refine ⟨5968741119169751779741841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15916642984452671412644909 5968741119169751779741841)
                  ·
                    refine ⟨4476555839377313834806381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5968741119169751779741841 4476555839377313834806381)
                    ·
                      refine ⟨1678708439766492688052393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476555839377313834806381 1678708439766492688052393)
                      ·
                        rfl

theorem cell23_3269273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_3269273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269273 prefixEnd_3269273 := by exact prefixLift 3269273
  have htrace : WordTrace (prefixWord ++ tailWord_3269273) baseStart_3269273 baseEnd_3269273 := by
    simpa [prefixWord, tailWord_3269273, baseEnd_3269273] using wordTrace_append hprefix tailTrace_3269273
  have hstable : (prefixWord ++ tailWord_3269273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269273).length < 2 ^ (prefixWord ++ tailWord_3269273).sum := by decide
  have hdescent : baseEnd_3269273 < baseStart_3269273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269293 : List Nat := [1, 5, 2, 1, 1, 3, 10]
def baseStart_3269293 : Nat := 118140960795 + 3269293 * 2 ^ 59
def prefixEnd_3269293 : Nat := 4983230072969 + 3 ^ 40 * 3269293 * 2
def baseEnd_3269293 : Nat := 20724922338019538392621

theorem tailTrace_3269293 : CollatzResearch.WordTrace tailWord_3269293 prefixEnd_3269293 20724922338019538392621 := by
  unfold tailWord_3269293
  simp only [CollatzResearch.WordTrace]
  refine ⟨119240911744917286636932533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79493941163278191091288355 119240911744917286636932533)
  ·
    refine ⟨11178835476085995622212425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119240911744917286636932533 11178835476085995622212425)
    ·
      refine ⟨8384126607064496716659319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11178835476085995622212425 8384126607064496716659319)
      ·
        refine ⟨12576189910596745074988979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8384126607064496716659319 12576189910596745074988979)
        ·
          refine ⟨18864284865895117612483469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12576189910596745074988979 18864284865895117612483469)
          ·
            refine ⟨7074106824710669104681301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18864284865895117612483469 7074106824710669104681301)
            ·
              refine ⟨20724922338019538392621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7074106824710669104681301 20724922338019538392621)
              ·
                rfl

theorem cell23_3269293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 10].length) (baseStart_3269293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269293 prefixEnd_3269293 := by exact prefixLift 3269293
  have htrace : WordTrace (prefixWord ++ tailWord_3269293) baseStart_3269293 baseEnd_3269293 := by
    simpa [prefixWord, tailWord_3269293, baseEnd_3269293] using wordTrace_append hprefix tailTrace_3269293
  have hstable : (prefixWord ++ tailWord_3269293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269293).length < 2 ^ (prefixWord ++ tailWord_3269293).sum := by decide
  have hdescent : baseEnd_3269293 < baseStart_3269293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269296 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_3269296 : Nat := 118140960795 + 3269296 * 2 ^ 59
def prefixEnd_3269296 : Nat := 4983230072969 + 3 ^ 40 * 3269296 * 2
def baseEnd_3269296 : Nat := 1678720249821546098064787

theorem tailTrace_3269296 : CollatzResearch.WordTrace tailWord_3269296 prefixEnd_3269296 1678720249821546098064787 := by
  unfold tailWord_3269296
  simp only [CollatzResearch.WordTrace]
  refine ⟨59620510581953209074645871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79494014109270945432861161 59620510581953209074645871)
  ·
    refine ⟨89430765872929813611968807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59620510581953209074645871 89430765872929813611968807)
    ·
      refine ⟨134146148809394720417953211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89430765872929813611968807 134146148809394720417953211)
      ·
        refine ⟨201219223214092080626929817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134146148809394720417953211 201219223214092080626929817)
        ·
          refine ⟨150914417410569060470197363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201219223214092080626929817 150914417410569060470197363)
          ·
            refine ⟨226371626115853590705296045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150914417410569060470197363 226371626115853590705296045)
            ·
              refine ⟨84889359793445096514486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226371626115853590705296045 84889359793445096514486017)
              ·
                refine ⟨63667019845083822385864513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84889359793445096514486017 63667019845083822385864513)
                ·
                  refine ⟨47750264883812866789398385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63667019845083822385864513 47750264883812866789398385)
                  ·
                    refine ⟨35812698662859650092048789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47750264883812866789398385 35812698662859650092048789)
                    ·
                      refine ⟨1678720249821546098064787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35812698662859650092048789 1678720249821546098064787)
                      ·
                        rfl

theorem cell23_3269296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_3269296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269296 prefixEnd_3269296 := by exact prefixLift 3269296
  have htrace : WordTrace (prefixWord ++ tailWord_3269296) baseStart_3269296 baseEnd_3269296 := by
    simpa [prefixWord, tailWord_3269296, baseEnd_3269296] using wordTrace_append hprefix tailTrace_3269296
  have hstable : (prefixWord ++ tailWord_3269296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269296).length < 2 ^ (prefixWord ++ tailWord_3269296).sum := by decide
  have hdescent : baseEnd_3269296 < baseStart_3269296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269297 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_3269297 : Nat := 118140960795 + 3269297 * 2 ^ 59
def prefixEnd_3269297 : Nat := 4983230072969 + 3 ^ 40 * 3269297 * 2
def baseEnd_3269297 : Nat := 559573587767400198050761

theorem tailTrace_3269297 : CollatzResearch.WordTrace tailWord_3269297 prefixEnd_3269297 559573587767400198050761 := by
  unfold tailWord_3269297
  simp only [CollatzResearch.WordTrace]
  refine ⟨119241057636902795320078145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79494038424601863546718763 119241057636902795320078145)
  ·
    refine ⟨89430793227677096490058609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119241057636902795320078145 89430793227677096490058609)
    ·
      refine ⟨67073094920757822367543957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89430793227677096490058609 67073094920757822367543957)
      ·
        refine ⟨3144051324410522923478623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67073094920757822367543957 3144051324410522923478623)
        ·
          refine ⟨4716076986615784385217935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144051324410522923478623 4716076986615784385217935)
          ·
            refine ⟨7074115479923676577826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716076986615784385217935 7074115479923676577826903)
            ·
              refine ⟨10611173219885514866740355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074115479923676577826903 10611173219885514866740355)
              ·
                refine ⟨15916759829828272300110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10611173219885514866740355 15916759829828272300110533)
                ·
                  refine ⟨2984392468092801056270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15916759829828272300110533 2984392468092801056270725)
                  ·
                    refine ⟨559573587767400198050761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984392468092801056270725 559573587767400198050761)
                    ·
                      rfl

theorem cell23_3269297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_3269297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269297 prefixEnd_3269297 := by exact prefixLift 3269297
  have htrace : WordTrace (prefixWord ++ tailWord_3269297) baseStart_3269297 baseEnd_3269297 := by
    simpa [prefixWord, tailWord_3269297, baseEnd_3269297] using wordTrace_append hprefix tailTrace_3269297
  have hstable : (prefixWord ++ tailWord_3269297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269297).length < 2 ^ (prefixWord ++ tailWord_3269297).sum := by decide
  have hdescent : baseEnd_3269297 < baseStart_3269297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269320 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3269320 : Nat := 118140960795 + 3269320 * 2 ^ 59
def prefixEnd_3269320 : Nat := 4983230072969 + 3 ^ 40 * 3269320 * 2
def baseEnd_3269320 : Nat := 1678732573357254004164677

theorem tailTrace_3269320 : CollatzResearch.WordTrace tailWord_3269320 prefixEnd_3269320 1678732573357254004164677 := by
  unfold tailWord_3269320
  simp only [CollatzResearch.WordTrace]
  refine ⟨59620948257909735124082707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79494597677212980165443609 59620948257909735124082707)
  ·
    refine ⟨89431422386864602686124061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59620948257909735124082707 89431422386864602686124061)
    ·
      refine ⟨33536783395074226007296523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89431422386864602686124061 33536783395074226007296523)
      ·
        refine ⟨50305175092611339010944785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33536783395074226007296523 50305175092611339010944785)
        ·
          refine ⟨37728881319458504258208589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50305175092611339010944785 37728881319458504258208589)
          ·
            refine ⟨14148330494796939096828221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37728881319458504258208589 14148330494796939096828221)
            ·
              refine ⟨5305623935548852161310583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14148330494796939096828221 5305623935548852161310583)
              ·
                refine ⟨7958435903323278241965875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305623935548852161310583 7958435903323278241965875)
                ·
                  refine ⟨11937653854984917362948813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7958435903323278241965875 11937653854984917362948813)
                  ·
                    refine ⟨4476620195619344011105805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11937653854984917362948813 4476620195619344011105805)
                    ·
                      refine ⟨1678732573357254004164677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476620195619344011105805 1678732573357254004164677)
                      ·
                        rfl

theorem cell23_3269320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3269320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269320 prefixEnd_3269320 := by exact prefixLift 3269320
  have htrace : WordTrace (prefixWord ++ tailWord_3269320) baseStart_3269320 baseEnd_3269320 := by
    simpa [prefixWord, tailWord_3269320, baseEnd_3269320] using wordTrace_append hprefix tailTrace_3269320
  have hstable : (prefixWord ++ tailWord_3269320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269320).length < 2 ^ (prefixWord ++ tailWord_3269320).sum := by decide
  have hdescent : baseEnd_3269320 < baseStart_3269320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269363 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3]
def baseStart_3269363 : Nat := 118140960795 + 3269363 * 2 ^ 59
def prefixEnd_3269363 : Nat := 4983230072969 + 3 ^ 40 * 3269363 * 2
def baseEnd_3269363 : Nat := 1678754653025397335926979

theorem tailTrace_3269363 : CollatzResearch.WordTrace tailWord_3269363 prefixEnd_3269363 1678754653025397335926979 := by
  unfold tailWord_3269363
  simp only [CollatzResearch.WordTrace]
  refine ⟨119243464854663688591980743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79495643236442459061320495 119243464854663688591980743)
  ·
    refine ⟨178865197281995532887971115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119243464854663688591980743 178865197281995532887971115)
    ·
      refine ⟨268297795922993299331956673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178865197281995532887971115 268297795922993299331956673)
      ·
        refine ⟨201223346942244974498967505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268297795922993299331956673 201223346942244974498967505)
        ·
          refine ⟨150917510206683730874225629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201223346942244974498967505 150917510206683730874225629)
          ·
            refine ⟨56594066327506399077834611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150917510206683730874225629 56594066327506399077834611)
            ·
              refine ⟨84891099491259598616751917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56594066327506399077834611 84891099491259598616751917)
              ·
                refine ⟨31834162309222349481281969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84891099491259598616751917 31834162309222349481281969)
                ·
                  refine ⟨23875621731916762110961477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31834162309222349481281969 23875621731916762110961477)
                  ·
                    refine ⟨4476679074734392895805277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23875621731916762110961477 4476679074734392895805277)
                    ·
                      refine ⟨1678754653025397335926979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4476679074734392895805277 1678754653025397335926979)
                      ·
                        rfl

theorem cell23_3269363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_3269363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269363 prefixEnd_3269363 := by exact prefixLift 3269363
  have htrace : WordTrace (prefixWord ++ tailWord_3269363) baseStart_3269363 baseEnd_3269363 := by
    simpa [prefixWord, tailWord_3269363, baseEnd_3269363] using wordTrace_append hprefix tailTrace_3269363
  have hstable : (prefixWord ++ tailWord_3269363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269363).length < 2 ^ (prefixWord ++ tailWord_3269363).sum := by decide
  have hdescent : baseEnd_3269363 < baseStart_3269363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269365 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3269365 : Nat := 118140960795 + 3269365 * 2 ^ 59
def prefixEnd_3269365 : Nat := 4983230072969 + 3 ^ 40 * 3269365 * 2
def baseEnd_3269365 : Nat := 559585226662235442700657

theorem tailTrace_3269365 : CollatzResearch.WordTrace tailWord_3269365 prefixEnd_3269365 559585226662235442700657 := by
  unfold tailWord_3269365
  simp only [CollatzResearch.WordTrace]
  refine ⟨119243537800656442933553549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79495691867104295289035699 119243537800656442933553549)
  ·
    refine ⟨44716326675246166100082581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119243537800656442933553549 44716326675246166100082581)
    ·
      refine ⟨2096077812902164035941371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44716326675246166100082581 2096077812902164035941371)
      ·
        refine ⟨3144116719353246053912057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096077812902164035941371 3144116719353246053912057)
        ·
          refine ⟨2358087539514934540434043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144116719353246053912057 2358087539514934540434043)
          ·
            refine ⟨3537131309272401810651065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358087539514934540434043 3537131309272401810651065)
            ·
              refine ⟨2652848481954301357988299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537131309272401810651065 2652848481954301357988299)
              ·
                refine ⟨3979272722931452036982449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652848481954301357988299 3979272722931452036982449)
                ·
                  refine ⟨2984454542198589027736837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3979272722931452036982449 2984454542198589027736837)
                  ·
                    refine ⟨559585226662235442700657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984454542198589027736837 559585226662235442700657)
                    ·
                      rfl

theorem cell23_3269365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3269365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269365 prefixEnd_3269365 := by exact prefixLift 3269365
  have htrace : WordTrace (prefixWord ++ tailWord_3269365) baseStart_3269365 baseEnd_3269365 := by
    simpa [prefixWord, tailWord_3269365, baseEnd_3269365] using wordTrace_append hprefix tailTrace_3269365
  have hstable : (prefixWord ++ tailWord_3269365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269365).length < 2 ^ (prefixWord ++ tailWord_3269365).sum := by decide
  have hdescent : baseEnd_3269365 < baseStart_3269365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269373 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3269373 : Nat := 118140960795 + 3269373 * 2 ^ 59
def prefixEnd_3269373 : Nat := 4983230072969 + 3 ^ 40 * 3269373 * 2
def baseEnd_3269373 : Nat := 1678759787831942296801933

theorem tailTrace_3269373 : CollatzResearch.WordTrace tailWord_3269373 prefixEnd_3269373 1678759787831942296801933 := by
  unfold tailWord_3269373
  simp only [CollatzResearch.WordTrace]
  refine ⟨119243829584627460299844773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79495886389751640199896515 119243829584627460299844773)
  ·
    refine ⟨22358218047117648806220895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119243829584627460299844773 22358218047117648806220895)
    ·
      refine ⟨33537327070676473209331343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22358218047117648806220895 33537327070676473209331343)
      ·
        refine ⟨50305990606014709813997015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33537327070676473209331343 50305990606014709813997015)
        ·
          refine ⟨75458985909022064720995523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50305990606014709813997015 75458985909022064720995523)
          ·
            refine ⟨113188478863533097081493285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75458985909022064720995523 113188478863533097081493285)
            ·
              refine ⟨21222839786912455702779991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113188478863533097081493285 21222839786912455702779991)
              ·
                refine ⟨31834259680368683554169987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21222839786912455702779991 31834259680368683554169987)
                ·
                  refine ⟨47751389520553025331254981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31834259680368683554169987 47751389520553025331254981)
                  ·
                    refine ⟨8953385535103692249610309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47751389520553025331254981 8953385535103692249610309)
                    ·
                      refine ⟨1678759787831942296801933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8953385535103692249610309 1678759787831942296801933)
                      ·
                        rfl

theorem cell23_3269373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3269373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269373 prefixEnd_3269373 := by exact prefixLift 3269373
  have htrace : WordTrace (prefixWord ++ tailWord_3269373) baseStart_3269373 baseEnd_3269373 := by
    simpa [prefixWord, tailWord_3269373, baseEnd_3269373] using wordTrace_append hprefix tailTrace_3269373
  have hstable : (prefixWord ++ tailWord_3269373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269373).length < 2 ^ (prefixWord ++ tailWord_3269373).sum := by decide
  have hdescent : baseEnd_3269373 < baseStart_3269373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269400 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 5]
def baseStart_3269400 : Nat := 118140960795 + 3269400 * 2 ^ 59
def prefixEnd_3269400 : Nat := 4983230072969 + 3 ^ 40 * 3269400 * 2
def baseEnd_3269400 : Nat := 186530405756623743462701

theorem tailTrace_3269400 : CollatzResearch.WordTrace tailWord_3269400 prefixEnd_3269400 186530405756623743462701 := by
  unfold tailWord_3269400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59622407177764821955538827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79496542903686429274051769 59622407177764821955538827)
  ·
    refine ⟨89433610766647232933308241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59622407177764821955538827 89433610766647232933308241)
    ·
      refine ⟨67075208074985424699981181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89433610766647232933308241 67075208074985424699981181)
      ·
        refine ⟨25153203028119534262492943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67075208074985424699981181 25153203028119534262492943)
        ·
          refine ⟨37729804542179301393739415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25153203028119534262492943 37729804542179301393739415)
          ·
            refine ⟨56594706813268952090609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37729804542179301393739415 56594706813268952090609123)
            ·
              refine ⟨84892060219903428135913685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56594706813268952090609123 84892060219903428135913685)
              ·
                refine ⟨1989657661403986596935477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84892060219903428135913685 1989657661403986596935477)
                ·
                  refine ⟨186530405756623743462701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989657661403986596935477 186530405756623743462701)
                  ·
                    rfl

theorem cell23_3269400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 5].length) (baseStart_3269400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269400 prefixEnd_3269400 := by exact prefixLift 3269400
  have htrace : WordTrace (prefixWord ++ tailWord_3269400) baseStart_3269400 baseEnd_3269400 := by
    simpa [prefixWord, tailWord_3269400, baseEnd_3269400] using wordTrace_append hprefix tailTrace_3269400
  have hstable : (prefixWord ++ tailWord_3269400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269400).length < 2 ^ (prefixWord ++ tailWord_3269400).sum := by decide
  have hdescent : baseEnd_3269400 < baseStart_3269400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269420 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_3269420 : Nat := 118140960795 + 3269420 * 2 ^ 59
def prefixEnd_3269420 : Nat := 4983230072969 + 3 ^ 40 * 3269420 * 2
def baseEnd_3269420 : Nat := 1678783921422703612914217

theorem tailTrace_3269420 : CollatzResearch.WordTrace tailWord_3269420 prefixEnd_3269420 1678783921422703612914217 := by
  unfold tailWord_3269420
  simp only [CollatzResearch.WordTrace]
  refine ⟨59622771907728593663402857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79497029210304791551203809 59622771907728593663402857)
  ·
    refine ⟨44717078930796445247552143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59622771907728593663402857 44717078930796445247552143)
    ·
      refine ⟨67075618396194667871328215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44717078930796445247552143 67075618396194667871328215)
      ·
        refine ⟨100613427594292001806992323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67075618396194667871328215 100613427594292001806992323)
        ·
          refine ⟨150920141391438002710488485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100613427594292001806992323 150920141391438002710488485)
          ·
            refine ⟨28297526510894625508216591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150920141391438002710488485 28297526510894625508216591)
            ·
              refine ⟨42446289766341938262324887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28297526510894625508216591 42446289766341938262324887)
              ·
                refine ⟨63669434649512907393487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42446289766341938262324887 63669434649512907393487331)
                ·
                  refine ⟨95504151974269361090230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63669434649512907393487331 95504151974269361090230997)
                  ·
                    refine ⟨2238378561896938150552289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95504151974269361090230997 2238378561896938150552289)
                    ·
                      refine ⟨1678783921422703612914217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238378561896938150552289 1678783921422703612914217)
                      ·
                        rfl

theorem cell23_3269420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_3269420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269420 prefixEnd_3269420 := by exact prefixLift 3269420
  have htrace : WordTrace (prefixWord ++ tailWord_3269420) baseStart_3269420 baseEnd_3269420 := by
    simpa [prefixWord, tailWord_3269420, baseEnd_3269420] using wordTrace_append hprefix tailTrace_3269420
  have hstable : (prefixWord ++ tailWord_3269420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269420).length < 2 ^ (prefixWord ++ tailWord_3269420).sum := by decide
  have hdescent : baseEnd_3269420 < baseStart_3269420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269450 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3269450 : Nat := 118140960795 + 3269450 * 2 ^ 59
def prefixEnd_3269450 : Nat := 4983230072969 + 3 ^ 40 * 3269450 * 2
def baseEnd_3269450 : Nat := 1678799325842338495539079

theorem tailTrace_3269450 : CollatzResearch.WordTrace tailWord_3269450 prefixEnd_3269450 1678799325842338495539079 := by
  unfold tailWord_3269450
  simp only [CollatzResearch.WordTrace]
  refine ⟨29811659501337125612599451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79497758670232334966931869 29811659501337125612599451)
  ·
    refine ⟨44717489252005688418899177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29811659501337125612599451 44717489252005688418899177)
    ·
      refine ⟨33538116939004266314174383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44717489252005688418899177 33538116939004266314174383)
      ·
        refine ⟨50307175408506399471261575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33538116939004266314174383 50307175408506399471261575)
        ·
          refine ⟨75460763112759599206892363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50307175408506399471261575 75460763112759599206892363)
          ·
            refine ⟨113191144669139398810338545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75460763112759599206892363 113191144669139398810338545)
            ·
              refine ⟨84893358501854549107753909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113191144669139398810338545 84893358501854549107753909)
              ·
                refine ⟨7958752359548863978851929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84893358501854549107753909 7958752359548863978851929)
                ·
                  refine ⟨5969064269661647984138947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7958752359548863978851929 5969064269661647984138947)
                  ·
                    refine ⟨8953596404492471976208421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969064269661647984138947 8953596404492471976208421)
                    ·
                      refine ⟨1678799325842338495539079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8953596404492471976208421 1678799325842338495539079)
                      ·
                        rfl

theorem cell23_3269450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3269450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269450 prefixEnd_3269450 := by exact prefixLift 3269450
  have htrace : WordTrace (prefixWord ++ tailWord_3269450) baseStart_3269450 baseEnd_3269450 := by
    simpa [prefixWord, tailWord_3269450, baseEnd_3269450] using wordTrace_append hprefix tailTrace_3269450
  have hstable : (prefixWord ++ tailWord_3269450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269450).length < 2 ^ (prefixWord ++ tailWord_3269450).sum := by decide
  have hdescent : baseEnd_3269450 < baseStart_3269450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269490 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3269490 : Nat := 118140960795 + 3269490 * 2 ^ 59
def prefixEnd_3269490 : Nat := 4983230072969 + 3 ^ 40 * 3269490 * 2
def baseEnd_3269490 : Nat := 186535540563168704337655

theorem tailTrace_3269490 : CollatzResearch.WordTrace tailWord_3269490 prefixEnd_3269490 186535540563168704337655 := by
  unfold tailWord_3269490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29812024231300897320463481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79498731283469059521235949 29812024231300897320463481)
  ·
    refine ⟨22359018173475672990347611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29812024231300897320463481 22359018173475672990347611)
    ·
      refine ⟨33538527260213509485521417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22359018173475672990347611 33538527260213509485521417)
      ·
        refine ⟨25153895445160132114141063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33538527260213509485521417 25153895445160132114141063)
        ·
          refine ⟨37730843167740198171211595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25153895445160132114141063 37730843167740198171211595)
          ·
            refine ⟨56596264751610297256817393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37730843167740198171211595 56596264751610297256817393)
            ·
              refine ⟨42447198563707722942613045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56596264751610297256817393 42447198563707722942613045)
              ·
                refine ⟨3979424865347599025869973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42447198563707722942613045 3979424865347599025869973)
                ·
                  refine ⟨186535540563168704337655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979424865347599025869973 186535540563168704337655)
                  ·
                    rfl

theorem cell23_3269490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3269490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269490 prefixEnd_3269490 := by exact prefixLift 3269490
  have htrace : WordTrace (prefixWord ++ tailWord_3269490) baseStart_3269490 baseEnd_3269490 := by
    simpa [prefixWord, tailWord_3269490, baseEnd_3269490] using wordTrace_append hprefix tailTrace_3269490
  have hstable : (prefixWord ++ tailWord_3269490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269490).length < 2 ^ (prefixWord ++ tailWord_3269490).sum := by decide
  have hdescent : baseEnd_3269490 < baseStart_3269490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269494 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3269494 : Nat := 118140960795 + 3269494 * 2 ^ 59
def prefixEnd_3269494 : Nat := 4983230072969 + 3 ^ 40 * 3269494 * 2
def baseEnd_3269494 : Nat := 559607306330378774462959

theorem tailTrace_3269494 : CollatzResearch.WordTrace tailWord_3269494 prefixEnd_3269494 559607306330378774462959 := by
  unfold tailWord_3269494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453015176074318622812471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79498828544792731976666357 7453015176074318622812471)
  ·
    refine ⟨11179522764111477934218707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7453015176074318622812471 11179522764111477934218707)
    ·
      refine ⟨16769284146167216901328061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11179522764111477934218707 16769284146167216901328061)
      ·
        refine ⟨6288481554812706337998023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16769284146167216901328061 6288481554812706337998023)
        ·
          refine ⟨9432722332219059506997035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288481554812706337998023 9432722332219059506997035)
          ·
            refine ⟨14149083498328589260495553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432722332219059506997035 14149083498328589260495553)
            ·
              refine ⟨10611812623746441945371665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14149083498328589260495553 10611812623746441945371665)
              ·
                refine ⟨7958859467809831459028749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10611812623746441945371665 7958859467809831459028749)
                ·
                  refine ⟨2984572300428686797135781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7958859467809831459028749 2984572300428686797135781)
                  ·
                    refine ⟨559607306330378774462959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984572300428686797135781 559607306330378774462959)
                    ·
                      rfl

theorem cell23_3269494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3269494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269494 prefixEnd_3269494 := by exact prefixLift 3269494
  have htrace : WordTrace (prefixWord ++ tailWord_3269494) baseStart_3269494 baseEnd_3269494 := by
    simpa [prefixWord, tailWord_3269494, baseEnd_3269494] using wordTrace_append hprefix tailTrace_3269494
  have hstable : (prefixWord ++ tailWord_3269494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269494).length < 2 ^ (prefixWord ++ tailWord_3269494).sum := by decide
  have hdescent : baseEnd_3269494 < baseStart_3269494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269511 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3269511 : Nat := 118140960795 + 3269511 * 2 ^ 59
def prefixEnd_3269511 : Nat := 4983230072969 + 3 ^ 40 * 3269511 * 2
def baseEnd_3269511 : Nat := 559610216054087585625433

theorem tailTrace_3269511 : CollatzResearch.WordTrace tailWord_3269511 prefixEnd_3269511 559610216054087585625433 := by
  unfold tailWord_3269511
  simp only [CollatzResearch.WordTrace]
  refine ⟨119248862858127509868368387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79499241905418339912245591 119248862858127509868368387)
  ·
    refine ⟨178873294287191264802552581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119248862858127509868368387 178873294287191264802552581)
    ·
      refine ⟨33538742678848362150478609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178873294287191264802552581 33538742678848362150478609)
      ·
        refine ⟨25154057009136271612858957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33538742678848362150478609 25154057009136271612858957)
        ·
          refine ⟨9432771378426101854822109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25154057009136271612858957 9432771378426101854822109)
          ·
            refine ⟨3537289266909788195558291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9432771378426101854822109 3537289266909788195558291)
            ·
              refine ⟨5305933900364682293337437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537289266909788195558291 5305933900364682293337437)
              ·
                refine ⟨1989725212636755860001539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5305933900364682293337437 1989725212636755860001539)
                ·
                  refine ⟨2984587818955133790002309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989725212636755860001539 2984587818955133790002309)
                  ·
                    refine ⟨559610216054087585625433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2984587818955133790002309 559610216054087585625433)
                    ·
                      rfl

theorem cell23_3269511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3269511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269511 prefixEnd_3269511 := by exact prefixLift 3269511
  have htrace : WordTrace (prefixWord ++ tailWord_3269511) baseStart_3269511 baseEnd_3269511 := by
    simpa [prefixWord, tailWord_3269511, baseEnd_3269511] using wordTrace_append hprefix tailTrace_3269511
  have hstable : (prefixWord ++ tailWord_3269511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269511).length < 2 ^ (prefixWord ++ tailWord_3269511).sum := by decide
  have hdescent : baseEnd_3269511 < baseStart_3269511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269557 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3269557 : Nat := 118140960795 + 3269557 * 2 ^ 59
def prefixEnd_3269557 : Nat := 4983230072969 + 3 ^ 40 * 3269557 * 2
def baseEnd_3269557 : Nat := 1678854268272369576901087

theorem tailTrace_3269557 : CollatzResearch.WordTrace tailWord_3269557 prefixEnd_3269557 1678854268272369576901087 := by
  unfold tailWord_3269557
  simp only [CollatzResearch.WordTrace]
  refine ⟨119250540615960859724542925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79500360410640573149695283 119250540615960859724542925)
  ·
    refine ⟨44718952730985322396703597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119250540615960859724542925 44718952730985322396703597)
    ·
      refine ⟨16769607274119495898763849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44718952730985322396703597 16769607274119495898763849)
      ·
        refine ⟨12577205455589621924072887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16769607274119495898763849 12577205455589621924072887)
        ·
          refine ⟨18865808183384432886109331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12577205455589621924072887 18865808183384432886109331)
          ·
            refine ⟨28298712275076649329163997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18865808183384432886109331 28298712275076649329163997)
            ·
              refine ⟨10612017103153743498436499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28298712275076649329163997 10612017103153743498436499)
              ·
                refine ⟨15918025654730615247654749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612017103153743498436499 15918025654730615247654749)
                ·
                  refine ⟨5969259620523980717870531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15918025654730615247654749 5969259620523980717870531)
                  ·
                    refine ⟨8953889430785971076805797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5969259620523980717870531 8953889430785971076805797)
                    ·
                      refine ⟨1678854268272369576901087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8953889430785971076805797 1678854268272369576901087)
                      ·
                        rfl

theorem cell23_3269557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3269557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269557 prefixEnd_3269557 := by exact prefixLift 3269557
  have htrace : WordTrace (prefixWord ++ tailWord_3269557) baseStart_3269557 baseEnd_3269557 := by
    simpa [prefixWord, tailWord_3269557, baseEnd_3269557] using wordTrace_append hprefix tailTrace_3269557
  have hstable : (prefixWord ++ tailWord_3269557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269557).length < 2 ^ (prefixWord ++ tailWord_3269557).sum := by decide
  have hdescent : baseEnd_3269557 < baseStart_3269557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269597 : List Nat := [1, 4, 3, 1, 2, 1, 3, 8]
def baseStart_3269597 : Nat := 118140960795 + 3269597 * 2 ^ 59
def prefixEnd_3269597 : Nat := 4983230072969 + 3 ^ 40 * 3269597 * 2
def baseEnd_3269597 : Nat := 62180548425872200755589

theorem tailTrace_3269597 : CollatzResearch.WordTrace tailWord_3269597 prefixEnd_3269597 62180548425872200755589 := by
  unfold tailWord_3269597
  simp only [CollatzResearch.WordTrace]
  refine ⟨119251999535815946555999045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79501333023877297703999363 119251999535815946555999045)
  ·
    refine ⟨22359749912965489979249821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119251999535815946555999045 22359749912965489979249821)
    ·
      refine ⟨8384906217362058742218683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22359749912965489979249821 8384906217362058742218683)
      ·
        refine ⟨12577359326043088113328025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8384906217362058742218683 12577359326043088113328025)
        ·
          refine ⟨9433019494532316084996019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12577359326043088113328025 9433019494532316084996019)
          ·
            refine ⟨14149529241798474127494029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433019494532316084996019 14149529241798474127494029)
            ·
              refine ⟨5306073465674427797810261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14149529241798474127494029 5306073465674427797810261)
              ·
                refine ⟨62180548425872200755589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5306073465674427797810261 62180548425872200755589)
                ·
                  rfl

theorem cell23_3269597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 8].length) (baseStart_3269597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269597 prefixEnd_3269597 := by exact prefixLift 3269597
  have htrace : WordTrace (prefixWord ++ tailWord_3269597) baseStart_3269597 baseEnd_3269597 := by
    simpa [prefixWord, tailWord_3269597, baseEnd_3269597] using wordTrace_append hprefix tailTrace_3269597
  have hstable : (prefixWord ++ tailWord_3269597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269597).length < 2 ^ (prefixWord ++ tailWord_3269597).sum := by decide
  have hdescent : baseEnd_3269597 < baseStart_3269597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269614 : List Nat := [4, 1, 2, 1, 4, 1, 3, 7]
def baseStart_3269614 : Nat := 118140960795 + 3269614 * 2 ^ 59
def prefixEnd_3269614 : Nat := 4983230072969 + 3 ^ 40 * 3269614 * 2
def baseEnd_3269614 : Nat := 62180871728506513106975

theorem tailTrace_3269614 : CollatzResearch.WordTrace tailWord_3269614 prefixEnd_3269614 62180871728506513106975 := by
  unfold tailWord_3269614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14906577447094294807420987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79501746384502905639578597 14906577447094294807420987)
  ·
    refine ⟨22359866170641442211131481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14906577447094294807420987 22359866170641442211131481)
    ·
      refine ⟨16769899627981081658348611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22359866170641442211131481 16769899627981081658348611)
      ·
        refine ⟨25154849441971622487522917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16769899627981081658348611 25154849441971622487522917)
        ·
          refine ⟨4716534270369679216410547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25154849441971622487522917 4716534270369679216410547)
          ·
            refine ⟨7074801405554518824615821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716534270369679216410547 7074801405554518824615821)
            ·
              refine ⟨2653050527082944559230933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7074801405554518824615821 2653050527082944559230933)
              ·
                refine ⟨62180871728506513106975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2653050527082944559230933 62180871728506513106975)
                ·
                  rfl

theorem cell23_3269614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_3269614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269614 prefixEnd_3269614 := by exact prefixLift 3269614
  have htrace : WordTrace (prefixWord ++ tailWord_3269614) baseStart_3269614 baseEnd_3269614 := by
    simpa [prefixWord, tailWord_3269614, baseEnd_3269614] using wordTrace_append hprefix tailTrace_3269614
  have hstable : (prefixWord ++ tailWord_3269614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269614).length < 2 ^ (prefixWord ++ tailWord_3269614).sum := by decide
  have hdescent : baseEnd_3269614 < baseStart_3269614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269668 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3269668 : Nat := 118140960795 + 3269668 * 2 ^ 59
def prefixEnd_3269668 : Nat := 4983230072969 + 3 ^ 40 * 3269668 * 2
def baseEnd_3269668 : Nat := 1678911264625018642613077

theorem tailTrace_3269668 : CollatzResearch.WordTrace tailWord_3269668 prefixEnd_3269668 1678911264625018642613077 := by
  unfold tailWord_3269668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59627294559279362840916829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79503059412372483787889105 59627294559279362840916829)
  ·
    refine ⟨22360235459729761065343811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59627294559279362840916829 22360235459729761065343811)
    ·
      refine ⟨33540353189594641598015717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22360235459729761065343811 33540353189594641598015717)
      ·
        refine ⟨6288816223048995299627947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33540353189594641598015717 6288816223048995299627947)
        ·
          refine ⟨9433224334573492949441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288816223048995299627947 9433224334573492949441921)
          ·
            refine ⟨7074918250930119712081441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9433224334573492949441921 7074918250930119712081441)
            ·
              refine ⟨5306188688197589784061081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7074918250930119712081441 5306188688197589784061081)
              ·
                refine ⟨3979641516148192338045811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306188688197589784061081 3979641516148192338045811)
                ·
                  refine ⟨5969462274222288507068717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979641516148192338045811 5969462274222288507068717)
                  ·
                    refine ⟨2238548352833358190150769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5969462274222288507068717 2238548352833358190150769)
                    ·
                      refine ⟨1678911264625018642613077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238548352833358190150769 1678911264625018642613077)
                      ·
                        rfl

theorem cell23_3269668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3269668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269668 prefixEnd_3269668 := by exact prefixLift 3269668
  have htrace : WordTrace (prefixWord ++ tailWord_3269668) baseStart_3269668 baseEnd_3269668 := by
    simpa [prefixWord, tailWord_3269668, baseEnd_3269668] using wordTrace_append hprefix tailTrace_3269668
  have hstable : (prefixWord ++ tailWord_3269668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269668).length < 2 ^ (prefixWord ++ tailWord_3269668).sum := by decide
  have hdescent : baseEnd_3269668 < baseStart_3269668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269684 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3269684 : Nat := 118140960795 + 3269684 * 2 ^ 59
def prefixEnd_3269684 : Nat := 4983230072969 + 3 ^ 40 * 3269684 * 2
def baseEnd_3269684 : Nat := 1678919480315490580013003

theorem tailTrace_3269684 : CollatzResearch.WordTrace tailWord_3269684 prefixEnd_3269684 1678919480315490580013003 := by
  unfold tailWord_3269684
  simp only [CollatzResearch.WordTrace]
  refine ⟨59627586343250380207208053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79503448457667173609610737 59627586343250380207208053)
  ·
    refine ⟨5590086219679723144425755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59627586343250380207208053 5590086219679723144425755)
    ·
      refine ⟨8385129329519584716638633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590086219679723144425755 8385129329519584716638633)
      ·
        refine ⟨6288846997139688537478975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385129329519584716638633 6288846997139688537478975)
        ·
          refine ⟨9433270495709532806218463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288846997139688537478975 9433270495709532806218463)
          ·
            refine ⟨14149905743564299209327695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433270495709532806218463 14149905743564299209327695)
            ·
              refine ⟨21224858615346448813991543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149905743564299209327695 21224858615346448813991543)
              ·
                refine ⟨31837287923019673220987315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21224858615346448813991543 31837287923019673220987315)
                ·
                  refine ⟨47755931884529509831480973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31837287923019673220987315 47755931884529509831480973)
                  ·
                    refine ⟨17908474456698566186805365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47755931884529509831480973 17908474456698566186805365)
                    ·
                      refine ⟨1678919480315490580013003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17908474456698566186805365 1678919480315490580013003)
                      ·
                        rfl

theorem cell23_3269684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3269684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269684 prefixEnd_3269684 := by exact prefixLift 3269684
  have htrace : WordTrace (prefixWord ++ tailWord_3269684) baseStart_3269684 baseEnd_3269684 := by
    simpa [prefixWord, tailWord_3269684, baseEnd_3269684] using wordTrace_append hprefix tailTrace_3269684
  have hstable : (prefixWord ++ tailWord_3269684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269684).length < 2 ^ (prefixWord ++ tailWord_3269684).sum := by decide
  have hdescent : baseEnd_3269684 < baseStart_3269684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269717 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3269717 : Nat := 118140960795 + 3269717 * 2 ^ 59
def prefixEnd_3269717 : Nat := 4983230072969 + 3 ^ 40 * 3269717 * 2
def baseEnd_3269717 : Nat := 559645475059029650300117

theorem tailTrace_3269717 : CollatzResearch.WordTrace tailWord_3269717 prefixEnd_3269717 559645475059029650300117 := by
  unfold tailWord_3269717
  simp only [CollatzResearch.WordTrace]
  refine ⟨119256376295381207050367405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79504250863587471366911603 119256376295381207050367405)
  ·
    refine ⟨44721141110767952643887777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119256376295381207050367405 44721141110767952643887777)
    ·
      refine ⟨33540855833075964482915833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44721141110767952643887777 33540855833075964482915833)
      ·
        refine ⟨25155641874806973362186875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33540855833075964482915833 25155641874806973362186875)
        ·
          refine ⟨37733462812210460043280313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25155641874806973362186875 37733462812210460043280313)
          ·
            refine ⟨28300097109157845032460235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37733462812210460043280313 28300097109157845032460235)
            ·
              refine ⟨42450145663736767548690353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28300097109157845032460235 42450145663736767548690353)
              ·
                refine ⟨31837609247802575661517765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42450145663736767548690353 31837609247802575661517765)
                ·
                  refine ⟨5969551733962982936534581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31837609247802575661517765 5969551733962982936534581)
                  ·
                    refine ⟨559645475059029650300117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5969551733962982936534581 559645475059029650300117)
                    ·
                      rfl

theorem cell23_3269717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3269717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269717 prefixEnd_3269717 := by exact prefixLift 3269717
  have htrace : WordTrace (prefixWord ++ tailWord_3269717) baseStart_3269717 baseEnd_3269717 := by
    simpa [prefixWord, tailWord_3269717, baseEnd_3269717] using wordTrace_append hprefix tailTrace_3269717
  have hstable : (prefixWord ++ tailWord_3269717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269717).length < 2 ^ (prefixWord ++ tailWord_3269717).sum := by decide
  have hdescent : baseEnd_3269717 < baseStart_3269717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269757 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3269757 : Nat := 118140960795 + 3269757 * 2 ^ 59
def prefixEnd_3269757 : Nat := 4983230072969 + 3 ^ 40 * 3269757 * 2
def baseEnd_3269757 : Nat := 1678956964403268794400167

theorem tailTrace_3269757 : CollatzResearch.WordTrace tailWord_3269757 prefixEnd_3269757 1678956964403268794400167 := by
  unfold tailWord_3269757
  simp only [CollatzResearch.WordTrace]
  refine ⟨119257835215236293881823525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79505223476824195921215683 119257835215236293881823525)
  ·
    refine ⟨22360844102856805102841911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119257835215236293881823525 22360844102856805102841911)
    ·
      refine ⟨33541266154285207654262867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22360844102856805102841911 33541266154285207654262867)
      ·
        refine ⟨50311899231427811481394301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33541266154285207654262867 50311899231427811481394301)
        ·
          refine ⟨18866962211785429305522863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50311899231427811481394301 18866962211785429305522863)
          ·
            refine ⟨28300443317678143958284295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18866962211785429305522863 28300443317678143958284295)
            ·
              refine ⟨42450664976517215937426443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28300443317678143958284295 42450664976517215937426443)
              ·
                refine ⟨63675997464775823906139665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42450664976517215937426443 63675997464775823906139665)
                ·
                  refine ⟨47756998098581867929604749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63675997464775823906139665 47756998098581867929604749)
                  ·
                    refine ⟨17908874286968200473601781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47756998098581867929604749 17908874286968200473601781)
                    ·
                      refine ⟨1678956964403268794400167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17908874286968200473601781 1678956964403268794400167)
                      ·
                        rfl

theorem cell23_3269757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3269757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269757 prefixEnd_3269757 := by exact prefixLift 3269757
  have htrace : WordTrace (prefixWord ++ tailWord_3269757) baseStart_3269757 baseEnd_3269757 := by
    simpa [prefixWord, tailWord_3269757, baseEnd_3269757] using wordTrace_append hprefix tailTrace_3269757
  have hstable : (prefixWord ++ tailWord_3269757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269757).length < 2 ^ (prefixWord ++ tailWord_3269757).sum := by decide
  have hdescent : baseEnd_3269757 < baseStart_3269757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269767 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3269767 : Nat := 118140960795 + 3269767 * 2 ^ 59
def prefixEnd_3269767 : Nat := 4983230072969 + 3 ^ 40 * 3269767 * 2
def baseEnd_3269767 : Nat := 1678962099209813755275121

theorem tailTrace_3269767 : CollatzResearch.WordTrace tailWord_3269767 prefixEnd_3269767 1678962099209813755275121 := by
  unfold tailWord_3269767
  simp only [CollatzResearch.WordTrace]
  refine ⟨119258199945200065589687555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79505466630133377059791703 119258199945200065589687555)
  ·
    refine ⟨178887299917800098384531333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119258199945200065589687555 178887299917800098384531333)
    ·
      refine ⟨33541368734587518447099625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178887299917800098384531333 33541368734587518447099625)
      ·
        refine ⟨25156026550940638835324719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33541368734587518447099625 25156026550940638835324719)
        ·
          refine ⟨37734039826410958252987079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156026550940638835324719 37734039826410958252987079)
          ·
            refine ⟨56601059739616437379480619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37734039826410958252987079 56601059739616437379480619)
            ·
              refine ⟨84901589609424656069220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56601059739616437379480619 84901589609424656069220929)
              ·
                refine ⟨63676192207068492051915697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84901589609424656069220929 63676192207068492051915697)
                ·
                  refine ⟨47757144155301369038936773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63676192207068492051915697 47757144155301369038936773)
                  ·
                    refine ⟨8954464529119006694800645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47757144155301369038936773 8954464529119006694800645)
                    ·
                      refine ⟨1678962099209813755275121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8954464529119006694800645 1678962099209813755275121)
                      ·
                        rfl

theorem cell23_3269767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3269767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269767 prefixEnd_3269767 := by exact prefixLift 3269767
  have htrace : WordTrace (prefixWord ++ tailWord_3269767) baseStart_3269767 baseEnd_3269767 := by
    simpa [prefixWord, tailWord_3269767, baseEnd_3269767] using wordTrace_append hprefix tailTrace_3269767
  have hstable : (prefixWord ++ tailWord_3269767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269767).length < 2 ^ (prefixWord ++ tailWord_3269767).sum := by decide
  have hdescent : baseEnd_3269767 < baseStart_3269767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269791 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3269791 : Nat := 118140960795 + 3269791 * 2 ^ 59
def prefixEnd_3269791 : Nat := 4983230072969 + 3 ^ 40 * 3269791 * 2
def baseEnd_3269791 : Nat := 1678974422745521661375011

theorem tailTrace_3269791 : CollatzResearch.WordTrace tailWord_3269791 prefixEnd_3269791 1678974422745521661375011 := by
  unfold tailWord_3269791
  simp only [CollatzResearch.WordTrace]
  refine ⟨119259075297113117688561227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79506050198075411792374151 119259075297113117688561227)
  ·
    refine ⟨178888612945669676532841841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119259075297113117688561227 178888612945669676532841841)
    ·
      refine ⟨134166459709252257399631381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178888612945669676532841841 134166459709252257399631381)
      ·
        refine ⟨6289052798871199565607721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134166459709252257399631381 6289052798871199565607721)
        ·
          refine ⟨4716789599153399674205791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6289052798871199565607721 4716789599153399674205791)
          ·
            refine ⟨7075184398730099511308687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716789599153399674205791 7075184398730099511308687)
            ·
              refine ⟨10612776598095149266963031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075184398730099511308687 10612776598095149266963031)
              ·
                refine ⟨15919164897142723900444547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612776598095149266963031 15919164897142723900444547)
                ·
                  refine ⟨23878747345714085850666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15919164897142723900444547 23878747345714085850666821)
                  ·
                    refine ⟨4477265127321391097000029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23878747345714085850666821 4477265127321391097000029)
                    ·
                      refine ⟨1678974422745521661375011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4477265127321391097000029 1678974422745521661375011)
                      ·
                        rfl

theorem cell23_3269791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3269791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269791 prefixEnd_3269791 := by exact prefixLift 3269791
  have htrace : WordTrace (prefixWord ++ tailWord_3269791) baseStart_3269791 baseEnd_3269791 := by
    simpa [prefixWord, tailWord_3269791, baseEnd_3269791] using wordTrace_append hprefix tailTrace_3269791
  have hstable : (prefixWord ++ tailWord_3269791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269791).length < 2 ^ (prefixWord ++ tailWord_3269791).sum := by decide
  have hdescent : baseEnd_3269791 < baseStart_3269791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269821 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3269821 : Nat := 118140960795 + 3269821 * 2 ^ 59
def prefixEnd_3269821 : Nat := 4983230072969 + 3 ^ 40 * 3269821 * 2
def baseEnd_3269821 : Nat := 1678989827165156543999873

theorem tailTrace_3269821 : CollatzResearch.WordTrace tailWord_3269821 prefixEnd_3269821 1678989827165156543999873 := by
  unfold tailWord_3269821
  simp only [CollatzResearch.WordTrace]
  refine ⟨119260169487004432812153317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79506779658002955208102211 119260169487004432812153317)
  ·
    refine ⟨22361281778813331152278747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119260169487004432812153317 22361281778813331152278747)
    ·
      refine ⟨33541922668219996728418121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22361281778813331152278747 33541922668219996728418121)
      ·
        refine ⟨25156442001164997546313591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33541922668219996728418121 25156442001164997546313591)
        ·
          refine ⟨37734663001747496319470387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25156442001164997546313591 37734663001747496319470387)
          ·
            refine ⟨56601994502621244479205581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37734663001747496319470387 56601994502621244479205581)
            ·
              refine ⟨21225747938482966679702093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56601994502621244479205581 21225747938482966679702093)
              ·
                refine ⟨7959655476931112504888285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21225747938482966679702093 7959655476931112504888285)
                ·
                  refine ⟨2984870803849167189333107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7959655476931112504888285 2984870803849167189333107)
                  ·
                    refine ⟨4477306205773750783999661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2984870803849167189333107 4477306205773750783999661)
                    ·
                      refine ⟨1678989827165156543999873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4477306205773750783999661 1678989827165156543999873)
                      ·
                        rfl

theorem cell23_3269821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3269821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269821 prefixEnd_3269821 := by exact prefixLift 3269821
  have htrace : WordTrace (prefixWord ++ tailWord_3269821) baseStart_3269821 baseEnd_3269821 := by
    simpa [prefixWord, tailWord_3269821, baseEnd_3269821] using wordTrace_append hprefix tailTrace_3269821
  have hstable : (prefixWord ++ tailWord_3269821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269821).length < 2 ^ (prefixWord ++ tailWord_3269821).sum := by decide
  have hdescent : baseEnd_3269821 < baseStart_3269821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269827 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_3269827 : Nat := 118140960795 + 3269827 * 2 ^ 59
def prefixEnd_3269827 : Nat := 4983230072969 + 3 ^ 40 * 3269827 * 2
def baseEnd_3269827 : Nat := 1678992908049083520524845

theorem tailTrace_3269827 : CollatzResearch.WordTrace tailWord_3269827 prefixEnd_3269827 1678992908049083520524845 := by
  unfold tailWord_3269827
  simp only [CollatzResearch.WordTrace]
  refine ⟨119260388324982695836871735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79506925549988463891247823 119260388324982695836871735)
  ·
    refine ⟨178890582487474043755307603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119260388324982695836871735 178890582487474043755307603)
    ·
      refine ⟨268335873731211065632961405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178890582487474043755307603 268335873731211065632961405)
      ·
        refine ⟨100625952649204149612360527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268335873731211065632961405 100625952649204149612360527)
        ·
          refine ⟨150938928973806224418540791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100625952649204149612360527 150938928973806224418540791)
          ·
            refine ⟨226408393460709336627811187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150938928973806224418540791 226408393460709336627811187)
            ·
              refine ⟨339612590191064004941716781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226408393460709336627811187 339612590191064004941716781)
              ·
                refine ⟨127354721321649001853143793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339612590191064004941716781 127354721321649001853143793)
                ·
                  refine ⟨95516040991236751389857845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127354721321649001853143793 95516040991236751389857845)
                  ·
                    refine ⟨8954628842928445442799173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95516040991236751389857845 8954628842928445442799173)
                    ·
                      refine ⟨1678992908049083520524845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8954628842928445442799173 1678992908049083520524845)
                      ·
                        rfl

theorem cell23_3269827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_3269827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269827 prefixEnd_3269827 := by exact prefixLift 3269827
  have htrace : WordTrace (prefixWord ++ tailWord_3269827) baseStart_3269827 baseEnd_3269827 := by
    simpa [prefixWord, tailWord_3269827, baseEnd_3269827] using wordTrace_append hprefix tailTrace_3269827
  have hstable : (prefixWord ++ tailWord_3269827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269827).length < 2 ^ (prefixWord ++ tailWord_3269827).sum := by decide
  have hdescent : baseEnd_3269827 < baseStart_3269827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269828 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 6]
def baseStart_3269828 : Nat := 118140960795 + 3269828 * 2 ^ 59
def prefixEnd_3269828 : Nat := 4983230072969 + 3 ^ 40 * 3269828 * 2
def baseEnd_3269828 : Nat := 186554824614415335179149

theorem tailTrace_3269828 : CollatzResearch.WordTrace tailWord_3269828 prefixEnd_3269828 186554824614415335179149 := by
  unfold tailWord_3269828
  simp only [CollatzResearch.WordTrace]
  refine ⟨59630212398989536503829069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79506949865319382005105425 59630212398989536503829069)
  ·
    refine ⟨22361329649621076188935901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59630212398989536503829069 22361329649621076188935901)
    ·
      refine ⟨8385498618607903570850963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22361329649621076188935901 8385498618607903570850963)
      ·
        refine ⟨12578247927911855356276445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8385498618607903570850963 12578247927911855356276445)
        ·
          refine ⟨4716842972966945758603667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12578247927911855356276445 4716842972966945758603667)
          ·
            refine ⟨7075264459450418637905501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716842972966945758603667 7075264459450418637905501)
            ·
              refine ⟨2653224172293906989214563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7075264459450418637905501 2653224172293906989214563)
              ·
                refine ⟨3979836258440860483821845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653224172293906989214563 3979836258440860483821845)
                ·
                  refine ⟨186554824614415335179149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979836258440860483821845 186554824614415335179149)
                  ·
                    rfl

theorem cell23_3269828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_3269828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269828 prefixEnd_3269828 := by exact prefixLift 3269828
  have htrace : WordTrace (prefixWord ++ tailWord_3269828) baseStart_3269828 baseEnd_3269828 := by
    simpa [prefixWord, tailWord_3269828, baseEnd_3269828] using wordTrace_append hprefix tailTrace_3269828
  have hstable : (prefixWord ++ tailWord_3269828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269828).length < 2 ^ (prefixWord ++ tailWord_3269828).sum := by decide
  have hdescent : baseEnd_3269828 < baseStart_3269828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269867 : List Nat := [1, 1, 1, 1, 2, 6, 11]
def baseStart_3269867 : Nat := 118140960795 + 3269867 * 2 ^ 59
def prefixEnd_3269867 : Nat := 4983230072969 + 3 ^ 40 * 3269867 * 2
def baseEnd_3269867 : Nat := 20728561077472387210181

theorem tailTrace_3269867 : CollatzResearch.WordTrace tailWord_3269867 prefixEnd_3269867 20728561077472387210181 := by
  unfold tailWord_3269867
  simp only [CollatzResearch.WordTrace]
  refine ⟨119261847244837782668327855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79507898163225188445551903 119261847244837782668327855)
  ·
    refine ⟨178892770867256674002491783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119261847244837782668327855 178892770867256674002491783)
    ·
      refine ⟨268339156300885011003737675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178892770867256674002491783 268339156300885011003737675)
      ·
        refine ⟨402508734451327516505606513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268339156300885011003737675 402508734451327516505606513)
        ·
          refine ⟨301881550838495637379204885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402508734451327516505606513 301881550838495637379204885)
          ·
            refine ⟨14150697695554483002150229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 301881550838495637379204885 14150697695554483002150229)
            ·
              refine ⟨20728561077472387210181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14150697695554483002150229 20728561077472387210181)
              ·
                rfl

theorem cell23_3269867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 11].length) (baseStart_3269867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269867 prefixEnd_3269867 := by exact prefixLift 3269867
  have htrace : WordTrace (prefixWord ++ tailWord_3269867) baseStart_3269867 baseEnd_3269867 := by
    simpa [prefixWord, tailWord_3269867, baseEnd_3269867] using wordTrace_append hprefix tailTrace_3269867
  have hstable : (prefixWord ++ tailWord_3269867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269867).length < 2 ^ (prefixWord ++ tailWord_3269867).sum := by decide
  have hdescent : baseEnd_3269867 < baseStart_3269867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269911 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3269911 : Nat := 118140960795 + 3269911 * 2 ^ 59
def prefixEnd_3269911 : Nat := 4983230072969 + 3 ^ 40 * 3269911 * 2
def baseEnd_3269911 : Nat := 1679036040424061191874459

theorem tailTrace_3269911 : CollatzResearch.WordTrace tailWord_3269911 prefixEnd_3269911 1679036040424061191874459 := by
  unfold tailWord_3269911
  simp only [CollatzResearch.WordTrace]
  refine ⟨119263452056678378182929587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79508968037785585455286391 119263452056678378182929587)
  ·
    refine ⟨178895178085017567274394381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119263452056678378182929587 178895178085017567274394381)
    ·
      refine ⟨67085691781881587727897893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178895178085017567274394381 67085691781881587727897893)
      ·
        refine ⟨12578567209102797698980855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67085691781881587727897893 12578567209102797698980855)
        ·
          refine ⟨18867850813654196548471283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12578567209102797698980855 18867850813654196548471283)
          ·
            refine ⟨28301776220481294822706925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867850813654196548471283 28301776220481294822706925)
            ·
              refine ⟨10613166082680485558515097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28301776220481294822706925 10613166082680485558515097)
              ·
                refine ⟨7959874562010364168886323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10613166082680485558515097 7959874562010364168886323)
                ·
                  refine ⟨11939811843015546253329485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959874562010364168886323 11939811843015546253329485)
                  ·
                    refine ⟨4477429441130829844998557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11939811843015546253329485 4477429441130829844998557)
                    ·
                      refine ⟨1679036040424061191874459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4477429441130829844998557 1679036040424061191874459)
                      ·
                        rfl

theorem cell23_3269911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3269911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269911 prefixEnd_3269911 := by exact prefixLift 3269911
  have htrace : WordTrace (prefixWord ++ tailWord_3269911) baseStart_3269911 baseEnd_3269911 := by
    simpa [prefixWord, tailWord_3269911, baseEnd_3269911] using wordTrace_append hprefix tailTrace_3269911
  have hstable : (prefixWord ++ tailWord_3269911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269911).length < 2 ^ (prefixWord ++ tailWord_3269911).sum := by decide
  have hdescent : baseEnd_3269911 < baseStart_3269911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269918 : List Nat := [4, 3, 2, 1, 3, 10]
def baseStart_3269918 : Nat := 118140960795 + 3269918 * 2 ^ 59
def prefixEnd_3269918 : Nat := 4983230072969 + 3 ^ 40 * 3269918 * 2
def baseEnd_3269918 : Nat := 6909628126702233187189

theorem tailTrace_3269918 : CollatzResearch.WordTrace tailWord_3269918 prefixEnd_3269918 6909628126702233187189 := by
  unfold tailWord_3269918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907963420956627297304301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79509138245102012252289605 14907963420956627297304301)
  ·
    refine ⟨5590486282858735236489113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14907963420956627297304301 5590486282858735236489113)
    ·
      refine ⟨4192864712144051427366835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5590486282858735236489113 4192864712144051427366835)
      ·
        refine ⟨6289297068216077141050253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192864712144051427366835 6289297068216077141050253)
        ·
          refine ⟨2358486400581028927893845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6289297068216077141050253 2358486400581028927893845)
          ·
            refine ⟨6909628126702233187189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2358486400581028927893845 6909628126702233187189)
            ·
              rfl

theorem cell23_3269918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 10].length) (baseStart_3269918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269918 prefixEnd_3269918 := by exact prefixLift 3269918
  have htrace : WordTrace (prefixWord ++ tailWord_3269918) baseStart_3269918 baseEnd_3269918 := by
    simpa [prefixWord, tailWord_3269918, baseEnd_3269918] using wordTrace_append hprefix tailTrace_3269918
  have hstable : (prefixWord ++ tailWord_3269918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269918).length < 2 ^ (prefixWord ++ tailWord_3269918).sum := by decide
  have hdescent : baseEnd_3269918 < baseStart_3269918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269938 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_3269938 : Nat := 118140960795 + 3269938 * 2 ^ 59
def prefixEnd_3269938 : Nat := 4983230072969 + 3 ^ 40 * 3269938 * 2
def baseEnd_3269938 : Nat := 1679049904401732586236835

theorem tailTrace_3269938 : CollatzResearch.WordTrace tailWord_3269938 prefixEnd_3269938 1679049904401732586236835 := by
  unfold tailWord_3269938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816109206895140448540617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79509624551720374529441645 29816109206895140448540617)
  ·
    refine ⟨22362081905171355336405463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29816109206895140448540617 22362081905171355336405463)
    ·
      refine ⟨33543122857757033004608195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22362081905171355336405463 33543122857757033004608195)
      ·
        refine ⟨50314684286635549506912293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33543122857757033004608195 50314684286635549506912293)
        ·
          refine ⟨9434003303744165532546055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50314684286635549506912293 9434003303744165532546055)
          ·
            refine ⟨14151004955616248298819083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9434003303744165532546055 14151004955616248298819083)
            ·
              refine ⟨21226507433424372448228625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14151004955616248298819083 21226507433424372448228625)
              ·
                refine ⟨15919880575068279336171469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21226507433424372448228625 15919880575068279336171469)
                ·
                  refine ⟨5969955215650604751064301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15919880575068279336171469 5969955215650604751064301)
                  ·
                    refine ⟨2238733205868976781649113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5969955215650604751064301 2238733205868976781649113)
                    ·
                      refine ⟨1679049904401732586236835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238733205868976781649113 1679049904401732586236835)
                      ·
                        rfl

theorem cell23_3269938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_3269938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269938 prefixEnd_3269938 := by exact prefixLift 3269938
  have htrace : WordTrace (prefixWord ++ tailWord_3269938) baseStart_3269938 baseEnd_3269938 := by
    simpa [prefixWord, tailWord_3269938, baseEnd_3269938] using wordTrace_append hprefix tailTrace_3269938
  have hstable : (prefixWord ++ tailWord_3269938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269938).length < 2 ^ (prefixWord ++ tailWord_3269938).sum := by decide
  have hdescent : baseEnd_3269938 < baseStart_3269938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269968 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2]
def baseStart_3269968 : Nat := 118140960795 + 3269968 * 2 ^ 59
def prefixEnd_3269968 : Nat := 4983230072969 + 3 ^ 40 * 3269968 * 2
def baseEnd_3269968 : Nat := 1679065308821367468861697

theorem tailTrace_3269968 : CollatzResearch.WordTrace tailWord_3269968 prefixEnd_3269968 1679065308821367468861697 := by
  unfold tailWord_3269968
  simp only [CollatzResearch.WordTrace]
  refine ⟨59632765508735938458877279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79510354011647917945169705 59632765508735938458877279)
  ·
    refine ⟨89449148263103907688315919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59632765508735938458877279 89449148263103907688315919)
    ·
      refine ⟨134173722394655861532473879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89449148263103907688315919 134173722394655861532473879)
      ·
        refine ⟨201260583591983792298710819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134173722394655861532473879 201260583591983792298710819)
        ·
          refine ⟨301890875387975688448066229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201260583591983792298710819 301890875387975688448066229)
          ·
            refine ⟨28302269567622720792006209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301890875387975688448066229 28302269567622720792006209)
            ·
              refine ⟨21226702175717040594004657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28302269567622720792006209 21226702175717040594004657)
              ·
                refine ⟨15920026631787780445503493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21226702175717040594004657 15920026631787780445503493)
                ·
                  refine ⟨2985004993460208833531905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15920026631787780445503493 2985004993460208833531905)
                  ·
                    refine ⟨2238753745095156625148929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985004993460208833531905 2238753745095156625148929)
                    ·
                      refine ⟨1679065308821367468861697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238753745095156625148929 1679065308821367468861697)
                      ·
                        rfl

theorem cell23_3269968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2].length) (baseStart_3269968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3269968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3269968 prefixEnd_3269968 := by exact prefixLift 3269968
  have htrace : WordTrace (prefixWord ++ tailWord_3269968) baseStart_3269968 baseEnd_3269968 := by
    simpa [prefixWord, tailWord_3269968, baseEnd_3269968] using wordTrace_append hprefix tailTrace_3269968
  have hstable : (prefixWord ++ tailWord_3269968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269968).length < 2 ^ (prefixWord ++ tailWord_3269968).sum := by decide
  have hdescent : baseEnd_3269968 < baseStart_3269968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270001 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_3270001 : Nat := 118140960795 + 3270001 * 2 ^ 59
def prefixEnd_3270001 : Nat := 4983230072969 + 3 ^ 40 * 3270001 * 2
def baseEnd_3270001 : Nat := 1679082253682965839749045

theorem tailTrace_3270001 : CollatzResearch.WordTrace tailWord_3270001 prefixEnd_3270001 1679082253682965839749045 := by
  unfold tailWord_3270001
  simp only [CollatzResearch.WordTrace]
  refine ⟨119266734626352323553705857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79511156417568215702470571 119266734626352323553705857)
  ·
    refine ⟨89450050969764242665279393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119266734626352323553705857 89450050969764242665279393)
    ·
      refine ⟨67087538227323181998959545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89450050969764242665279393 67087538227323181998959545)
      ·
        refine ⟨50315653670492386499219659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67087538227323181998959545 50315653670492386499219659)
        ·
          refine ⟨75473480505738579748829489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50315653670492386499219659 75473480505738579748829489)
          ·
            refine ⟨56605110379303934811622117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75473480505738579748829489 56605110379303934811622117)
            ·
              refine ⟨10613458196119487777179147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56605110379303934811622117 10613458196119487777179147)
              ·
                refine ⟨15920187294179231665768721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613458196119487777179147 15920187294179231665768721)
                ·
                  refine ⟨11940140470634423749326541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15920187294179231665768721 11940140470634423749326541)
                  ·
                    refine ⟨4477552676487908905997453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11940140470634423749326541 4477552676487908905997453)
                    ·
                      refine ⟨1679082253682965839749045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4477552676487908905997453 1679082253682965839749045)
                      ·
                        rfl

theorem cell23_3270001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_3270001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270001 prefixEnd_3270001 := by exact prefixLift 3270001
  have htrace : WordTrace (prefixWord ++ tailWord_3270001) baseStart_3270001 baseEnd_3270001 := by
    simpa [prefixWord, tailWord_3270001, baseEnd_3270001] using wordTrace_append hprefix tailTrace_3270001
  have hstable : (prefixWord ++ tailWord_3270001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270001).length < 2 ^ (prefixWord ++ tailWord_3270001).sum := by decide
  have hdescent : baseEnd_3270001 < baseStart_3270001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270002 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3270002 : Nat := 118140960795 + 3270002 * 2 ^ 59
def prefixEnd_3270002 : Nat := 4983230072969 + 3 ^ 40 * 3270002 * 2
def baseEnd_3270002 : Nat := 1679082767163620335836541

theorem tailTrace_3270002 : CollatzResearch.WordTrace tailWord_3270002 prefixEnd_3270002 1679082767163620335836541 := by
  unfold tailWord_3270002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29816692774837175181123065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79511180732899133816328173 29816692774837175181123065)
  ·
    refine ⟨22362519581127881385842299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29816692774837175181123065 22362519581127881385842299)
    ·
      refine ⟨33543779371691822078763449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22362519581127881385842299 33543779371691822078763449)
      ·
        refine ⟨25157834528768866559072587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33543779371691822078763449 25157834528768866559072587)
        ·
          refine ⟨37736751793153299838608881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25157834528768866559072587 37736751793153299838608881)
          ·
            refine ⟨28302563844864974878956661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37736751793153299838608881 28302563844864974878956661)
            ·
              refine ⟨2653365360456091394902187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28302563844864974878956661 2653365360456091394902187)
              ·
                refine ⟨3980048040684137092353281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653365360456091394902187 3980048040684137092353281)
                ·
                  refine ⟨2985036030513102819264961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980048040684137092353281 2985036030513102819264961)
                  ·
                    refine ⟨2238777022884827114448721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985036030513102819264961 2238777022884827114448721)
                    ·
                      refine ⟨1679082767163620335836541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238777022884827114448721 1679082767163620335836541)
                      ·
                        rfl

theorem cell23_3270002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3270002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270002 prefixEnd_3270002 := by exact prefixLift 3270002
  have htrace : WordTrace (prefixWord ++ tailWord_3270002) baseStart_3270002 baseEnd_3270002 := by
    simpa [prefixWord, tailWord_3270002, baseEnd_3270002] using wordTrace_append hprefix tailTrace_3270002
  have hstable : (prefixWord ++ tailWord_3270002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270002).length < 2 ^ (prefixWord ++ tailWord_3270002).sum := by decide
  have hdescent : baseEnd_3270002 < baseStart_3270002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270025 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 5]
def baseStart_3270025 : Nat := 118140960795 + 3270025 * 2 ^ 59
def prefixEnd_3270025 : Nat := 4983230072969 + 3 ^ 40 * 3270025 * 2
def baseEnd_3270025 : Nat := 186566064135408193983215

theorem tailTrace_3270025 : CollatzResearch.WordTrace tailWord_3270025 prefixEnd_3270025 186566064135408193983215 := by
  unfold tailWord_3270025
  simp only [CollatzResearch.WordTrace]
  refine ⟨119267609978265375652579529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79511739985510250435053019 119267609978265375652579529)
  ·
    refine ⟨89450707483699031739434647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119267609978265375652579529 89450707483699031739434647)
    ·
      refine ⟨134176061225548547609151971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89450707483699031739434647 134176061225548547609151971)
      ·
        refine ⟨201264091838322821413727957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134176061225548547609151971 201264091838322821413727957)
        ·
          refine ⟨4717127152460691126884249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 201264091838322821413727957 4717127152460691126884249)
          ·
            refine ⟨3537845364345518345163187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4717127152460691126884249 3537845364345518345163187)
            ·
              refine ⟨5306768046518277517744781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537845364345518345163187 5306768046518277517744781)
              ·
                refine ⟨1990038017444354069154293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5306768046518277517744781 1990038017444354069154293)
                ·
                  refine ⟨186566064135408193983215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990038017444354069154293 186566064135408193983215)
                  ·
                    rfl

theorem cell23_3270025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 5].length) (baseStart_3270025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270025 prefixEnd_3270025 := by exact prefixLift 3270025
  have htrace : WordTrace (prefixWord ++ tailWord_3270025) baseStart_3270025 baseEnd_3270025 := by
    simpa [prefixWord, tailWord_3270025, baseEnd_3270025] using wordTrace_append hprefix tailTrace_3270025
  have hstable : (prefixWord ++ tailWord_3270025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270025).length < 2 ^ (prefixWord ++ tailWord_3270025).sum := by decide
  have hdescent : baseEnd_3270025 < baseStart_3270025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270041 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3270041 : Nat := 118140960795 + 3270041 * 2 ^ 59
def prefixEnd_3270041 : Nat := 4983230072969 + 3 ^ 40 * 3270041 * 2
def baseEnd_3270041 : Nat := 1679102792909145683248861

theorem tailTrace_3270041 : CollatzResearch.WordTrace tailWord_3270041 prefixEnd_3270041 1679102792909145683248861 := by
  unfold tailWord_3270041
  simp only [CollatzResearch.WordTrace]
  refine ⟨119268193546207410385161977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79512129030804940256774651 119268193546207410385161977)
  ·
    refine ⟨89451145159655557788871483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119268193546207410385161977 89451145159655557788871483)
    ·
      refine ⟨134176717739483336683307225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89451145159655557788871483 134176717739483336683307225)
      ·
        refine ⟨100632538304612502512480419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134176717739483336683307225 100632538304612502512480419)
        ·
          refine ⟨150948807456918753768720629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100632538304612502512480419 150948807456918753768720629)
          ·
            refine ⟨14151450699086133165817559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150948807456918753768720629 14151450699086133165817559)
            ·
              refine ⟨21227176048629199748726339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14151450699086133165817559 21227176048629199748726339)
              ·
                refine ⟨31840764072943799623089509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21227176048629199748726339 31840764072943799623089509)
                ·
                  refine ⟨5970143263676962429329283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31840764072943799623089509 5970143263676962429329283)
                  ·
                    refine ⟨8955214895515443643993925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5970143263676962429329283 8955214895515443643993925)
                    ·
                      refine ⟨1679102792909145683248861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8955214895515443643993925 1679102792909145683248861)
                      ·
                        rfl

theorem cell23_3270041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3270041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270041 prefixEnd_3270041 := by exact prefixLift 3270041
  have htrace : WordTrace (prefixWord ++ tailWord_3270041) baseStart_3270041 baseEnd_3270041 := by
    simpa [prefixWord, tailWord_3270041, baseEnd_3270041] using wordTrace_append hprefix tailTrace_3270041
  have hstable : (prefixWord ++ tailWord_3270041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270041).length < 2 ^ (prefixWord ++ tailWord_3270041).sum := by decide
  have hdescent : baseEnd_3270041 < baseStart_3270041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270064 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 10]
def baseStart_3270064 : Nat := 118140960795 + 3270064 * 2 ^ 59
def prefixEnd_3270064 : Nat := 4983230072969 + 3 ^ 40 * 3270064 * 2
def baseEnd_3270064 : Nat := 186568289218244343695695

theorem tailTrace_3270064 : CollatzResearch.WordTrace tailWord_3270064 prefixEnd_3270064 186568289218244343695695 := by
  unfold tailWord_3270064
  simp only [CollatzResearch.WordTrace]
  refine ⟨59634516212562042656624623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79512688283416056875499497 59634516212562042656624623)
  ·
    refine ⟨89451774318843063984936935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59634516212562042656624623 89451774318843063984936935)
    ·
      refine ⟨134177661478264595977405403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89451774318843063984936935 134177661478264595977405403)
      ·
        refine ⟨201266492217396893966108105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134177661478264595977405403 201266492217396893966108105)
        ·
          refine ⟨150949869163047670474581079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201266492217396893966108105 150949869163047670474581079)
          ·
            refine ⟨226424803744571505711871619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150949869163047670474581079 226424803744571505711871619)
            ·
              refine ⟨339637205616857258567807429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226424803744571505711871619 339637205616857258567807429)
              ·
                refine ⟨63681976053160735981463893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339637205616857258567807429 63681976053160735981463893)
                ·
                  refine ⟨186568289218244343695695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63681976053160735981463893 186568289218244343695695)
                  ·
                    rfl

theorem cell23_3270064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_3270064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270064 prefixEnd_3270064 := by exact prefixLift 3270064
  have htrace : WordTrace (prefixWord ++ tailWord_3270064) baseStart_3270064 baseEnd_3270064 := by
    simpa [prefixWord, tailWord_3270064, baseEnd_3270064] using wordTrace_append hprefix tailTrace_3270064
  have hstable : (prefixWord ++ tailWord_3270064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270064).length < 2 ^ (prefixWord ++ tailWord_3270064).sum := by decide
  have hdescent : baseEnd_3270064 < baseStart_3270064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270101 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3270101 : Nat := 118140960795 + 3270101 * 2 ^ 59
def prefixEnd_3270101 : Nat := 4983230072969 + 3 ^ 40 * 3270101 * 2
def baseEnd_3270101 : Nat := 1679133601748415448498585

theorem tailTrace_3270101 : CollatzResearch.WordTrace tailWord_3270101 prefixEnd_3270101 1679133601748415448498585 := by
  unfold tailWord_3270101
  simp only [CollatzResearch.WordTrace]
  refine ⟨119270381925990040632346157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79513587950660027088230771 119270381925990040632346157)
  ·
    refine ⟨44726393222246265237129809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119270381925990040632346157 44726393222246265237129809)
    ·
      refine ⟨33544794916684698927847357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44726393222246265237129809 33544794916684698927847357)
      ·
        refine ⟨12579298093756762097942759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33544794916684698927847357 12579298093756762097942759)
        ·
          refine ⟨18868947140635143146914139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12579298093756762097942759 18868947140635143146914139)
          ·
            refine ⟨28303420710952714720371209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18868947140635143146914139 28303420710952714720371209)
            ·
              refine ⟨21227565533214536040278407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28303420710952714720371209 21227565533214536040278407)
              ·
                refine ⟨31841348299821804060417611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21227565533214536040278407 31841348299821804060417611)
                ·
                  refine ⟨47762022449732706090626417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31841348299821804060417611 47762022449732706090626417)
                  ·
                    refine ⟨35821516837299529567969813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47762022449732706090626417 35821516837299529567969813)
                    ·
                      refine ⟨1679133601748415448498585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35821516837299529567969813 1679133601748415448498585)
                      ·
                        rfl

theorem cell23_3270101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3270101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270101 prefixEnd_3270101 := by exact prefixLift 3270101
  have htrace : WordTrace (prefixWord ++ tailWord_3270101) baseStart_3270101 baseEnd_3270101 := by
    simpa [prefixWord, tailWord_3270101, baseEnd_3270101] using wordTrace_append hprefix tailTrace_3270101
  have hstable : (prefixWord ++ tailWord_3270101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270101).length < 2 ^ (prefixWord ++ tailWord_3270101).sum := by decide
  have hdescent : baseEnd_3270101 < baseStart_3270101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270111 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 5, 5]
def baseStart_3270111 : Nat := 118140960795 + 3270111 * 2 ^ 59
def prefixEnd_3270111 : Nat := 4983230072969 + 3 ^ 40 * 3270111 * 2
def baseEnd_3270111 : Nat := 559712912184986803124513

theorem tailTrace_3270111 : CollatzResearch.WordTrace tailWord_3270111 prefixEnd_3270111 559712912184986803124513 := by
  unfold tailWord_3270111
  simp only [CollatzResearch.WordTrace]
  refine ⟨119270746655953812340210187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79513831103969208226806791 119270746655953812340210187)
  ·
    refine ⟨178906119983930718510315281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119270746655953812340210187 178906119983930718510315281)
    ·
      refine ⟨134179589987948038882736461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178906119983930718510315281 134179589987948038882736461)
      ·
        refine ⟨50317346245480514581026173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134179589987948038882736461 50317346245480514581026173)
        ·
          refine ⟨18869004842055192967884815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50317346245480514581026173 18869004842055192967884815)
          ·
            refine ⟨28303507263082789451827223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18869004842055192967884815 28303507263082789451827223)
            ·
              refine ⟨42455260894624184177740835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28303507263082789451827223 42455260894624184177740835)
              ·
                refine ⟨63682891341936276266611253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42455260894624184177740835 63682891341936276266611253)
                ·
                  refine ⟨5970271063306525899994805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63682891341936276266611253 5970271063306525899994805)
                  ·
                    refine ⟨559712912184986803124513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970271063306525899994805 559712912184986803124513)
                    ·
                      rfl

theorem cell23_3270111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_3270111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270111 prefixEnd_3270111 := by exact prefixLift 3270111
  have htrace : WordTrace (prefixWord ++ tailWord_3270111) baseStart_3270111 baseEnd_3270111 := by
    simpa [prefixWord, tailWord_3270111, baseEnd_3270111] using wordTrace_append hprefix tailTrace_3270111
  have hstable : (prefixWord ++ tailWord_3270111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270111).length < 2 ^ (prefixWord ++ tailWord_3270111).sum := by decide
  have hdescent : baseEnd_3270111 < baseStart_3270111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270145 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3270145 : Nat := 118140960795 + 3270145 * 2 ^ 59
def prefixEnd_3270145 : Nat := 4983230072969 + 3 ^ 40 * 3270145 * 2
def baseEnd_3270145 : Nat := 559718731632404425449461

theorem tailTrace_3270145 : CollatzResearch.WordTrace tailWord_3270145 prefixEnd_3270145 559718731632404425449461 := by
  unfold tailWord_3270145
  simp only [CollatzResearch.WordTrace]
  refine ⟨119271986737830636146947889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79514657825220424097965259 119271986737830636146947889)
  ·
    refine ⟨89453990053372977110210917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119271986737830636146947889 89453990053372977110210917)
    ·
      refine ⟨16772623135007433208164547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89453990053372977110210917 16772623135007433208164547)
      ·
        refine ⟨25158934702511149812246821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772623135007433208164547 25158934702511149812246821)
        ·
          refine ⟨4717300256720840589796279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25158934702511149812246821 4717300256720840589796279)
          ·
            refine ⟨7075950385081260884694419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717300256720840589796279 7075950385081260884694419)
            ·
              refine ⟨10613925577621891327041629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075950385081260884694419 10613925577621891327041629)
              ·
                refine ⟨3980222091608209247640611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10613925577621891327041629 3980222091608209247640611)
                ·
                  refine ⟨5970333137412313871460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980222091608209247640611 5970333137412313871460917)
                  ·
                    refine ⟨559718731632404425449461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970333137412313871460917 559718731632404425449461)
                    ·
                      rfl

theorem cell23_3270145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3270145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270145 prefixEnd_3270145 := by exact prefixLift 3270145
  have htrace : WordTrace (prefixWord ++ tailWord_3270145) baseStart_3270145 baseEnd_3270145 := by
    simpa [prefixWord, tailWord_3270145, baseEnd_3270145] using wordTrace_append hprefix tailTrace_3270145
  have hstable : (prefixWord ++ tailWord_3270145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270145).length < 2 ^ (prefixWord ++ tailWord_3270145).sum := by decide
  have hdescent : baseEnd_3270145 < baseStart_3270145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270161 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3270161 : Nat := 118140960795 + 3270161 * 2 ^ 59
def prefixEnd_3270161 : Nat := 4983230072969 + 3 ^ 40 * 3270161 * 2
def baseEnd_3270161 : Nat := 1679164410587685213748309

theorem tailTrace_3270161 : CollatzResearch.WordTrace tailWord_3270161 prefixEnd_3270161 1679164410587685213748309 := by
  unfold tailWord_3270161
  simp only [CollatzResearch.WordTrace]
  refine ⟨119272570305772670879530337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79515046870515113919686891 119272570305772670879530337)
  ·
    refine ⟨89454427729329503159647753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119272570305772670879530337 89454427729329503159647753)
    ·
      refine ⟨67090820796997127369735815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89454427729329503159647753 67090820796997127369735815)
      ·
        refine ⟨100636231195495691054603723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67090820796997127369735815 100636231195495691054603723)
        ·
          refine ⟨150954346793243536581905585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100636231195495691054603723 150954346793243536581905585)
          ·
            refine ⟨113215760094932652436429189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150954346793243536581905585 113215760094932652436429189)
            ·
              refine ⟨21227955017799872331830473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113215760094932652436429189 21227955017799872331830473)
              ·
                refine ⟨15920966263349904248872855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21227955017799872331830473 15920966263349904248872855)
                ·
                  refine ⟨23881449395024856373309283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15920966263349904248872855 23881449395024856373309283)
                  ·
                    refine ⟨35822174092537284559963925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23881449395024856373309283 35822174092537284559963925)
                    ·
                      refine ⟨1679164410587685213748309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35822174092537284559963925 1679164410587685213748309)
                      ·
                        rfl

theorem cell23_3270161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3270161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270161 prefixEnd_3270161 := by exact prefixLift 3270161
  have htrace : WordTrace (prefixWord ++ tailWord_3270161) baseStart_3270161 baseEnd_3270161 := by
    simpa [prefixWord, tailWord_3270161, baseEnd_3270161] using wordTrace_append hprefix tailTrace_3270161
  have hstable : (prefixWord ++ tailWord_3270161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270161).length < 2 ^ (prefixWord ++ tailWord_3270161).sum := by decide
  have hdescent : baseEnd_3270161 < baseStart_3270161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270199 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_3270199 : Nat := 118140960795 + 3270199 * 2 ^ 59
def prefixEnd_3270199 : Nat := 4983230072969 + 3 ^ 40 * 3270199 * 2
def baseEnd_3270199 : Nat := 1679183922852556065073135

theorem tailTrace_3270199 : CollatzResearch.WordTrace tailWord_3270199 prefixEnd_3270199 1679183922852556065073135 := by
  unfold tailWord_3270199
  simp only [CollatzResearch.WordTrace]
  refine ⟨119273956279635003369413651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79515970853090002246275767 119273956279635003369413651)
  ·
    refine ⟨178910934419452505054120477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119273956279635003369413651 178910934419452505054120477)
    ·
      refine ⟨67091600407294689395295179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178910934419452505054120477 67091600407294689395295179)
      ·
        refine ⟨100637400610942034092942769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67091600407294689395295179 100637400610942034092942769)
        ·
          refine ⟨75478050458206525569707077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100637400610942034092942769 75478050458206525569707077)
          ·
            refine ⟨14152134460913723544320077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75478050458206525569707077 14152134460913723544320077)
            ·
              refine ⟨5307050422842646329120029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14152134460913723544320077 5307050422842646329120029)
              ·
                refine ⟨1990143908565992373420011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5307050422842646329120029 1990143908565992373420011)
                ·
                  refine ⟨2985215862848988560130017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990143908565992373420011 2985215862848988560130017)
                  ·
                    refine ⟨2238911897136741420097513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985215862848988560130017 2238911897136741420097513)
                    ·
                      refine ⟨1679183922852556065073135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238911897136741420097513 1679183922852556065073135)
                      ·
                        rfl

theorem cell23_3270199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_3270199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270199 prefixEnd_3270199 := by exact prefixLift 3270199
  have htrace : WordTrace (prefixWord ++ tailWord_3270199) baseStart_3270199 baseEnd_3270199 := by
    simpa [prefixWord, tailWord_3270199, baseEnd_3270199] using wordTrace_append hprefix tailTrace_3270199
  have hstable : (prefixWord ++ tailWord_3270199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270199).length < 2 ^ (prefixWord ++ tailWord_3270199).sum := by decide
  have hdescent : baseEnd_3270199 < baseStart_3270199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270205 : List Nat := [1, 4, 1, 3, 4, 1, 9]
def baseStart_3270205 : Nat := 118140960795 + 3270205 * 2 ^ 59
def prefixEnd_3270205 : Nat := 4983230072969 + 3 ^ 40 * 3270205 * 2
def baseEnd_3270205 : Nat := 20730703749833123970347

theorem tailTrace_3270205 : CollatzResearch.WordTrace tailWord_3270205 prefixEnd_3270205 20730703749833123970347 := by
  unfold tailWord_3270205
  simp only [CollatzResearch.WordTrace]
  refine ⟨119274175117613266394132069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79516116745075510929421379 119274175117613266394132069)
  ·
    refine ⟨22363907834552487448899763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119274175117613266394132069 22363907834552487448899763)
    ·
      refine ⟨33545861751828731173349645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22363907834552487448899763 33545861751828731173349645)
      ·
        refine ⟨12579698156935774190006117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33545861751828731173349645 12579698156935774190006117)
        ·
          refine ⟨2358693404425457660626147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12579698156935774190006117 2358693404425457660626147)
          ·
            refine ⟨3538040106638186490939221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358693404425457660626147 3538040106638186490939221)
            ·
              refine ⟨20730703749833123970347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3538040106638186490939221 20730703749833123970347)
              ·
                rfl

theorem cell23_3270205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 9].length) (baseStart_3270205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270205 prefixEnd_3270205 := by exact prefixLift 3270205
  have htrace : WordTrace (prefixWord ++ tailWord_3270205) baseStart_3270205 baseEnd_3270205 := by
    simpa [prefixWord, tailWord_3270205, baseEnd_3270205] using wordTrace_append hprefix tailTrace_3270205
  have hstable : (prefixWord ++ tailWord_3270205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270205).length < 2 ^ (prefixWord ++ tailWord_3270205).sum := by decide
  have hdescent : baseEnd_3270205 < baseStart_3270205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270225 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_3270225 : Nat := 118140960795 + 3270225 * 2 ^ 59
def prefixEnd_3270225 : Nat := 4983230072969 + 3 ^ 40 * 3270225 * 2
def baseEnd_3270225 : Nat := 1679197273349572963348015

theorem tailTrace_3270225 : CollatzResearch.WordTrace tailWord_3270225 prefixEnd_3270225 1679197273349572963348015 := by
  unfold tailWord_3270225
  simp only [CollatzResearch.WordTrace]
  refine ⟨119274904577540809809860129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79516603051693873206573419 119274904577540809809860129)
  ·
    refine ⟨89456178433155607357395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119274904577540809809860129 89456178433155607357395097)
    ·
      refine ⟨67092133824866705518046323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89456178433155607357395097 67092133824866705518046323)
      ·
        refine ⟨100638200737300058277069485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67092133824866705518046323 100638200737300058277069485)
        ·
          refine ⟨37739325276487521853901057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100638200737300058277069485 37739325276487521853901057)
          ·
            refine ⟨28304493957365641390425793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37739325276487521853901057 28304493957365641390425793)
            ·
              refine ⟨21228370468024231042819345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28304493957365641390425793 21228370468024231042819345)
              ·
                refine ⟨15921277851018173282114509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21228370468024231042819345 15921277851018173282114509)
                ·
                  refine ⟨5970479194131814980792941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15921277851018173282114509 5970479194131814980792941)
                  ·
                    refine ⟨2238929697799430617797353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5970479194131814980792941 2238929697799430617797353)
                    ·
                      refine ⟨1679197273349572963348015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2238929697799430617797353 1679197273349572963348015)
                      ·
                        rfl

theorem cell23_3270225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_3270225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270225 prefixEnd_3270225 := by exact prefixLift 3270225
  have htrace : WordTrace (prefixWord ++ tailWord_3270225) baseStart_3270225 baseEnd_3270225 := by
    simpa [prefixWord, tailWord_3270225, baseEnd_3270225] using wordTrace_append hprefix tailTrace_3270225
  have hstable : (prefixWord ++ tailWord_3270225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270225).length < 2 ^ (prefixWord ++ tailWord_3270225).sum := by decide
  have hdescent : baseEnd_3270225 < baseStart_3270225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_3270251 : Nat := 118140960795 + 3270251 * 2 ^ 59
def prefixEnd_3270251 : Nat := 4983230072969 + 3 ^ 40 * 3270251 * 2
def baseEnd_3270251 : Nat := 1679210623846589861622895

theorem tailTrace_3270251 : CollatzResearch.WordTrace tailWord_3270251 prefixEnd_3270251 1679210623846589861622895 := by
  unfold tailWord_3270251
  simp only [CollatzResearch.WordTrace]
  refine ⟨119275852875446616250306607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79517235250297744166871071 119275852875446616250306607)
  ·
    refine ⟨178913779313169924375459911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119275852875446616250306607 178913779313169924375459911)
    ·
      refine ⟨268370668969754886563189867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178913779313169924375459911 268370668969754886563189867)
      ·
        refine ⟨402556003454632329844784801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268370668969754886563189867 402556003454632329844784801)
        ·
          refine ⟨301917002590974247383588601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402556003454632329844784801 301917002590974247383588601)
          ·
            refine ⟨226437751943230685537691451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301917002590974247383588601 226437751943230685537691451)
            ·
              refine ⟨339656627914846028306537177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226437751943230685537691451 339656627914846028306537177)
              ·
                refine ⟨254742470936134521229902883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339656627914846028306537177 254742470936134521229902883)
                ·
                  refine ⟨382113706404201781844854325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254742470936134521229902883 382113706404201781844854325)
                  ·
                    refine ⟨35823159975393917047955093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 382113706404201781844854325 35823159975393917047955093)
                    ·
                      refine ⟨1679210623846589861622895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35823159975393917047955093 1679210623846589861622895)
                      ·
                        rfl

theorem cell23_3270251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_3270251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270251 prefixEnd_3270251 := by exact prefixLift 3270251
  have htrace : WordTrace (prefixWord ++ tailWord_3270251) baseStart_3270251 baseEnd_3270251 := by
    simpa [prefixWord, tailWord_3270251, baseEnd_3270251] using wordTrace_append hprefix tailTrace_3270251
  have hstable : (prefixWord ++ tailWord_3270251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270251).length < 2 ^ (prefixWord ++ tailWord_3270251).sum := by decide
  have hdescent : baseEnd_3270251 < baseStart_3270251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270268 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3270268 : Nat := 118140960795 + 3270268 * 2 ^ 59
def prefixEnd_3270268 : Nat := 4983230072969 + 3 ^ 40 * 3270268 * 2
def baseEnd_3270268 : Nat := 1679219353017716295110317

theorem tailTrace_3270268 : CollatzResearch.WordTrace tailWord_3270268 prefixEnd_3270268 1679219353017716295110317 := by
  unfold tailWord_3270268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59638236458192514076837729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79517648610923352102450305 59638236458192514076837729)
  ·
    refine ⟨44728677343644385557628297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59638236458192514076837729 44728677343644385557628297)
    ·
      refine ⟨33546508007733289168221223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44728677343644385557628297 33546508007733289168221223)
      ·
        refine ⟨50319762011599933752331835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33546508007733289168221223 50319762011599933752331835)
        ·
          refine ⟨75479643017399900628497753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50319762011599933752331835 75479643017399900628497753)
          ·
            refine ⟨56609732263049925471373315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75479643017399900628497753 56609732263049925471373315)
            ·
              refine ⟨84914598394574888207059973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56609732263049925471373315 84914598394574888207059973)
              ·
                refine ⟨15921487198982791538823745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84914598394574888207059973 15921487198982791538823745)
                ·
                  refine ⟨11941115399237093654117809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15921487198982791538823745 11941115399237093654117809)
                  ·
                    refine ⟨8955836549427820240588357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11941115399237093654117809 8955836549427820240588357)
                    ·
                      refine ⟨1679219353017716295110317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8955836549427820240588357 1679219353017716295110317)
                      ·
                        rfl

theorem cell23_3270268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3270268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270268 prefixEnd_3270268 := by exact prefixLift 3270268
  have htrace : WordTrace (prefixWord ++ tailWord_3270268) baseStart_3270268 baseEnd_3270268 := by
    simpa [prefixWord, tailWord_3270268, baseEnd_3270268] using wordTrace_append hprefix tailTrace_3270268
  have hstable : (prefixWord ++ tailWord_3270268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270268).length < 2 ^ (prefixWord ++ tailWord_3270268).sum := by decide
  have hdescent : baseEnd_3270268 < baseStart_3270268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270368 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 8]
def baseStart_3270368 : Nat := 118140960795 + 3270368 * 2 ^ 59
def prefixEnd_3270368 : Nat := 4983230072969 + 3 ^ 40 * 3270368 * 2
def baseEnd_3270368 : Nat := 186585633453685100428873

theorem tailTrace_3270368 : CollatzResearch.WordTrace tailWord_3270368 prefixEnd_3270368 186585633453685100428873 := by
  unfold tailWord_3270368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59640060108011372616157879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79520080144015163488210505 59640060108011372616157879)
  ·
    refine ⟨89460090162017058924236819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59640060108011372616157879 89460090162017058924236819)
    ·
      refine ⟨134190135243025588386355229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89460090162017058924236819 134190135243025588386355229)
      ·
        refine ⟨50321300716134595644883211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134190135243025588386355229 50321300716134595644883211)
        ·
          refine ⟨75481951074201893467324817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50321300716134595644883211 75481951074201893467324817)
          ·
            refine ⟨56611463305651420100493613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75481951074201893467324817 56611463305651420100493613)
            ·
              refine ⟨21229298739619282537685105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56611463305651420100493613 21229298739619282537685105)
              ·
                refine ⟨15921974054714461903263829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21229298739619282537685105 15921974054714461903263829)
                ·
                  refine ⟨186585633453685100428873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15921974054714461903263829 186585633453685100428873)
                  ·
                    rfl

theorem cell23_3270368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_3270368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270368 prefixEnd_3270368 := by exact prefixLift 3270368
  have htrace : WordTrace (prefixWord ++ tailWord_3270368) baseStart_3270368 baseEnd_3270368 := by
    simpa [prefixWord, tailWord_3270368, baseEnd_3270368] using wordTrace_append hprefix tailTrace_3270368
  have hstable : (prefixWord ++ tailWord_3270368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270368).length < 2 ^ (prefixWord ++ tailWord_3270368).sum := by decide
  have hdescent : baseEnd_3270368 < baseStart_3270368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270382 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_3270382 : Nat := 118140960795 + 3270382 * 2 ^ 59
def prefixEnd_3270382 : Nat := 4983230072969 + 3 ^ 40 * 3270382 * 2
def baseEnd_3270382 : Nat := 1679277889812328849084793

theorem tailTrace_3270382 : CollatzResearch.WordTrace tailWord_3270382 prefixEnd_3270382 1679277889812328849084793 := by
  unfold tailWord_3270382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910078854746503202915675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79520420558648017082216933 14910078854746503202915675)
  ·
    refine ⟨22365118282119754804373513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14910078854746503202915675 22365118282119754804373513)
    ·
      refine ⟨16773838711589816103280135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22365118282119754804373513 16773838711589816103280135)
      ·
        refine ⟨25160758067384724154920203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16773838711589816103280135 25160758067384724154920203)
        ·
          refine ⟨37741137101077086232380305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25160758067384724154920203 37741137101077086232380305)
          ·
            refine ⟨28305852825807814674285229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37741137101077086232380305 28305852825807814674285229)
            ·
              refine ⟨10614694809677930502856961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28305852825807814674285229 10614694809677930502856961)
              ·
                refine ⟨7961021107258447877142721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10614694809677930502856961 7961021107258447877142721)
                ·
                  refine ⟨5970765830443835907857041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7961021107258447877142721 5970765830443835907857041)
                  ·
                    refine ⟨4478074372832876930892781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970765830443835907857041 4478074372832876930892781)
                    ·
                      refine ⟨1679277889812328849084793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4478074372832876930892781 1679277889812328849084793)
                      ·
                        rfl

theorem cell23_3270382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_3270382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270382 prefixEnd_3270382 := by exact prefixLift 3270382
  have htrace : WordTrace (prefixWord ++ tailWord_3270382) baseStart_3270382 baseEnd_3270382 := by
    simpa [prefixWord, tailWord_3270382, baseEnd_3270382] using wordTrace_append hprefix tailTrace_3270382
  have hstable : (prefixWord ++ tailWord_3270382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270382).length < 2 ^ (prefixWord ++ tailWord_3270382).sum := by decide
  have hdescent : baseEnd_3270382 < baseStart_3270382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270402 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3270402 : Nat := 118140960795 + 3270402 * 2 ^ 59
def prefixEnd_3270402 : Nat := 4983230072969 + 3 ^ 40 * 3270402 * 2
def baseEnd_3270402 : Nat := 186587573269490974537189

theorem tailTrace_3270402 : CollatzResearch.WordTrace tailWord_3270402 prefixEnd_3270402 186587573269490974537189 := by
  unfold tailWord_3270402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29820340074474892259763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79520906865266379359368973 29820340074474892259763365)
  ·
    refine ⟨5591313763964042298705631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29820340074474892259763365 5591313763964042298705631)
    ·
      refine ⟨8386970645946063448058447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5591313763964042298705631 8386970645946063448058447)
      ·
        refine ⟨12580455968919095172087671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8386970645946063448058447 12580455968919095172087671)
        ·
          refine ⟨18870683953378642758131507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580455968919095172087671 18870683953378642758131507)
          ·
            refine ⟨28306025930067964137197261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18870683953378642758131507 28306025930067964137197261)
            ·
              refine ⟨10614759723775486551448973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28306025930067964137197261 10614759723775486551448973)
              ·
                refine ⟨3980534896415807456793365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10614759723775486551448973 3980534896415807456793365)
                ·
                  refine ⟨186587573269490974537189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3980534896415807456793365 186587573269490974537189)
                  ·
                    rfl

theorem cell23_3270402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3270402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270402 prefixEnd_3270402 := by exact prefixLift 3270402
  have htrace : WordTrace (prefixWord ++ tailWord_3270402) baseStart_3270402 baseEnd_3270402 := by
    simpa [prefixWord, tailWord_3270402, baseEnd_3270402] using wordTrace_append hprefix tailTrace_3270402
  have hstable : (prefixWord ++ tailWord_3270402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270402).length < 2 ^ (prefixWord ++ tailWord_3270402).sum := by decide
  have hdescent : baseEnd_3270402 < baseStart_3270402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270412 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3270412 : Nat := 118140960795 + 3270412 * 2 ^ 59
def prefixEnd_3270412 : Nat := 4983230072969 + 3 ^ 40 * 3270412 * 2
def baseEnd_3270412 : Nat := 1679293294231963731709655

theorem tailTrace_3270412 : CollatzResearch.WordTrace tailWord_3270412 prefixEnd_3270412 1679293294231963731709655 := by
  unfold tailWord_3270412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59640862513931670373458745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79521150018575560497944993 59640862513931670373458745)
  ·
    refine ⟨44730646885448752780094059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59640862513931670373458745 44730646885448752780094059)
    ·
      refine ⟨67095970328173129170141089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44730646885448752780094059 67095970328173129170141089)
      ·
        refine ⟨50321977746129846877605817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67095970328173129170141089 50321977746129846877605817)
        ·
          refine ⟨37741483309597385158204363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50321977746129846877605817 37741483309597385158204363)
          ·
            refine ⟨56612224964396077737306545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37741483309597385158204363 56612224964396077737306545)
            ·
              refine ⟨42459168723297058302979909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56612224964396077737306545 42459168723297058302979909)
              ·
                refine ⟨7961094135618198431808733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42459168723297058302979909 7961094135618198431808733)
                ·
                  refine ⟨2985410300856824411928275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7961094135618198431808733 2985410300856824411928275)
                  ·
                    refine ⟨4478115451285236617892413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985410300856824411928275 4478115451285236617892413)
                    ·
                      refine ⟨1679293294231963731709655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4478115451285236617892413 1679293294231963731709655)
                      ·
                        rfl

theorem cell23_3270412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3270412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270412 prefixEnd_3270412 := by exact prefixLift 3270412
  have htrace : WordTrace (prefixWord ++ tailWord_3270412) baseStart_3270412 baseEnd_3270412 := by
    simpa [prefixWord, tailWord_3270412, baseEnd_3270412] using wordTrace_append hprefix tailTrace_3270412
  have hstable : (prefixWord ++ tailWord_3270412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270412).length < 2 ^ (prefixWord ++ tailWord_3270412).sum := by decide
  have hdescent : baseEnd_3270412 < baseStart_3270412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270415 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 1, 5]
def baseStart_3270415 : Nat := 118140960795 + 3270415 * 2 ^ 59
def prefixEnd_3270415 : Nat := 4983230072969 + 3 ^ 40 * 3270415 * 2
def baseEnd_3270415 : Nat := 559764944891309073324047

theorem tailTrace_3270415 : CollatzResearch.WordTrace tailWord_3270415 prefixEnd_3270415 559764944891309073324047 := by
  unfold tailWord_3270415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119281834446852472259276699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79521222964568314839517799 119281834446852472259276699)
  ·
    refine ⟨178922751670278708388915049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119281834446852472259276699 178922751670278708388915049)
    ·
      refine ⟨134192063752709031291686287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178922751670278708388915049 134192063752709031291686287)
      ·
        refine ⟨201288095629063546937529431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134192063752709031291686287 201288095629063546937529431)
        ·
          refine ⟨301932143443595320406294147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201288095629063546937529431 301932143443595320406294147)
          ·
            refine ⟨452898215165392980609441221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301932143443595320406294147 452898215165392980609441221)
            ·
              refine ⟨84918415343511183864270229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452898215165392980609441221 84918415343511183864270229)
              ·
                refine ⟨3980550719227086743637667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84918415343511183864270229 3980550719227086743637667)
                ·
                  refine ⟨5970826078840630115456501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980550719227086743637667 5970826078840630115456501)
                  ·
                    refine ⟨559764944891309073324047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970826078840630115456501 559764944891309073324047)
                    ·
                      rfl

theorem cell23_3270415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_3270415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270415 prefixEnd_3270415 := by exact prefixLift 3270415
  have htrace : WordTrace (prefixWord ++ tailWord_3270415) baseStart_3270415 baseEnd_3270415 := by
    simpa [prefixWord, tailWord_3270415, baseEnd_3270415] using wordTrace_append hprefix tailTrace_3270415
  have hstable : (prefixWord ++ tailWord_3270415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270415).length < 2 ^ (prefixWord ++ tailWord_3270415).sum := by decide
  have hdescent : baseEnd_3270415 < baseStart_3270415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270462 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_3270462 : Nat := 118140960795 + 3270462 * 2 ^ 59
def prefixEnd_3270462 : Nat := 4983230072969 + 3 ^ 40 * 3270462 * 2
def baseEnd_3270462 : Nat := 559772989421562845361475

theorem tailTrace_3270462 : CollatzResearch.WordTrace tailWord_3270462 prefixEnd_3270462 559772989421562845361475 := by
  unfold tailWord_3270462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910443584710274910779705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79522365785121466190825093 14910443584710274910779705)
  ·
    refine ⟨11182832688532706183084779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14910443584710274910779705 11182832688532706183084779)
    ·
      refine ⟨16774249032799059274627169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11182832688532706183084779 16774249032799059274627169)
      ·
        refine ⟨12580686774599294455970377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16774249032799059274627169 12580686774599294455970377)
        ·
          refine ⟨9435515080949470841977783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12580686774599294455970377 9435515080949470841977783)
          ·
            refine ⟨14153272621424206262966675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435515080949470841977783 14153272621424206262966675)
            ·
              refine ⟨21229908932136309394450013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153272621424206262966675 21229908932136309394450013)
              ·
                refine ⟨7961215849551116022918755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21229908932136309394450013 7961215849551116022918755)
                ·
                  refine ⟨11941823774326674034378133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961215849551116022918755 11941823774326674034378133)
                  ·
                    refine ⟨559772989421562845361475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11941823774326674034378133 559772989421562845361475)
                    ·
                      rfl

theorem cell23_3270462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_3270462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270462 prefixEnd_3270462 := by exact prefixLift 3270462
  have htrace : WordTrace (prefixWord ++ tailWord_3270462) baseStart_3270462 baseEnd_3270462 := by
    simpa [prefixWord, tailWord_3270462, baseEnd_3270462] using wordTrace_append hprefix tailTrace_3270462
  have hstable : (prefixWord ++ tailWord_3270462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270462).length < 2 ^ (prefixWord ++ tailWord_3270462).sum := by decide
  have hdescent : baseEnd_3270462 < baseStart_3270462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270469 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_3270469 : Nat := 118140960795 + 3270469 * 2 ^ 59
def prefixEnd_3270469 : Nat := 4983230072969 + 3 ^ 40 * 3270469 * 2
def baseEnd_3270469 : Nat := 1679322562629270008696893

theorem tailTrace_3270469 : CollatzResearch.WordTrace tailWord_3270469 prefixEnd_3270469 1679322562629270008696893 := by
  unfold tailWord_3270469
  simp only [CollatzResearch.WordTrace]
  refine ⟨119283803988656839481742461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79522535992437892987828307 119283803988656839481742461)
  ·
    refine ⟨44731426495746314805653423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119283803988656839481742461 44731426495746314805653423)
    ·
      refine ⟨67097139743619472208480135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44731426495746314805653423 67097139743619472208480135)
      ·
        refine ⟨100645709615429208312720203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67097139743619472208480135 100645709615429208312720203)
        ·
          refine ⟨150968564423143812469080305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100645709615429208312720203 150968564423143812469080305)
          ·
            refine ⟨113226423317357859351810229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150968564423143812469080305 113226423317357859351810229)
            ·
              refine ⟨10614977186002299314232209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113226423317357859351810229 10614977186002299314232209)
              ·
                refine ⟨7961232889501724485674157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10614977186002299314232209 7961232889501724485674157)
                ·
                  refine ⟨2985462333563146682127809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7961232889501724485674157 2985462333563146682127809)
                  ·
                    refine ⟨2239096750172360011595857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985462333563146682127809 2239096750172360011595857)
                    ·
                      refine ⟨1679322562629270008696893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239096750172360011595857 1679322562629270008696893)
                      ·
                        rfl

theorem cell23_3270469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_3270469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270469 prefixEnd_3270469 := by exact prefixLift 3270469
  have htrace : WordTrace (prefixWord ++ tailWord_3270469) baseStart_3270469 baseEnd_3270469 := by
    simpa [prefixWord, tailWord_3270469, baseEnd_3270469] using wordTrace_append hprefix tailTrace_3270469
  have hstable : (prefixWord ++ tailWord_3270469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270469).length < 2 ^ (prefixWord ++ tailWord_3270469).sum := by decide
  have hdescent : baseEnd_3270469 < baseStart_3270469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270472 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3270472 : Nat := 118140960795 + 3270472 * 2 ^ 59
def prefixEnd_3270472 : Nat := 4983230072969 + 3 ^ 40 * 3270472 * 2
def baseEnd_3270472 : Nat := 1679324103071233496959379

theorem tailTrace_3270472 : CollatzResearch.WordTrace tailWord_3270472 prefixEnd_3270472 1679324103071233496959379 := by
  unfold tailWord_3270472
  simp only [CollatzResearch.WordTrace]
  refine ⟨59641956703822985497050835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79522608938430647329401113 59641956703822985497050835)
  ·
    refine ⟨89462935055734478245576253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59641956703822985497050835 89462935055734478245576253)
    ·
      refine ⟨33548600645900429342091095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89462935055734478245576253 33548600645900429342091095)
      ·
        refine ⟨50322900968850644013136643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33548600645900429342091095 50322900968850644013136643)
        ·
          refine ⟨75484351453275966019704965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50322900968850644013136643 75484351453275966019704965)
          ·
            refine ⟨14153315897489243628694681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75484351453275966019704965 14153315897489243628694681)
            ·
              refine ⟨10614986923116932721521011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153315897489243628694681 10614986923116932721521011)
              ·
                refine ⟨15922480384675399082281517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10614986923116932721521011 15922480384675399082281517)
                ·
                  refine ⟨5970930144253274655855569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15922480384675399082281517 5970930144253274655855569)
                  ·
                    refine ⟨4478197608189955991891677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5970930144253274655855569 4478197608189955991891677)
                    ·
                      refine ⟨1679324103071233496959379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4478197608189955991891677 1679324103071233496959379)
                      ·
                        rfl

theorem cell23_3270472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3270472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270472 prefixEnd_3270472 := by exact prefixLift 3270472
  have htrace : WordTrace (prefixWord ++ tailWord_3270472) baseStart_3270472 baseEnd_3270472 := by
    simpa [prefixWord, tailWord_3270472, baseEnd_3270472] using wordTrace_append hprefix tailTrace_3270472
  have hstable : (prefixWord ++ tailWord_3270472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270472).length < 2 ^ (prefixWord ++ tailWord_3270472).sum := by decide
  have hdescent : baseEnd_3270472 < baseStart_3270472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270482 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3270482 : Nat := 118140960795 + 3270482 * 2 ^ 59
def prefixEnd_3270482 : Nat := 4983230072969 + 3 ^ 40 * 3270482 * 2
def baseEnd_3270482 : Nat := 1679329237877778457834333

theorem tailTrace_3270482 : CollatzResearch.WordTrace tailWord_3270482 prefixEnd_3270482 1679329237877778457834333 := by
  unfold tailWord_3270482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29821069534402435675491425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79522852091739828467977133 29821069534402435675491425)
  ·
    refine ⟨22365802150801826756618569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29821069534402435675491425 22365802150801826756618569)
    ·
      refine ⟨16774351613101370067463927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22365802150801826756618569 16774351613101370067463927)
      ·
        refine ⟨25161527419652055101195891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16774351613101370067463927 25161527419652055101195891)
        ·
          refine ⟨37742291129478082651793837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25161527419652055101195891 37742291129478082651793837)
          ·
            refine ⟨14153359173554280994422689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37742291129478082651793837 14153359173554280994422689)
            ·
              refine ⟨10615019380165710745817017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14153359173554280994422689 10615019380165710745817017)
              ·
                refine ⟨7961264535124283059362763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10615019380165710745817017 7961264535124283059362763)
                ·
                  refine ⟨11941896802686424589044145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961264535124283059362763 11941896802686424589044145)
                  ·
                    refine ⟨8956422602014818441783109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11941896802686424589044145 8956422602014818441783109)
                    ·
                      refine ⟨1679329237877778457834333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8956422602014818441783109 1679329237877778457834333)
                      ·
                        rfl

theorem cell23_3270482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3270482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270482 prefixEnd_3270482 := by exact prefixLift 3270482
  have htrace : WordTrace (prefixWord ++ tailWord_3270482) baseStart_3270482 baseEnd_3270482 := by
    simpa [prefixWord, tailWord_3270482, baseEnd_3270482] using wordTrace_append hprefix tailTrace_3270482
  have hstable : (prefixWord ++ tailWord_3270482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270482).length < 2 ^ (prefixWord ++ tailWord_3270482).sum := by decide
  have hdescent : baseEnd_3270482 < baseStart_3270482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270492 : List Nat := [2, 2, 4, 2, 2, 1, 10]
def baseStart_3270492 : Nat := 118140960795 + 3270492 * 2 ^ 59
def prefixEnd_3270492 : Nat := 4983230072969 + 3 ^ 40 * 3270492 * 2
def baseEnd_3270492 : Nat := 20732523119559548379127

theorem tailTrace_3270492 : CollatzResearch.WordTrace tailWord_3270492 prefixEnd_3270492 20732523119559548379127 := by
  unfold tailWord_3270492
  simp only [CollatzResearch.WordTrace]
  refine ⟨59642321433786757204914865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79523095245049009606553153 59642321433786757204914865)
  ·
    refine ⟨44731741075340067903686149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59642321433786757204914865 44731741075340067903686149)
    ·
      refine ⟨8387201451626262731941153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44731741075340067903686149 8387201451626262731941153)
      ·
        refine ⟨6290401088719697048955865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8387201451626262731941153 6290401088719697048955865)
        ·
          refine ⟨4717800816539772786716899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290401088719697048955865 4717800816539772786716899)
          ·
            refine ⟨7076701224809659180075349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717800816539772786716899 7076701224809659180075349)
            ·
              refine ⟨20732523119559548379127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7076701224809659180075349 20732523119559548379127)
              ·
                rfl

theorem cell23_3270492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 10].length) (baseStart_3270492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270492 prefixEnd_3270492 := by exact prefixLift 3270492
  have htrace : WordTrace (prefixWord ++ tailWord_3270492) baseStart_3270492 baseEnd_3270492 := by
    simpa [prefixWord, tailWord_3270492, baseEnd_3270492] using wordTrace_append hprefix tailTrace_3270492
  have hstable : (prefixWord ++ tailWord_3270492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270492).length < 2 ^ (prefixWord ++ tailWord_3270492).sum := by decide
  have hdescent : baseEnd_3270492 < baseStart_3270492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270526 : List Nat := [4, 2, 3, 1, 1, 3, 2, 7]
def baseStart_3270526 : Nat := 118140960795 + 3270526 * 2 ^ 59
def prefixEnd_3270526 : Nat := 4983230072969 + 3 ^ 40 * 3270526 * 2
def baseEnd_3270526 : Nat := 62198215963947269840153

theorem tailTrace_3270526 : CollatzResearch.WordTrace tailWord_3270526 prefixEnd_3270526 62198215963947269840153 := by
  unfold tailWord_3270526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910735368681292277070929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79523921966300225477711621 14910735368681292277070929)
  ·
    refine ⟨11183051526510969207803197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14910735368681292277070929 11183051526510969207803197)
    ·
      refine ⟨4193644322441613452926199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11183051526510969207803197 4193644322441613452926199)
      ·
        refine ⟨6290466483662420179389299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193644322441613452926199 6290466483662420179389299)
        ·
          refine ⟨9435699725493630269083949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290466483662420179389299 9435699725493630269083949)
          ·
            refine ⟨3538387397060111350906481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9435699725493630269083949 3538387397060111350906481)
            ·
              refine ⟨2653790547795083513179861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538387397060111350906481 2653790547795083513179861)
              ·
                refine ⟨62198215963947269840153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2653790547795083513179861 62198215963947269840153)
                ·
                  rfl

theorem cell23_3270526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_3270526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270526 prefixEnd_3270526 := by exact prefixLift 3270526
  have htrace : WordTrace (prefixWord ++ tailWord_3270526) baseStart_3270526 baseEnd_3270526 := by
    simpa [prefixWord, tailWord_3270526, baseEnd_3270526] using wordTrace_append hprefix tailTrace_3270526
  have hstable : (prefixWord ++ tailWord_3270526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270526).length < 2 ^ (prefixWord ++ tailWord_3270526).sum := by decide
  have hdescent : baseEnd_3270526 < baseStart_3270526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270545 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3270545 : Nat := 118140960795 + 3270545 * 2 ^ 59
def prefixEnd_3270545 : Nat := 4983230072969 + 3 ^ 40 * 3270545 * 2
def baseEnd_3270545 : Nat := 1679361587159011711346543

theorem tailTrace_3270545 : CollatzResearch.WordTrace tailWord_3270545 prefixEnd_3270545 1679361587159011711346543 := by
  unfold tailWord_3270545
  simp only [CollatzResearch.WordTrace]
  refine ⟨119286575936381504461509089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79524383957587669641006059 119286575936381504461509089)
  ·
    refine ⟨89464931952286128346131817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119286575936381504461509089 89464931952286128346131817)
    ·
      refine ⟨67098698964214596259598863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89464931952286128346131817 67098698964214596259598863)
      ·
        refine ⟨100648048446321894389398295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67098698964214596259598863 100648048446321894389398295)
        ·
          refine ⟨150972072669482841584097443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100648048446321894389398295 150972072669482841584097443)
          ·
            refine ⟨226458109004224262376146165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150972072669482841584097443 226458109004224262376146165)
            ·
              refine ⟨21230447719146024597763703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226458109004224262376146165 21230447719146024597763703)
              ·
                refine ⟨31845671578719036896645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21230447719146024597763703 31845671578719036896645555)
                ·
                  refine ⟨47768507368078555344968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31845671578719036896645555 47768507368078555344968333)
                  ·
                    refine ⟨17913190263029458254363125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47768507368078555344968333 17913190263029458254363125)
                    ·
                      refine ⟨1679361587159011711346543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17913190263029458254363125 1679361587159011711346543)
                      ·
                        rfl

theorem cell23_3270545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3270545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270545 prefixEnd_3270545 := by exact prefixLift 3270545
  have htrace : WordTrace (prefixWord ++ tailWord_3270545) baseStart_3270545 baseEnd_3270545 := by
    simpa [prefixWord, tailWord_3270545, baseEnd_3270545] using wordTrace_append hprefix tailTrace_3270545
  have hstable : (prefixWord ++ tailWord_3270545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270545).length < 2 ^ (prefixWord ++ tailWord_3270545).sum := by decide
  have hdescent : baseEnd_3270545 < baseStart_3270545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270610 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3270610 : Nat := 118140960795 + 3270610 * 2 ^ 59
def prefixEnd_3270610 : Nat := 4983230072969 + 3 ^ 40 * 3270610 * 2
def baseEnd_3270610 : Nat := 1679394963401553957033745

theorem tailTrace_3270610 : CollatzResearch.WordTrace tailWord_3270610 prefixEnd_3270610 1679394963401553957033745 := by
  unfold tailWord_3270610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29822236670286505140656321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79525964454097347041750189 29822236670286505140656321)
  ·
    refine ⟨22366677502714878855492241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29822236670286505140656321 22366677502714878855492241)
    ·
      refine ⟨16775008127036159141619181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22366677502714878855492241 16775008127036159141619181)
      ·
        refine ⟨6290628047638559678107193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16775008127036159141619181 6290628047638559678107193)
        ·
          refine ⟨4717971035728919758580395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6290628047638559678107193 4717971035728919758580395)
          ·
            refine ⟨7076956553593379637870593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717971035728919758580395 7076956553593379637870593)
            ·
              refine ⟨5307717415195034728402945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7076956553593379637870593 5307717415195034728402945)
              ·
                refine ⟨3980788061396276046302209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5307717415195034728402945 3980788061396276046302209)
                ·
                  refine ⟨2985591046047207034726657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980788061396276046302209 2985591046047207034726657)
                  ·
                    refine ⟨2239193284535405276044993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985591046047207034726657 2239193284535405276044993)
                    ·
                      refine ⟨1679394963401553957033745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239193284535405276044993 1679394963401553957033745)
                      ·
                        rfl

theorem cell23_3270610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3270610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270610 prefixEnd_3270610 := by exact prefixLift 3270610
  have htrace : WordTrace (prefixWord ++ tailWord_3270610) baseStart_3270610 baseEnd_3270610 := by
    simpa [prefixWord, tailWord_3270610, baseEnd_3270610] using wordTrace_append hprefix tailTrace_3270610
  have hstable : (prefixWord ++ tailWord_3270610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270610).length < 2 ^ (prefixWord ++ tailWord_3270610).sum := by decide
  have hdescent : baseEnd_3270610 < baseStart_3270610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270632 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3270632 : Nat := 118140960795 + 3270632 * 2 ^ 59
def prefixEnd_3270632 : Nat := 4983230072969 + 3 ^ 40 * 3270632 * 2
def baseEnd_3270632 : Nat := 1679406259975952870958643

theorem tailTrace_3270632 : CollatzResearch.WordTrace tailWord_3270632 prefixEnd_3270632 1679406259975952870958643 := by
  unfold tailWord_3270632
  simp only [CollatzResearch.WordTrace]
  refine ⟨59644874543533159159963075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79526499391377545546617433 59644874543533159159963075)
  ·
    refine ⟨89467311815299738739944613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59644874543533159159963075 89467311815299738739944613)
    ·
      refine ⟨16775120965368701013739615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89467311815299738739944613 16775120965368701013739615)
      ·
        refine ⟨25162681448053051520609423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16775120965368701013739615 25162681448053051520609423)
        ·
          refine ⟨37744022172079577280914135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162681448053051520609423 37744022172079577280914135)
          ·
            refine ⟨56616033258119365921371203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37744022172079577280914135 56616033258119365921371203)
            ·
              refine ⟨84924049887179048882056805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56616033258119365921371203 84924049887179048882056805)
              ·
                refine ⟨15923259353846071665385651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84924049887179048882056805 15923259353846071665385651)
                ·
                  refine ⟨23884889030769107498078477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15923259353846071665385651 23884889030769107498078477)
                  ·
                    refine ⟨8956833386538415311779429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23884889030769107498078477 8956833386538415311779429)
                    ·
                      refine ⟨1679406259975952870958643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8956833386538415311779429 1679406259975952870958643)
                      ·
                        rfl

theorem cell23_3270632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3270632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270632 prefixEnd_3270632 := by exact prefixLift 3270632
  have htrace : WordTrace (prefixWord ++ tailWord_3270632) baseStart_3270632 baseEnd_3270632 := by
    simpa [prefixWord, tailWord_3270632, baseEnd_3270632] using wordTrace_append hprefix tailTrace_3270632
  have hstable : (prefixWord ++ tailWord_3270632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270632).length < 2 ^ (prefixWord ++ tailWord_3270632).sum := by decide
  have hdescent : baseEnd_3270632 < baseStart_3270632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270649 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3270649 : Nat := 118140960795 + 3270649 * 2 ^ 59
def prefixEnd_3270649 : Nat := 4983230072969 + 3 ^ 40 * 3270649 * 2
def baseEnd_3270649 : Nat := 1679414989147079304446065

theorem tailTrace_3270649 : CollatzResearch.WordTrace tailWord_3270649 prefixEnd_3270649 1679414989147079304446065 := by
  unfold tailWord_3270649
  simp only [CollatzResearch.WordTrace]
  refine ⟨119290369128004730223295001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79526912752003153482196667 119290369128004730223295001)
  ·
    refine ⟨89467776846003547667471251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119290369128004730223295001 89467776846003547667471251)
    ·
      refine ⟨134201665269005321501206877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89467776846003547667471251 134201665269005321501206877)
      ·
        refine ⟨50325624475876995562952579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134201665269005321501206877 50325624475876995562952579)
        ·
          refine ⟨75488436713815493344428869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50325624475876995562952579 75488436713815493344428869)
          ·
            refine ⟨14154081883840405002080413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75488436713815493344428869 14154081883840405002080413)
            ·
              refine ⟨5307780706440151875780155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14154081883840405002080413 5307780706440151875780155)
              ·
                refine ⟨7961671059660227813670233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5307780706440151875780155 7961671059660227813670233)
                ·
                  refine ⟨5971253294745170860252675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7961671059660227813670233 5971253294745170860252675)
                  ·
                    refine ⟨8956879942117756290379013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5971253294745170860252675 8956879942117756290379013)
                    ·
                      refine ⟨1679414989147079304446065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8956879942117756290379013 1679414989147079304446065)
                      ·
                        rfl

theorem cell23_3270649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3270649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270649 prefixEnd_3270649 := by exact prefixLift 3270649
  have htrace : WordTrace (prefixWord ++ tailWord_3270649) baseStart_3270649 baseEnd_3270649 := by
    simpa [prefixWord, tailWord_3270649, baseEnd_3270649] using wordTrace_append hprefix tailTrace_3270649
  have hstable : (prefixWord ++ tailWord_3270649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270649).length < 2 ^ (prefixWord ++ tailWord_3270649).sum := by decide
  have hdescent : baseEnd_3270649 < baseStart_3270649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270699 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 3]
def baseStart_3270699 : Nat := 118140960795 + 3270699 * 2 ^ 59
def prefixEnd_3270699 : Nat := 4983230072969 + 3 ^ 40 * 3270699 * 2
def baseEnd_3270699 : Nat := 1679440663179804108820835

theorem tailTrace_3270699 : CollatzResearch.WordTrace tailWord_3270699 prefixEnd_3270699 1679440663179804108820835 := by
  unfold tailWord_3270699
  simp only [CollatzResearch.WordTrace]
  refine ⟨119292192777823588762615151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79528128518549059175076767 119292192777823588762615151)
  ·
    refine ⟨178938289166735383143922727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119292192777823588762615151 178938289166735383143922727)
    ·
      refine ⟨268407433750103074715884091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178938289166735383143922727 268407433750103074715884091)
      ·
        refine ⟨402611150625154612073826137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268407433750103074715884091 402611150625154612073826137)
        ·
          refine ⟨301958362968865959055369603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402611150625154612073826137 301958362968865959055369603)
          ·
            refine ⟨452937544453298938583054405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301958362968865959055369603 452937544453298938583054405)
            ·
              refine ⟨84925789584993550984322701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452937544453298938583054405 84925789584993550984322701)
              ·
                refine ⟨31847171094372581619121013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84925789584993550984322701 31847171094372581619121013)
                ·
                  refine ⟨2985672290097429526792595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31847171094372581619121013 2985672290097429526792595)
                  ·
                    refine ⟨4478508435146144290188893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985672290097429526792595 4478508435146144290188893)
                    ·
                      refine ⟨1679440663179804108820835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4478508435146144290188893 1679440663179804108820835)
                      ·
                        rfl

theorem cell23_3270699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 3].length) (baseStart_3270699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270699 prefixEnd_3270699 := by exact prefixLift 3270699
  have htrace : WordTrace (prefixWord ++ tailWord_3270699) baseStart_3270699 baseEnd_3270699 := by
    simpa [prefixWord, tailWord_3270699, baseEnd_3270699] using wordTrace_append hprefix tailTrace_3270699
  have hstable : (prefixWord ++ tailWord_3270699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270699).length < 2 ^ (prefixWord ++ tailWord_3270699).sum := by decide
  have hdescent : baseEnd_3270699 < baseStart_3270699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270719 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 1, 5]
def baseStart_3270719 : Nat := 118140960795 + 3270719 * 2 ^ 59
def prefixEnd_3270719 : Nat := 4983230072969 + 3 ^ 40 * 3270719 * 2
def baseEnd_3270719 : Nat := 559816977597631343523581

theorem tailTrace_3270719 : CollatzResearch.WordTrace tailWord_3270719 prefixEnd_3270719 559816977597631343523581 := by
  unfold tailWord_3270719
  simp only [CollatzResearch.WordTrace]
  refine ⟨119292922237751132178343211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79528614825167421452228807 119292922237751132178343211)
  ·
    refine ⟨178939383356626698267514817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119292922237751132178343211 178939383356626698267514817)
    ·
      refine ⟨134204537517470023700636113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178939383356626698267514817 134204537517470023700636113)
      ·
        refine ⟨100653403138102517775477085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134204537517470023700636113 100653403138102517775477085)
        ·
          refine ⟨37745026176788444165803907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100653403138102517775477085 37745026176788444165803907)
          ·
            refine ⟨56617539265182666248705861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37745026176788444165803907 56617539265182666248705861)
            ·
              refine ⟨10615788612221749921632349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56617539265182666248705861 10615788612221749921632349)
              ·
                refine ⟨3980920729583156220612131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10615788612221749921632349 3980920729583156220612131)
                ·
                  refine ⟨5971381094374734330918197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980920729583156220612131 5971381094374734330918197)
                  ·
                    refine ⟨559816977597631343523581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5971381094374734330918197 559816977597631343523581)
                    ·
                      rfl

theorem cell23_3270719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_3270719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270719 prefixEnd_3270719 := by exact prefixLift 3270719
  have htrace : WordTrace (prefixWord ++ tailWord_3270719) baseStart_3270719 baseEnd_3270719 := by
    simpa [prefixWord, tailWord_3270719, baseEnd_3270719] using wordTrace_append hprefix tailTrace_3270719
  have hstable : (prefixWord ++ tailWord_3270719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270719).length < 2 ^ (prefixWord ++ tailWord_3270719).sum := by decide
  have hdescent : baseEnd_3270719 < baseStart_3270719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270756 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_3270756 : Nat := 118140960795 + 3270756 * 2 ^ 59
def prefixEnd_3270756 : Nat := 4983230072969 + 3 ^ 40 * 3270756 * 2
def baseEnd_3270756 : Nat := 1679469931577110385808073

theorem tailTrace_3270756 : CollatzResearch.WordTrace tailWord_3270756 prefixEnd_3270756 1679469931577110385808073 := by
  unfold tailWord_3270756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59647135869308543748720061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79529514492411391664960081 59647135869308543748720061)
  ·
    refine ⟨22367675950990703905770023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59647135869308543748720061 22367675950990703905770023)
    ·
      refine ⟨33551513926486055858655035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22367675950990703905770023 33551513926486055858655035)
      ·
        refine ⟨50327270889729083787982553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33551513926486055858655035 50327270889729083787982553)
        ·
          refine ⟨37745453167296812840986915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50327270889729083787982553 37745453167296812840986915)
          ·
            refine ⟨56618179750945219261480373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37745453167296812840986915 56618179750945219261480373)
            ·
              refine ⟨5307954351651114305763785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56618179750945219261480373 5307954351651114305763785)
              ·
                refine ⟨3980965763738335729322839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5307954351651114305763785 3980965763738335729322839)
                ·
                  refine ⟨5971448645607503593984259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980965763738335729322839 5971448645607503593984259)
                  ·
                    refine ⟨8957172968411255390976389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5971448645607503593984259 8957172968411255390976389)
                    ·
                      refine ⟨1679469931577110385808073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8957172968411255390976389 1679469931577110385808073)
                      ·
                        rfl

theorem cell23_3270756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_3270756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270756 prefixEnd_3270756 := by exact prefixLift 3270756
  have htrace : WordTrace (prefixWord ++ tailWord_3270756) baseStart_3270756 baseEnd_3270756 := by
    simpa [prefixWord, tailWord_3270756, baseEnd_3270756] using wordTrace_append hprefix tailTrace_3270756
  have hstable : (prefixWord ++ tailWord_3270756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270756).length < 2 ^ (prefixWord ++ tailWord_3270756).sum := by decide
  have hdescent : baseEnd_3270756 < baseStart_3270756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270769 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3270769 : Nat := 118140960795 + 3270769 * 2 ^ 59
def prefixEnd_3270769 : Nat := 4983230072969 + 3 ^ 40 * 3270769 * 2
def baseEnd_3270769 : Nat := 1679476606825618834945513

theorem tailTrace_3270769 : CollatzResearch.WordTrace tailWord_3270769 prefixEnd_3270769 1679476606825618834945513 := by
  unfold tailWord_3270769
  simp only [CollatzResearch.WordTrace]
  refine ⟨119294745887569990717663361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79529830591713327145108907 119294745887569990717663361)
  ·
    refine ⟨89471059415677493038247521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119294745887569990717663361 89471059415677493038247521)
    ·
      refine ⟨67103294561758119778685641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89471059415677493038247521 67103294561758119778685641)
      ·
        refine ⟨50327470921318589834014231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67103294561758119778685641 50327470921318589834014231)
        ·
          refine ⟨75491206381977884751021347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50327470921318589834014231 75491206381977884751021347)
          ·
            refine ⟨113236809572966827126532021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75491206381977884751021347 113236809572966827126532021)
            ·
              refine ⟨10615950897465640043112377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113236809572966827126532021 10615950897465640043112377)
              ·
                refine ⟨7961963173099230032334283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10615950897465640043112377 7961963173099230032334283)
                ·
                  refine ⟨11942944759648845048501425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7961963173099230032334283 11942944759648845048501425)
                  ·
                    refine ⟨8957208569736633786376069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11942944759648845048501425 8957208569736633786376069)
                    ·
                      refine ⟨1679476606825618834945513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8957208569736633786376069 1679476606825618834945513)
                      ·
                        rfl

theorem cell23_3270769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3270769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270769 prefixEnd_3270769 := by exact prefixLift 3270769
  have htrace : WordTrace (prefixWord ++ tailWord_3270769) baseStart_3270769 baseEnd_3270769 := by
    simpa [prefixWord, tailWord_3270769, baseEnd_3270769] using wordTrace_append hprefix tailTrace_3270769
  have hstable : (prefixWord ++ tailWord_3270769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270769).length < 2 ^ (prefixWord ++ tailWord_3270769).sum := by decide
  have hdescent : baseEnd_3270769 < baseStart_3270769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270839 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 6]
def baseStart_3270839 : Nat := 118140960795 + 3270839 * 2 ^ 59
def prefixEnd_3270839 : Nat := 4983230072969 + 3 ^ 40 * 3270839 * 2
def baseEnd_3270839 : Nat := 559837516823811187023397

theorem tailTrace_3270839 : CollatzResearch.WordTrace tailWord_3270839 prefixEnd_3270839 559837516823811187023397 := by
  unfold tailWord_3270839
  simp only [CollatzResearch.WordTrace]
  refine ⟨119297298997316392672711571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79531532664877595115141047 119297298997316392672711571)
  ·
    refine ⟨178945948495974589009067357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119297298997316392672711571 178945948495974589009067357)
    ·
      refine ⟨67104730685990470878400259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178945948495974589009067357 67104730685990470878400259)
      ·
        refine ⟨100657096028985706317600389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67104730685990470878400259 100657096028985706317600389)
        ·
          refine ⟨18873205505434819934550073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100657096028985706317600389 18873205505434819934550073)
          ·
            refine ⟨14154904129076114950912555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18873205505434819934550073 14154904129076114950912555)
            ·
              refine ⟨21232356193614172426368833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14154904129076114950912555 21232356193614172426368833)
              ·
                refine ⟨15924267145210629319776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21232356193614172426368833 15924267145210629319776625)
                ·
                  refine ⟨11943200358907971989832469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15924267145210629319776625 11943200358907971989832469)
                  ·
                    refine ⟨559837516823811187023397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11943200358907971989832469 559837516823811187023397)
                    ·
                      rfl

theorem cell23_3270839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_3270839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270839 prefixEnd_3270839 := by exact prefixLift 3270839
  have htrace : WordTrace (prefixWord ++ tailWord_3270839) baseStart_3270839 baseEnd_3270839 := by
    simpa [prefixWord, tailWord_3270839, baseEnd_3270839] using wordTrace_append hprefix tailTrace_3270839
  have hstable : (prefixWord ++ tailWord_3270839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270839).length < 2 ^ (prefixWord ++ tailWord_3270839).sum := by decide
  have hdescent : baseEnd_3270839 < baseStart_3270839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270859 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_3270859 : Nat := 118140960795 + 3270859 * 2 ^ 59
def prefixEnd_3270859 : Nat := 4983230072969 + 3 ^ 40 * 3270859 * 2
def baseEnd_3270859 : Nat := 1679522820084523482820099

theorem tailTrace_3270859 : CollatzResearch.WordTrace tailWord_3270859 prefixEnd_3270859 1679522820084523482820099 := by
  unfold tailWord_3270859
  simp only [CollatzResearch.WordTrace]
  refine ⟨119298028457243936088439631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79532018971495957392293087 119298028457243936088439631)
  ·
    refine ⟨178947042685865904132659447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119298028457243936088439631 178947042685865904132659447)
    ·
      refine ⟨268420564028798856198989171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178947042685865904132659447 268420564028798856198989171)
      ·
        refine ⟨402630846043198284298483757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268420564028798856198989171 402630846043198284298483757)
        ·
          refine ⟨150986567266199356611931409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402630846043198284298483757 150986567266199356611931409)
          ·
            refine ⟨113239925449649517458948557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150986567266199356611931409 113239925449649517458948557)
            ·
              refine ⟨42464972043618569047105709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113239925449649517458948557 42464972043618569047105709)
              ·
                refine ⟨15924364516356963392664641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42464972043618569047105709 15924364516356963392664641)
                ·
                  refine ⟨11943273387267722544498481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15924364516356963392664641 11943273387267722544498481)
                  ·
                    refine ⟨8957455040450791908373861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11943273387267722544498481 8957455040450791908373861)
                    ·
                      refine ⟨1679522820084523482820099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8957455040450791908373861 1679522820084523482820099)
                      ·
                        rfl

theorem cell23_3270859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_3270859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270859 prefixEnd_3270859 := by exact prefixLift 3270859
  have htrace : WordTrace (prefixWord ++ tailWord_3270859) baseStart_3270859 baseEnd_3270859 := by
    simpa [prefixWord, tailWord_3270859, baseEnd_3270859] using wordTrace_append hprefix tailTrace_3270859
  have hstable : (prefixWord ++ tailWord_3270859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270859).length < 2 ^ (prefixWord ++ tailWord_3270859).sum := by decide
  have hdescent : baseEnd_3270859 < baseStart_3270859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270883 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3270883 : Nat := 118140960795 + 3270883 * 2 ^ 59
def prefixEnd_3270883 : Nat := 4983230072969 + 3 ^ 40 * 3270883 * 2
def baseEnd_3270883 : Nat := 1679535143620231388919989

theorem tailTrace_3270883 : CollatzResearch.WordTrace tailWord_3270883 prefixEnd_3270883 1679535143620231388919989 := by
  unfold tailWord_3270883
  simp only [CollatzResearch.WordTrace]
  refine ⟨119298903809156988187313303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79532602539437992124875535 119298903809156988187313303)
  ·
    refine ⟨178948355713735482280969955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119298903809156988187313303 178948355713735482280969955)
    ·
      refine ⟨268422533570603223421454933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178948355713735482280969955 268422533570603223421454933)
      ·
        refine ⟨3145576565280506524470175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 268422533570603223421454933 3145576565280506524470175)
        ·
          refine ⟨4718364847920759786705263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145576565280506524470175 4718364847920759786705263)
          ·
            refine ⟨7077547271881139680057895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718364847920759786705263 7077547271881139680057895)
            ·
              refine ⟨10616320907821709520086843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077547271881139680057895 10616320907821709520086843)
              ·
                refine ⟨15924481361732564280130265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10616320907821709520086843 15924481361732564280130265)
                ·
                  refine ⟨11943361021299423210097699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15924481361732564280130265 11943361021299423210097699)
                  ·
                    refine ⟨17915041531949134815146549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11943361021299423210097699 17915041531949134815146549)
                    ·
                      refine ⟨1679535143620231388919989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17915041531949134815146549 1679535143620231388919989)
                      ·
                        rfl

theorem cell23_3270883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3270883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270883 prefixEnd_3270883 := by exact prefixLift 3270883
  have htrace : WordTrace (prefixWord ++ tailWord_3270883) baseStart_3270883 baseEnd_3270883 := by
    simpa [prefixWord, tailWord_3270883, baseEnd_3270883] using wordTrace_append hprefix tailTrace_3270883
  have hstable : (prefixWord ++ tailWord_3270883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270883).length < 2 ^ (prefixWord ++ tailWord_3270883).sum := by decide
  have hdescent : baseEnd_3270883 < baseStart_3270883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270914 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3270914 : Nat := 118140960795 + 3270914 * 2 ^ 59
def prefixEnd_3270914 : Nat := 4983230072969 + 3 ^ 40 * 3270914 * 2
def baseEnd_3270914 : Nat := 1679551061520520767632347

theorem tailTrace_3270914 : CollatzResearch.WordTrace tailWord_3270914 prefixEnd_3270914 1679551061520520767632347 := by
  unfold tailWord_3270914
  simp only [CollatzResearch.WordTrace]
  refine ⟨29825008618011170120422949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79533356314696453654461197 29825008618011170120422949)
  ·
    refine ⟨5592189115877094397579303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29825008618011170120422949 5592189115877094397579303)
    ·
      refine ⟨8388283673815641596368955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592189115877094397579303 8388283673815641596368955)
      ·
        refine ⟨12582425510723462394553433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388283673815641596368955 12582425510723462394553433)
        ·
          refine ⟨9436819133042596795915075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12582425510723462394553433 9436819133042596795915075)
          ·
            refine ⟨14155228699563895193872613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9436819133042596795915075 14155228699563895193872613)
            ·
              refine ⟨2654105381168230348851115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14155228699563895193872613 2654105381168230348851115)
              ·
                refine ⟨3981158071752345523276673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654105381168230348851115 3981158071752345523276673)
                ·
                  refine ⟨2985868553814259142457505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3981158071752345523276673 2985868553814259142457505)
                  ·
                    refine ⟨2239401415360694356843129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2985868553814259142457505 2239401415360694356843129)
                    ·
                      refine ⟨1679551061520520767632347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239401415360694356843129 1679551061520520767632347)
                      ·
                        rfl

theorem cell23_3270914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3270914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270914 prefixEnd_3270914 := by exact prefixLift 3270914
  have htrace : WordTrace (prefixWord ++ tailWord_3270914) baseStart_3270914 baseEnd_3270914 := by
    simpa [prefixWord, tailWord_3270914, baseEnd_3270914] using wordTrace_append hprefix tailTrace_3270914
  have hstable : (prefixWord ++ tailWord_3270914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270914).length < 2 ^ (prefixWord ++ tailWord_3270914).sum := by decide
  have hdescent : baseEnd_3270914 < baseStart_3270914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270954 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_3270954 : Nat := 118140960795 + 3270954 * 2 ^ 59
def prefixEnd_3270954 : Nat := 4983230072969 + 3 ^ 40 * 3270954 * 2
def baseEnd_3270954 : Nat := 186619066749633401236907

theorem tailTrace_3270954 : CollatzResearch.WordTrace tailWord_3270954 prefixEnd_3270954 186619066749633401236907 := by
  unfold tailWord_3270954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29825373347974941828286979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79534328927933178208765277 29825373347974941828286979)
  ·
    refine ⟨44738060021962412742430469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29825373347974941828286979 44738060021962412742430469)
    ·
      refine ⟨8388386254117952389205713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44738060021962412742430469 8388386254117952389205713)
      ·
        refine ⟨6291289690588464291904285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8388386254117952389205713 6291289690588464291904285)
        ·
          refine ⟨2359233633970674109464107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6291289690588464291904285 2359233633970674109464107)
          ·
            refine ⟨3538850450956011164196161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359233633970674109464107 3538850450956011164196161)
            ·
              refine ⟨2654137838217008373147121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538850450956011164196161 2654137838217008373147121)
              ·
                refine ⟨1990603378662756279860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654137838217008373147121 1990603378662756279860341)
                ·
                  refine ⟨186619066749633401236907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1990603378662756279860341 186619066749633401236907)
                  ·
                    rfl

theorem cell23_3270954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_3270954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270954 prefixEnd_3270954 := by exact prefixLift 3270954
  have htrace : WordTrace (prefixWord ++ tailWord_3270954) baseStart_3270954 baseEnd_3270954 := by
    simpa [prefixWord, tailWord_3270954, baseEnd_3270954] using wordTrace_append hprefix tailTrace_3270954
  have hstable : (prefixWord ++ tailWord_3270954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270954).length < 2 ^ (prefixWord ++ tailWord_3270954).sum := by decide
  have hdescent : baseEnd_3270954 < baseStart_3270954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270959 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 8]
def baseStart_3270959 : Nat := 118140960795 + 3270959 * 2 ^ 59
def prefixEnd_3270959 : Nat := 4983230072969 + 3 ^ 40 * 3270959 * 2
def baseEnd_3270959 : Nat := 186619352016663676841071

theorem tailTrace_3270959 : CollatzResearch.WordTrace tailWord_3270959 prefixEnd_3270959 186619352016663676841071 := by
  unfold tailWord_3270959
  simp only [CollatzResearch.WordTrace]
  refine ⟨119301675756881653167079931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79534450504587768778053287 119301675756881653167079931)
  ·
    refine ⟨178952513635322479750619897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119301675756881653167079931 178952513635322479750619897)
    ·
      refine ⟨134214385226491859812964923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178952513635322479750619897 134214385226491859812964923)
      ·
        refine ⟨201321577839737789719447385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134214385226491859812964923 201321577839737789719447385)
        ·
          refine ⟨150991183379803342289585539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201321577839737789719447385 150991183379803342289585539)
          ·
            refine ⟨226486775069705013434378309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150991183379803342289585539 226486775069705013434378309)
            ·
              refine ⟨42466270325569690018945933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226486775069705013434378309 42466270325569690018945933)
              ·
                refine ⟨15924851372088633757104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42466270325569690018945933 15924851372088633757104725)
                ·
                  refine ⟨186619352016663676841071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15924851372088633757104725 186619352016663676841071)
                  ·
                    rfl

theorem cell23_3270959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 8].length) (baseStart_3270959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270959 prefixEnd_3270959 := by exact prefixLift 3270959
  have htrace : WordTrace (prefixWord ++ tailWord_3270959) baseStart_3270959 baseEnd_3270959 := by
    simpa [prefixWord, tailWord_3270959, baseEnd_3270959] using wordTrace_append hprefix tailTrace_3270959
  have hstable : (prefixWord ++ tailWord_3270959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270959).length < 2 ^ (prefixWord ++ tailWord_3270959).sum := by decide
  have hdescent : baseEnd_3270959 < baseStart_3270959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270997 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3270997 : Nat := 118140960795 + 3270997 * 2 ^ 59
def prefixEnd_3270997 : Nat := 4983230072969 + 3 ^ 40 * 3270997 * 2
def baseEnd_3270997 : Nat := 559864560138281314298155

theorem tailTrace_3270997 : CollatzResearch.WordTrace tailWord_3270997 prefixEnd_3270997 559864560138281314298155 := by
  unfold tailWord_3270997
  simp only [CollatzResearch.WordTrace]
  refine ⟨119303061730743985656963245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79535374487162657104642163 119303061730743985656963245)
  ·
    refine ⟨44738648149028994621361217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119303061730743985656963245 44738648149028994621361217)
    ·
      refine ⟨33553986111771745966020913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44738648149028994621361217 33553986111771745966020913)
      ·
        refine ⟨25165489583828809474515685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33553986111771745966020913 25165489583828809474515685)
        ·
          refine ⟨4718529296967901776471691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25165489583828809474515685 4718529296967901776471691)
          ·
            refine ⟨7077793945451852664707537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718529296967901776471691 7077793945451852664707537)
            ·
              refine ⟨5308345459088889498530653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7077793945451852664707537 5308345459088889498530653)
              ·
                refine ⟨1990629547158333561948995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308345459088889498530653 1990629547158333561948995)
                ·
                  refine ⟨2985944320737500342923493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990629547158333561948995 2985944320737500342923493)
                  ·
                    refine ⟨559864560138281314298155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985944320737500342923493 559864560138281314298155)
                    ·
                      rfl

theorem cell23_3270997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3270997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3270997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3270997 prefixEnd_3270997 := by exact prefixLift 3270997
  have htrace : WordTrace (prefixWord ++ tailWord_3270997) baseStart_3270997 baseEnd_3270997 := by
    simpa [prefixWord, tailWord_3270997, baseEnd_3270997] using wordTrace_append hprefix tailTrace_3270997
  have hstable : (prefixWord ++ tailWord_3270997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270997).length < 2 ^ (prefixWord ++ tailWord_3270997).sum := by decide
  have hdescent : baseEnd_3270997 < baseStart_3270997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271010 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_3271010 : Nat := 118140960795 + 3271010 * 2 ^ 59
def prefixEnd_3271010 : Nat := 4983230072969 + 3 ^ 40 * 3271010 * 2
def baseEnd_3271010 : Nat := 186622261740372488003545

theorem tailTrace_3271010 : CollatzResearch.WordTrace tailWord_3271010 prefixEnd_3271010 186622261740372488003545 := by
  unfold tailWord_3271010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29825883969924222219296621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79535690586464592584790989 29825883969924222219296621)
  ·
    refine ⟨11184706488721583332236233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29825883969924222219296621 11184706488721583332236233)
    ·
      refine ⟨8388529866541187499177175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11184706488721583332236233 8388529866541187499177175)
      ·
        refine ⟨12582794799811781248765763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388529866541187499177175 12582794799811781248765763)
        ·
          refine ⟨18874192199717671873148645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582794799811781248765763 18874192199717671873148645)
          ·
            refine ⟨3538911037447063476215371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18874192199717671873148645 3538911037447063476215371)
            ·
              refine ⟨5308366556170595214323057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538911037447063476215371 5308366556170595214323057)
              ·
                refine ⟨3981274917127946410742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308366556170595214323057 3981274917127946410742293)
                ·
                  refine ⟨186622261740372488003545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3981274917127946410742293 186622261740372488003545)
                  ·
                    rfl

theorem cell23_3271010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_3271010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271010 prefixEnd_3271010 := by exact prefixLift 3271010
  have htrace : WordTrace (prefixWord ++ tailWord_3271010) baseStart_3271010 baseEnd_3271010 := by
    simpa [prefixWord, tailWord_3271010, baseEnd_3271010] using wordTrace_append hprefix tailTrace_3271010
  have hstable : (prefixWord ++ tailWord_3271010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271010).length < 2 ^ (prefixWord ++ tailWord_3271010).sum := by decide
  have hdescent : baseEnd_3271010 < baseStart_3271010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271036 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3271036 : Nat := 118140960795 + 3271036 * 2 ^ 59
def prefixEnd_3271036 : Nat := 4983230072969 + 3 ^ 40 * 3271036 * 2
def baseEnd_3271036 : Nat := 559871235386789763435595

theorem tailTrace_3271036 : CollatzResearch.WordTrace tailWord_3271036 prefixEnd_3271036 559871235386789763435595 := by
  unfold tailWord_3271036
  simp only [CollatzResearch.WordTrace]
  refine ⟨59652242088801347658816481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79536322785068463545088641 59652242088801347658816481)
  ·
    refine ⟨44739181566601010744112361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59652242088801347658816481 44739181566601010744112361)
    ·
      refine ⟨33554386174950758058084271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44739181566601010744112361 33554386174950758058084271)
      ·
        refine ⟨50331579262426137087126407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33554386174950758058084271 50331579262426137087126407)
        ·
          refine ⟨75497368893639205630689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50331579262426137087126407 75497368893639205630689611)
          ·
            refine ⟨113246053340458808446034417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75497368893639205630689611 113246053340458808446034417)
            ·
              refine ⟨84934540005344106334525813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113246053340458808446034417 84934540005344106334525813)
              ·
                refine ⟨7962613125501009968861795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84934540005344106334525813 7962613125501009968861795)
                ·
                  refine ⟨11943919688251514953292693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962613125501009968861795 11943919688251514953292693)
                  ·
                    refine ⟨559871235386789763435595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11943919688251514953292693 559871235386789763435595)
                    ·
                      rfl

theorem cell23_3271036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3271036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271036 prefixEnd_3271036 := by exact prefixLift 3271036
  have htrace : WordTrace (prefixWord ++ tailWord_3271036) baseStart_3271036 baseEnd_3271036 := by
    simpa [prefixWord, tailWord_3271036, baseEnd_3271036] using wordTrace_append hprefix tailTrace_3271036
  have hstable : (prefixWord ++ tailWord_3271036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271036).length < 2 ^ (prefixWord ++ tailWord_3271036).sum := by decide
  have hdescent : baseEnd_3271036 < baseStart_3271036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271054 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3271054 : Nat := 118140960795 + 3271054 * 2 ^ 59
def prefixEnd_3271054 : Nat := 4983230072969 + 3 ^ 40 * 3271054 * 2
def baseEnd_3271054 : Nat := 1679622948812150219881703

theorem tailTrace_3271054 : CollatzResearch.WordTrace tailWord_3271054 prefixEnd_3271054 1679622948812150219881703 := by
  unfold tailWord_3271054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913142586442185548973527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79536760461024989594525477 14913142586442185548973527)
  ·
    refine ⟨22369713879663278323460291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913142586442185548973527 22369713879663278323460291)
    ·
      refine ⟨33554570819494917485190437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22369713879663278323460291 33554570819494917485190437)
      ·
        refine ⟨6291482028655297028473207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33554570819494917485190437 6291482028655297028473207)
        ·
          refine ⟨9437223042982945542709811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6291482028655297028473207 9437223042982945542709811)
          ·
            refine ⟨14155834564474418314064717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437223042982945542709811 14155834564474418314064717)
            ·
              refine ⟨5308437961677906867774269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14155834564474418314064717 5308437961677906867774269)
              ·
                refine ⟨1990664235629215075415351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308437961677906867774269 1990664235629215075415351)
                ·
                  refine ⟨2985996353443822613123027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990664235629215075415351 2985996353443822613123027)
                  ·
                    refine ⟨4478994530165733919684541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2985996353443822613123027 4478994530165733919684541)
                    ·
                      refine ⟨1679622948812150219881703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4478994530165733919684541 1679622948812150219881703)
                      ·
                        rfl

theorem cell23_3271054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3271054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271054 prefixEnd_3271054 := by exact prefixLift 3271054
  have htrace : WordTrace (prefixWord ++ tailWord_3271054) baseStart_3271054 baseEnd_3271054 := by
    simpa [prefixWord, tailWord_3271054, baseEnd_3271054] using wordTrace_append hprefix tailTrace_3271054
  have hstable : (prefixWord ++ tailWord_3271054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271054).length < 2 ^ (prefixWord ++ tailWord_3271054).sum := by decide
  have hdescent : baseEnd_3271054 < baseStart_3271054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271066 : List Nat := [3, 1, 1, 4, 1, 2, 11]
def baseStart_3271066 : Nat := 118140960795 + 3271066 * 2 ^ 59
def prefixEnd_3271066 : Nat := 4983230072969 + 3 ^ 40 * 3271066 * 2
def baseEnd_3271066 : Nat := 20736161859012397196687

theorem tailTrace_3271066 : CollatzResearch.WordTrace tailWord_3271066 prefixEnd_3271066 20736161859012397196687 := by
  unfold tailWord_3271066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29826394591873502610306263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79537052244996006960816701 29826394591873502610306263)
  ·
    refine ⟨44739591887810253915459395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29826394591873502610306263 44739591887810253915459395)
    ·
      refine ⟨67109387831715380873189093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44739591887810253915459395 67109387831715380873189093)
      ·
        refine ⟨12583010218446633913722955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67109387831715380873189093 12583010218446633913722955)
        ·
          refine ⟨18874515327669950870584433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583010218446633913722955 18874515327669950870584433)
          ·
            refine ⟨14155886495752463152938325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18874515327669950870584433 14155886495752463152938325)
            ·
              refine ⟨20736161859012397196687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14155886495752463152938325 20736161859012397196687)
              ·
                rfl

theorem cell23_3271066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 11].length) (baseStart_3271066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271066 prefixEnd_3271066 := by exact prefixLift 3271066
  have htrace : WordTrace (prefixWord ++ tailWord_3271066) baseStart_3271066 baseEnd_3271066 := by
    simpa [prefixWord, tailWord_3271066, baseEnd_3271066] using wordTrace_append hprefix tailTrace_3271066
  have hstable : (prefixWord ++ tailWord_3271066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271066).length < 2 ^ (prefixWord ++ tailWord_3271066).sum := by decide
  have hdescent : baseEnd_3271066 < baseStart_3271066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271080 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3271080 : Nat := 118140960795 + 3271080 * 2 ^ 59
def prefixEnd_3271080 : Nat := 4983230072969 + 3 ^ 40 * 3271080 * 2
def baseEnd_3271080 : Nat := 1679636299309167118156583

theorem tailTrace_3271080 : CollatzResearch.WordTrace tailWord_3271080 prefixEnd_3271080 1679636299309167118156583 := by
  unfold tailWord_3271080
  simp only [CollatzResearch.WordTrace]
  refine ⟨59653044494721645416117347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79537392659628860554823129 59653044494721645416117347)
  ·
    refine ⟨89479566742082468124176021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59653044494721645416117347 89479566742082468124176021)
    ·
      refine ⟨4194354691035115693320751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89479566742082468124176021 4194354691035115693320751)
      ·
        refine ⟨6291532036552673539981127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194354691035115693320751 6291532036552673539981127)
        ·
          refine ⟨9437298054829010309971691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6291532036552673539981127 9437298054829010309971691)
          ·
            refine ⟨14155947082243515464957537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437298054829010309971691 14155947082243515464957537)
            ·
              refine ⟨10616960311682636598718153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14155947082243515464957537 10616960311682636598718153)
              ·
                refine ⟨7962720233761977449038615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10616960311682636598718153 7962720233761977449038615)
                ·
                  refine ⟨11944080350642966173557923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7962720233761977449038615 11944080350642966173557923)
                  ·
                    refine ⟨17916120525964449260336885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11944080350642966173557923 17916120525964449260336885)
                    ·
                      refine ⟨1679636299309167118156583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17916120525964449260336885 1679636299309167118156583)
                      ·
                        rfl

theorem cell23_3271080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3271080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271080 prefixEnd_3271080 := by exact prefixLift 3271080
  have htrace : WordTrace (prefixWord ++ tailWord_3271080) baseStart_3271080 baseEnd_3271080 := by
    simpa [prefixWord, tailWord_3271080, baseEnd_3271080] using wordTrace_append hprefix tailTrace_3271080
  have hstable : (prefixWord ++ tailWord_3271080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271080).length < 2 ^ (prefixWord ++ tailWord_3271080).sum := by decide
  have hdescent : baseEnd_3271080 < baseStart_3271080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271097 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3271097 : Nat := 118140960795 + 3271097 * 2 ^ 59
def prefixEnd_3271097 : Nat := 4983230072969 + 3 ^ 40 * 3271097 * 2
def baseEnd_3271097 : Nat := 1679645028480293551644005

theorem tailTrace_3271097 : CollatzResearch.WordTrace tailWord_3271097 prefixEnd_3271097 1679645028480293551644005 := by
  unfold tailWord_3271097
  simp only [CollatzResearch.WordTrace]
  refine ⟨119306709030381702735603545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79537806020254468490402363 119306709030381702735603545)
  ·
    refine ⟨89480031772786277051702659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119306709030381702735603545 89480031772786277051702659)
    ·
      refine ⟨134220047659179415577553989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89480031772786277051702659 134220047659179415577553989)
      ·
        refine ⟨25166258936096140420791373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134220047659179415577553989 25166258936096140420791373)
        ·
          refine ⟨9437347101036052657796765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25166258936096140420791373 9437347101036052657796765)
          ·
            refine ⟨3539005162888519746673787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9437347101036052657796765 3539005162888519746673787)
            ·
              refine ⟨5308507744332779620010681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539005162888519746673787 5308507744332779620010681)
              ·
                refine ⟨3981380808249584715008011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308507744332779620010681 3981380808249584715008011)
                ·
                  refine ⟨5972071212374377072512017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981380808249584715008011 5972071212374377072512017)
                  ·
                    refine ⟨4479053409280782804384013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972071212374377072512017 4479053409280782804384013)
                    ·
                      refine ⟨1679645028480293551644005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479053409280782804384013 1679645028480293551644005)
                      ·
                        rfl

theorem cell23_3271097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3271097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271097 prefixEnd_3271097 := by exact prefixLift 3271097
  have htrace : WordTrace (prefixWord ++ tailWord_3271097) baseStart_3271097 baseEnd_3271097 := by
    simpa [prefixWord, tailWord_3271097, baseEnd_3271097] using wordTrace_append hprefix tailTrace_3271097
  have hstable : (prefixWord ++ tailWord_3271097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271097).length < 2 ^ (prefixWord ++ tailWord_3271097).sum := by decide
  have hdescent : baseEnd_3271097 < baseStart_3271097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271133 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3271133 : Nat := 118140960795 + 3271133 * 2 ^ 59
def prefixEnd_3271133 : Nat := 4983230072969 + 3 ^ 40 * 3271133 * 2
def baseEnd_3271133 : Nat := 1679663513783855410793839

theorem tailTrace_3271133 : CollatzResearch.WordTrace tailWord_3271133 prefixEnd_3271133 1679663513783855410793839 := by
  unfold tailWord_3271133
  simp only [CollatzResearch.WordTrace]
  refine ⟨119308022058251280883914053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79538681372167520589276035 119308022058251280883914053)
  ·
    refine ⟨22370254135922115165733885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119308022058251280883914053 22370254135922115165733885)
    ·
      refine ⟨8388845300970793187150207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22370254135922115165733885 8388845300970793187150207)
      ·
        refine ⟨12583267951456189780725311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388845300970793187150207 12583267951456189780725311)
        ·
          refine ⟨18874901927184284671087967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583267951456189780725311 18874901927184284671087967)
          ·
            refine ⟨28312352890776427006631951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18874901927184284671087967 28312352890776427006631951)
            ·
              refine ⟨42468529336164640509947927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28312352890776427006631951 42468529336164640509947927)
              ·
                refine ⟨63702794004246960764921891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42468529336164640509947927 63702794004246960764921891)
                ·
                  refine ⟨95554191006370441147382837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63702794004246960764921891 95554191006370441147382837)
                  ·
                    refine ⟨8958205406847228857567141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95554191006370441147382837 8958205406847228857567141)
                    ·
                      refine ⟨1679663513783855410793839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8958205406847228857567141 1679663513783855410793839)
                      ·
                        rfl

theorem cell23_3271133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3271133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271133 prefixEnd_3271133 := by exact prefixLift 3271133
  have htrace : WordTrace (prefixWord ++ tailWord_3271133) baseStart_3271133 baseEnd_3271133 := by
    simpa [prefixWord, tailWord_3271133, baseEnd_3271133] using wordTrace_append hprefix tailTrace_3271133
  have hstable : (prefixWord ++ tailWord_3271133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271133).length < 2 ^ (prefixWord ++ tailWord_3271133).sum := by decide
  have hdescent : baseEnd_3271133 < baseStart_3271133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271143 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3271143 : Nat := 118140960795 + 3271143 * 2 ^ 59
def prefixEnd_3271143 : Nat := 4983230072969 + 3 ^ 40 * 3271143 * 2
def baseEnd_3271143 : Nat := 559889549530133457222931

theorem tailTrace_3271143 : CollatzResearch.WordTrace tailWord_3271143 prefixEnd_3271143 559889549530133457222931 := by
  unfold tailWord_3271143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119308386788215052591778083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79538924525476701727852055 119308386788215052591778083)
  ·
    refine ⟨178962580182322578887667125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119308386788215052591778083 178962580182322578887667125)
    ·
      refine ⟨16777741892092741770718793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178962580182322578887667125 16777741892092741770718793)
      ·
        refine ⟨12583306419069556328039095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16777741892092741770718793 12583306419069556328039095)
        ·
          refine ⟨18874959628604334492058643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583306419069556328039095 18874959628604334492058643)
          ·
            refine ⟨28312439442906501738087965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18874959628604334492058643 28312439442906501738087965)
            ·
              refine ⟨10617164791089938151782987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28312439442906501738087965 10617164791089938151782987)
              ·
                refine ⟨15925747186634907227674481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617164791089938151782987 15925747186634907227674481)
                ·
                  refine ⟨11944310389976180420755861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15925747186634907227674481 11944310389976180420755861)
                  ·
                    refine ⟨559889549530133457222931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11944310389976180420755861 559889549530133457222931)
                    ·
                      rfl

theorem cell23_3271143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3271143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271143 prefixEnd_3271143 := by exact prefixLift 3271143
  have htrace : WordTrace (prefixWord ++ tailWord_3271143) baseStart_3271143 baseEnd_3271143 := by
    simpa [prefixWord, tailWord_3271143, baseEnd_3271143] using wordTrace_append hprefix tailTrace_3271143
  have hstable : (prefixWord ++ tailWord_3271143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271143).length < 2 ^ (prefixWord ++ tailWord_3271143).sum := by decide
  have hdescent : baseEnd_3271143 < baseStart_3271143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271153 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_3271153 : Nat := 118140960795 + 3271153 * 2 ^ 59
def prefixEnd_3271153 : Nat := 4983230072969 + 3 ^ 40 * 3271153 * 2
def baseEnd_3271153 : Nat := 1679673783396945332543747

theorem tailTrace_3271153 : CollatzResearch.WordTrace tailWord_3271153 prefixEnd_3271153 1679673783396945332543747 := by
  unfold tailWord_3271153
  simp only [CollatzResearch.WordTrace]
  refine ⟨119308751518178824299642113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79539167678785882866428075 119308751518178824299642113)
  ·
    refine ⟨89481563638634118224731585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119308751518178824299642113 89481563638634118224731585)
    ·
      refine ⟨67111172728975588668548689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89481563638634118224731585 67111172728975588668548689)
      ·
        refine ⟨50333379546731691501411517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67111172728975588668548689 50333379546731691501411517)
        ·
          refine ⟨18875017330024384313029319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50333379546731691501411517 18875017330024384313029319)
          ·
            refine ⟨28312525995036576469543979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18875017330024384313029319 28312525995036576469543979)
            ·
              refine ⟨42468788992554864704315969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28312525995036576469543979 42468788992554864704315969)
              ·
                refine ⟨31851591744416148528236977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42468788992554864704315969 31851591744416148528236977)
                ·
                  refine ⟨23888693808312111396177733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31851591744416148528236977 23888693808312111396177733)
                  ·
                    refine ⟨4479130089058520886783325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23888693808312111396177733 4479130089058520886783325)
                    ·
                      refine ⟨1679673783396945332543747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479130089058520886783325 1679673783396945332543747)
                      ·
                        rfl

theorem cell23_3271153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_3271153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271153 prefixEnd_3271153 := by exact prefixLift 3271153
  have htrace : WordTrace (prefixWord ++ tailWord_3271153) baseStart_3271153 baseEnd_3271153 := by
    simpa [prefixWord, tailWord_3271153, baseEnd_3271153] using wordTrace_append hprefix tailTrace_3271153
  have hstable : (prefixWord ++ tailWord_3271153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271153).length < 2 ^ (prefixWord ++ tailWord_3271153).sum := by decide
  have hdescent : baseEnd_3271153 < baseStart_3271153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271183 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_3271183 : Nat := 118140960795 + 3271183 * 2 ^ 59
def prefixEnd_3271183 : Nat := 4983230072969 + 3 ^ 40 * 3271183 * 2
def baseEnd_3271183 : Nat := 1679689187816580215168609

theorem tailTrace_3271183 : CollatzResearch.WordTrace tailWord_3271183 prefixEnd_3271183 1679689187816580215168609 := by
  unfold tailWord_3271183
  simp only [CollatzResearch.WordTrace]
  refine ⟨119309845708070139423234203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79539897138713426282156135 119309845708070139423234203)
  ·
    refine ⟨178964768562105209134851305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119309845708070139423234203 178964768562105209134851305)
    ·
      refine ⟨134223576421578906851138479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178964768562105209134851305 134223576421578906851138479)
      ·
        refine ⟨201335364632368360276707719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134223576421578906851138479 201335364632368360276707719)
        ·
          refine ⟨302003046948552540415061579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201335364632368360276707719 302003046948552540415061579)
          ·
            refine ⟨453004570422828810622592369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302003046948552540415061579 453004570422828810622592369)
            ·
              refine ⟨339753427817121607966944277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453004570422828810622592369 339753427817121607966944277)
              ·
                refine ⟨15925941928927575373450513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 339753427817121607966944277 15925941928927575373450513)
                ·
                  refine ⟨11944456446695681530087885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15925941928927575373450513 11944456446695681530087885)
                  ·
                    refine ⟨4479171167510880573782957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11944456446695681530087885 4479171167510880573782957)
                    ·
                      refine ⟨1679689187816580215168609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479171167510880573782957 1679689187816580215168609)
                      ·
                        rfl

theorem cell23_3271183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_3271183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271183 prefixEnd_3271183 := by exact prefixLift 3271183
  have htrace : WordTrace (prefixWord ++ tailWord_3271183) baseStart_3271183 baseEnd_3271183 := by
    simpa [prefixWord, tailWord_3271183, baseEnd_3271183] using wordTrace_append hprefix tailTrace_3271183
  have hstable : (prefixWord ++ tailWord_3271183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271183).length < 2 ^ (prefixWord ++ tailWord_3271183).sum := by decide
  have hdescent : baseEnd_3271183 < baseStart_3271183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271203 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 7]
def baseStart_3271203 : Nat := 118140960795 + 3271203 * 2 ^ 59
def prefixEnd_3271203 : Nat := 4983230072969 + 3 ^ 40 * 3271203 * 2
def baseEnd_3271203 : Nat := 559899819143223378972839

theorem tailTrace_3271203 : CollatzResearch.WordTrace tailWord_3271203 prefixEnd_3271203 559899819143223378972839 := by
  unfold tailWord_3271203
  simp only [CollatzResearch.WordTrace]
  refine ⟨119310575167997682838962263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79540383445331788559308175 119310575167997682838962263)
  ·
    refine ⟨178965862751996524258443395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119310575167997682838962263 178965862751996524258443395)
    ·
      refine ⟨268448794127994786387665093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178965862751996524258443395 268448794127994786387665093)
      ·
        refine ⟨50334148898999022447687205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268448794127994786387665093 50334148898999022447687205)
        ·
          refine ⟨9437652918562316708941351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50334148898999022447687205 9437652918562316708941351)
          ·
            refine ⟨14156479377843475063412027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437652918562316708941351 14156479377843475063412027)
            ·
              refine ⟨21234719066765212595118041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14156479377843475063412027 21234719066765212595118041)
              ·
                refine ⟨15926039300073909446338531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21234719066765212595118041 15926039300073909446338531)
                ·
                  refine ⟨23889058950110864169507797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15926039300073909446338531 23889058950110864169507797)
                  ·
                    refine ⟨559899819143223378972839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23889058950110864169507797 559899819143223378972839)
                    ·
                      rfl

theorem cell23_3271203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_3271203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271203 prefixEnd_3271203 := by exact prefixLift 3271203
  have htrace : WordTrace (prefixWord ++ tailWord_3271203) baseStart_3271203 baseEnd_3271203 := by
    simpa [prefixWord, tailWord_3271203, baseEnd_3271203] using wordTrace_append hprefix tailTrace_3271203
  have hstable : (prefixWord ++ tailWord_3271203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271203).length < 2 ^ (prefixWord ++ tailWord_3271203).sum := by decide
  have hdescent : baseEnd_3271203 < baseStart_3271203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271223 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3271223 : Nat := 118140960795 + 3271223 * 2 ^ 59
def prefixEnd_3271223 : Nat := 4983230072969 + 3 ^ 40 * 3271223 * 2
def baseEnd_3271223 : Nat := 1679709727042760058668425

theorem tailTrace_3271223 : CollatzResearch.WordTrace tailWord_3271223 prefixEnd_3271223 1679709727042760058668425 := by
  unfold tailWord_3271223
  simp only [CollatzResearch.WordTrace]
  refine ⟨119311304627925226254690323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79540869751950150836460215 119311304627925226254690323)
  ·
    refine ⟨178966956941887839382035485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119311304627925226254690323 178966956941887839382035485)
    ·
      refine ⟨67112608853207939768263307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178966956941887839382035485 67112608853207939768263307)
      ·
        refine ⟨100668913279811909652394961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67112608853207939768263307 100668913279811909652394961)
        ·
          refine ⟨75501684959858932239296221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100668913279811909652394961 75501684959858932239296221)
          ·
            refine ⟨28313131859947099589736083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75501684959858932239296221 28313131859947099589736083)
            ·
              refine ⟨42469697789920649384604125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28313131859947099589736083 42469697789920649384604125)
              ·
                refine ⟨15926136671220243519226547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42469697789920649384604125 15926136671220243519226547)
                ·
                  refine ⟨23889205006830365278839821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15926136671220243519226547 23889205006830365278839821)
                  ·
                    refine ⟨8958451877561386979564933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23889205006830365278839821 8958451877561386979564933)
                    ·
                      refine ⟨1679709727042760058668425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8958451877561386979564933 1679709727042760058668425)
                      ·
                        rfl

theorem cell23_3271223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3271223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271223 prefixEnd_3271223 := by exact prefixLift 3271223
  have htrace : WordTrace (prefixWord ++ tailWord_3271223) baseStart_3271223 baseEnd_3271223 := by
    simpa [prefixWord, tailWord_3271223, baseEnd_3271223] using wordTrace_append hprefix tailTrace_3271223
  have hstable : (prefixWord ++ tailWord_3271223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271223).length < 2 ^ (prefixWord ++ tailWord_3271223).sum := by decide
  have hdescent : baseEnd_3271223 < baseStart_3271223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271240 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_3271240 : Nat := 118140960795 + 3271240 * 2 ^ 59
def prefixEnd_3271240 : Nat := 4983230072969 + 3 ^ 40 * 3271240 * 2
def baseEnd_3271240 : Nat := 1679718456213886492155847

theorem tailTrace_3271240 : CollatzResearch.WordTrace tailWord_3271240 prefixEnd_3271240 1679718456213886492155847 := by
  unfold tailWord_3271240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59655962334431819079029587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79541283112575758772039449 59655962334431819079029587)
  ·
    refine ⟨89483943501647728618544381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59655962334431819079029587 89483943501647728618544381)
    ·
      refine ⟨33556478813117898231954143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89483943501647728618544381 33556478813117898231954143)
      ·
        refine ⟨50334718219676847347931215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33556478813117898231954143 50334718219676847347931215)
        ·
          refine ⟨75502077329515271021896823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50334718219676847347931215 75502077329515271021896823)
          ·
            refine ⟨113253115994272906532845235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75502077329515271021896823 113253115994272906532845235)
            ·
              refine ⟨169879673991409359799267853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113253115994272906532845235 169879673991409359799267853)
              ·
                refine ⟨63704877746778509924725445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169879673991409359799267853 63704877746778509924725445)
                ·
                  refine ⟨11944664577520970610886021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63704877746778509924725445 11944664577520970610886021)
                  ·
                    refine ⟨2239624608285181989541129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11944664577520970610886021 2239624608285181989541129)
                    ·
                      refine ⟨1679718456213886492155847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239624608285181989541129 1679718456213886492155847)
                      ·
                        rfl

theorem cell23_3271240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_3271240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271240 prefixEnd_3271240 := by exact prefixLift 3271240
  have htrace : WordTrace (prefixWord ++ tailWord_3271240) baseStart_3271240 baseEnd_3271240 := by
    simpa [prefixWord, tailWord_3271240, baseEnd_3271240] using wordTrace_append hprefix tailTrace_3271240
  have hstable : (prefixWord ++ tailWord_3271240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271240).length < 2 ^ (prefixWord ++ tailWord_3271240).sum := by decide
  have hdescent : baseEnd_3271240 < baseStart_3271240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271253 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3271253 : Nat := 118140960795 + 3271253 * 2 ^ 59
def prefixEnd_3271253 : Nat := 4983230072969 + 3 ^ 40 * 3271253 * 2
def baseEnd_3271253 : Nat := 1679725131462394941293287

theorem tailTrace_3271253 : CollatzResearch.WordTrace tailWord_3271253 prefixEnd_3271253 1679725131462394941293287 := by
  unfold tailWord_3271253
  simp only [CollatzResearch.WordTrace]
  refine ⟨119312398817816541378282413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79541599211877694252188275 119312398817816541378282413)
  ·
    refine ⟨44742149556681203016855905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119312398817816541378282413 44742149556681203016855905)
    ·
      refine ⟨33556612167510902262641929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44742149556681203016855905 33556612167510902262641929)
      ·
        refine ⟨25167459125633176696981447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33556612167510902262641929 25167459125633176696981447)
        ·
          refine ⟨37751188688449765045472171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25167459125633176696981447 37751188688449765045472171)
          ·
            refine ⟨56626783032674647568208257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37751188688449765045472171 56626783032674647568208257)
            ·
              refine ⟨42470087274505985676156193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56626783032674647568208257 42470087274505985676156193)
              ·
                refine ⟨31852565455879489257117145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42470087274505985676156193 31852565455879489257117145)
                ·
                  refine ⟨23889424091909616942837859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31852565455879489257117145 23889424091909616942837859)
                  ·
                    refine ⟨35834136137864425414256789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23889424091909616942837859 35834136137864425414256789)
                    ·
                      refine ⟨1679725131462394941293287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35834136137864425414256789 1679725131462394941293287)
                      ·
                        rfl

theorem cell23_3271253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3271253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271253 prefixEnd_3271253 := by exact prefixLift 3271253
  have htrace : WordTrace (prefixWord ++ tailWord_3271253) baseStart_3271253 baseEnd_3271253 := by
    simpa [prefixWord, tailWord_3271253, baseEnd_3271253] using wordTrace_append hprefix tailTrace_3271253
  have hstable : (prefixWord ++ tailWord_3271253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271253).length < 2 ^ (prefixWord ++ tailWord_3271253).sum := by decide
  have hdescent : baseEnd_3271253 < baseStart_3271253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271277 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3271277 : Nat := 118140960795 + 3271277 * 2 ^ 59
def prefixEnd_3271277 : Nat := 4983230072969 + 3 ^ 40 * 3271277 * 2
def baseEnd_3271277 : Nat := 1679737454998102847393177

theorem tailTrace_3271277 : CollatzResearch.WordTrace tailWord_3271277 prefixEnd_3271277 1679737454998102847393177 := by
  unfold tailWord_3271277
  simp only [CollatzResearch.WordTrace]
  refine ⟨119313274169729593477156085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79542182779819728984770723 119313274169729593477156085)
  ·
    refine ⟨11185619453412149388483383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119313274169729593477156085 11185619453412149388483383)
    ·
      refine ⟨16778429180118224082725075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11185619453412149388483383 16778429180118224082725075)
      ·
        refine ⟨25167643770177336124087613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16778429180118224082725075 25167643770177336124087613)
        ·
          refine ⟨9437866413816501046532855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25167643770177336124087613 9437866413816501046532855)
          ·
            refine ⟨14156799620724751569799283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437866413816501046532855 14156799620724751569799283)
            ·
              refine ⟨21235199431087127354698925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14156799620724751569799283 21235199431087127354698925)
              ·
                refine ⟨7963199786657672758012097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21235199431087127354698925 7963199786657672758012097)
                ·
                  refine ⟨5972399839993254568509073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7963199786657672758012097 5972399839993254568509073)
                  ·
                    refine ⟨4479299879994940926381805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972399839993254568509073 4479299879994940926381805)
                    ·
                      refine ⟨1679737454998102847393177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479299879994940926381805 1679737454998102847393177)
                      ·
                        rfl

theorem cell23_3271277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3271277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271277 prefixEnd_3271277 := by exact prefixLift 3271277
  have htrace : WordTrace (prefixWord ++ tailWord_3271277) baseStart_3271277 baseEnd_3271277 := by
    simpa [prefixWord, tailWord_3271277, baseEnd_3271277] using wordTrace_append hprefix tailTrace_3271277
  have hstable : (prefixWord ++ tailWord_3271277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271277).length < 2 ^ (prefixWord ++ tailWord_3271277).sum := by decide
  have hdescent : baseEnd_3271277 < baseStart_3271277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271301 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_3271301 : Nat := 118140960795 + 3271301 * 2 ^ 59
def prefixEnd_3271301 : Nat := 4983230072969 + 3 ^ 40 * 3271301 * 2
def baseEnd_3271301 : Nat := 559916592844603584497689

theorem tailTrace_3271301 : CollatzResearch.WordTrace tailWord_3271301 prefixEnd_3271301 559916592844603584497689 := by
  unfold tailWord_3271301
  simp only [CollatzResearch.WordTrace]
  refine ⟨119314149521642645576029757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79542766347761763717353171 119314149521642645576029757)
  ·
    refine ⟨44742806070615992091011159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119314149521642645576029757 44742806070615992091011159)
    ·
      refine ⟨67114209105923988136516739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44742806070615992091011159 67114209105923988136516739)
      ·
        refine ⟨100671313658885982204775109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67114209105923988136516739 100671313658885982204775109)
        ·
          refine ⟨18875871311041121663395333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100671313658885982204775109 18875871311041121663395333)
          ·
            refine ⟨3539225870820210311886625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18875871311041121663395333 3539225870820210311886625)
            ·
              refine ⟨2654419403115157733914969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539225870820210311886625 2654419403115157733914969)
              ·
                refine ⟨1990814552336368300436227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654419403115157733914969 1990814552336368300436227)
                ·
                  refine ⟨2986221828504552450654341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990814552336368300436227 2986221828504552450654341)
                  ·
                    refine ⟨559916592844603584497689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986221828504552450654341 559916592844603584497689)
                    ·
                      rfl

theorem cell23_3271301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_3271301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271301 prefixEnd_3271301 := by exact prefixLift 3271301
  have htrace : WordTrace (prefixWord ++ tailWord_3271301) baseStart_3271301 baseEnd_3271301 := by
    simpa [prefixWord, tailWord_3271301, baseEnd_3271301] using wordTrace_append hprefix tailTrace_3271301
  have hstable : (prefixWord ++ tailWord_3271301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271301).length < 2 ^ (prefixWord ++ tailWord_3271301).sum := by decide
  have hdescent : baseEnd_3271301 < baseStart_3271301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271310 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3271310 : Nat := 118140960795 + 3271310 * 2 ^ 59
def prefixEnd_3271310 : Nat := 4983230072969 + 3 ^ 40 * 3271310 * 2
def baseEnd_3271310 : Nat := 559918133286567072760175

theorem tailTrace_3271310 : CollatzResearch.WordTrace tailWord_3271310 prefixEnd_3271310 559918133286567072760175 := by
  unfold tailWord_3271310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14914309722326255014138423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79542985185740026742071589 14914309722326255014138423)
  ·
    refine ⟨22371464583489382521207635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14914309722326255014138423 22371464583489382521207635)
    ·
      refine ⟨33557196875234073781811453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371464583489382521207635 33557196875234073781811453)
      ·
        refine ⟨12583948828212777668179295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33557196875234073781811453 12583948828212777668179295)
        ·
          refine ⟨18875923242319166502268943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12583948828212777668179295 18875923242319166502268943)
          ·
            refine ⟨28313884863478749753403415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18875923242319166502268943 28313884863478749753403415)
            ·
              refine ⟨42470827295218124630105123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28313884863478749753403415 42470827295218124630105123)
              ·
                refine ⟨63706240942827186945157685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42470827295218124630105123 63706240942827186945157685)
                ·
                  refine ⟨5972460088390048776108533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63706240942827186945157685 5972460088390048776108533)
                  ·
                    refine ⟨559918133286567072760175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5972460088390048776108533 559918133286567072760175)
                    ·
                      rfl

theorem cell23_3271310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3271310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271310 prefixEnd_3271310 := by exact prefixLift 3271310
  have htrace : WordTrace (prefixWord ++ tailWord_3271310) baseStart_3271310 baseEnd_3271310 := by
    simpa [prefixWord, tailWord_3271310, baseEnd_3271310] using wordTrace_append hprefix tailTrace_3271310
  have hstable : (prefixWord ++ tailWord_3271310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271310).length < 2 ^ (prefixWord ++ tailWord_3271310).sum := by decide
  have hdescent : baseEnd_3271310 < baseStart_3271310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271324 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3271324 : Nat := 118140960795 + 3271324 * 2 ^ 59
def prefixEnd_3271324 : Nat := 4983230072969 + 3 ^ 40 * 3271324 * 2
def baseEnd_3271324 : Nat := 1679761588588864163505461

theorem tailTrace_3271324 : CollatzResearch.WordTrace tailWord_3271324 prefixEnd_3271324 1679761588588864163505461 := by
  unfold tailWord_3271324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59657494200279660252058513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79543325600372880336078017 59657494200279660252058513)
  ·
    refine ⟨44743120650209745189043885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59657494200279660252058513 44743120650209745189043885)
    ·
      refine ⟨16778670243828654445891457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44743120650209745189043885 16778670243828654445891457)
      ·
        refine ⟨12584002682871490834418593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16778670243828654445891457 12584002682871490834418593)
        ·
          refine ⟨9438002012153618125813945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12584002682871490834418593 9438002012153618125813945)
          ·
            refine ⟨7078501509115213594360459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438002012153618125813945 7078501509115213594360459)
            ·
              refine ⟨10617752263672820391540689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078501509115213594360459 10617752263672820391540689)
              ·
                refine ⟨7963314197754615293655517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10617752263672820391540689 7963314197754615293655517)
                ·
                  refine ⟨2986242824157980735120819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7963314197754615293655517 2986242824157980735120819)
                  ·
                    refine ⟨4479364236236971102681229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986242824157980735120819 4479364236236971102681229)
                    ·
                      refine ⟨1679761588588864163505461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479364236236971102681229 1679761588588864163505461)
                      ·
                        rfl

theorem cell23_3271324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3271324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271324 prefixEnd_3271324 := by exact prefixLift 3271324
  have htrace : WordTrace (prefixWord ++ tailWord_3271324) baseStart_3271324 baseEnd_3271324 := by
    simpa [prefixWord, tailWord_3271324, baseEnd_3271324] using wordTrace_append hprefix tailTrace_3271324
  have hstable : (prefixWord ++ tailWord_3271324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271324).length < 2 ^ (prefixWord ++ tailWord_3271324).sum := by decide
  have hdescent : baseEnd_3271324 < baseStart_3271324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271341 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_3271341 : Nat := 118140960795 + 3271341 * 2 ^ 59
def prefixEnd_3271341 : Nat := 4983230072969 + 3 ^ 40 * 3271341 * 2
def baseEnd_3271341 : Nat := 1679770317759990596992883

theorem tailTrace_3271341 : CollatzResearch.WordTrace tailWord_3271341 prefixEnd_3271341 1679770317759990596992883 := by
  unfold tailWord_3271341
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315608441497732407485877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79543738960998488271657251 119315608441497732407485877)
  ·
    refine ⟨11185838291390412413201801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119315608441497732407485877 11185838291390412413201801)
    ·
      refine ⟨8389378718542809309901351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11185838291390412413201801 8389378718542809309901351)
      ·
        refine ⟨12584068077814213964852027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389378718542809309901351 12584068077814213964852027)
        ·
          refine ⟨18876102116721320947278041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12584068077814213964852027 18876102116721320947278041)
          ·
            refine ⟨14157076587540990710458531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18876102116721320947278041 14157076587540990710458531)
            ·
              refine ⟨21235614881311486065687797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157076587540990710458531 21235614881311486065687797)
              ·
                refine ⟨1990838895122951818658231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21235614881311486065687797 1990838895122951818658231)
                ·
                  refine ⟨2986258342684427727987347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990838895122951818658231 2986258342684427727987347)
                  ·
                    refine ⟨4479387514026641591981021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986258342684427727987347 4479387514026641591981021)
                    ·
                      refine ⟨1679770317759990596992883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479387514026641591981021 1679770317759990596992883)
                      ·
                        rfl

theorem cell23_3271341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_3271341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271341 prefixEnd_3271341 := by exact prefixLift 3271341
  have htrace : WordTrace (prefixWord ++ tailWord_3271341) baseStart_3271341 baseEnd_3271341 := by
    simpa [prefixWord, tailWord_3271341, baseEnd_3271341] using wordTrace_append hprefix tailTrace_3271341
  have hstable : (prefixWord ++ tailWord_3271341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271341).length < 2 ^ (prefixWord ++ tailWord_3271341).sum := by decide
  have hdescent : baseEnd_3271341 < baseStart_3271341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271347 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 4]
def baseStart_3271347 : Nat := 118140960795 + 3271347 * 2 ^ 59
def prefixEnd_3271347 : Nat := 4983230072969 + 3 ^ 40 * 3271347 * 2
def baseEnd_3271347 : Nat := 1679773398643917573517855

theorem tailTrace_3271347 : CollatzResearch.WordTrace tailWord_3271347 prefixEnd_3271347 1679773398643917573517855 := by
  unfold tailWord_3271347
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315827279475995432204295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79543884852983996954802863 119315827279475995432204295)
  ·
    refine ⟨178973740919213993148306443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119315827279475995432204295 178973740919213993148306443)
    ·
      refine ⟨268460611378820989722459665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178973740919213993148306443 268460611378820989722459665)
      ·
        refine ⟨201345458534115742291844749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268460611378820989722459665 201345458534115742291844749)
        ·
          refine ⟨75504546950293403359441781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201345458534115742291844749 75504546950293403359441781)
          ·
            refine ⟨7078551276590006564947667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75504546950293403359441781 7078551276590006564947667)
            ·
              refine ⟨10617826914885009847421501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078551276590006564947667 10617826914885009847421501)
              ·
                refine ⟨3981685093081878692783063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10617826914885009847421501 3981685093081878692783063)
                ·
                  refine ⟨5972527639622818039174595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981685093081878692783063 5972527639622818039174595)
                  ·
                    refine ⟨8958791459434227058761893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5972527639622818039174595 8958791459434227058761893)
                    ·
                      refine ⟨1679773398643917573517855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8958791459434227058761893 1679773398643917573517855)
                      ·
                        rfl

theorem cell23_3271347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_3271347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271347 prefixEnd_3271347 := by exact prefixLift 3271347
  have htrace : WordTrace (prefixWord ++ tailWord_3271347) baseStart_3271347 baseEnd_3271347 := by
    simpa [prefixWord, tailWord_3271347, baseEnd_3271347] using wordTrace_append hprefix tailTrace_3271347
  have hstable : (prefixWord ++ tailWord_3271347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271347).length < 2 ^ (prefixWord ++ tailWord_3271347).sum := by decide
  have hdescent : baseEnd_3271347 < baseStart_3271347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271357 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_3271357 : Nat := 118140960795 + 3271357 * 2 ^ 59
def prefixEnd_3271357 : Nat := 4983230072969 + 3 ^ 40 * 3271357 * 2
def baseEnd_3271357 : Nat := 559926177816820844797603

theorem tailTrace_3271357 : CollatzResearch.WordTrace tailWord_3271357 prefixEnd_3271357 559926177816820844797603 := by
  unfold tailWord_3271357
  simp only [CollatzResearch.WordTrace]
  refine ⟨119316192009439767140068325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79544128006293178093378883 119316192009439767140068325)
  ·
    refine ⟨22371786001769956338762811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119316192009439767140068325 22371786001769956338762811)
    ·
      refine ⟨33557679002654934508144217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22371786001769956338762811 33557679002654934508144217)
      ·
        refine ⟨25168259251991200881108163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33557679002654934508144217 25168259251991200881108163)
        ·
          refine ⟨37752388877986801321662245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25168259251991200881108163 37752388877986801321662245)
          ·
            refine ⟨7078572914622525247811671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37752388877986801321662245 7078572914622525247811671)
            ·
              refine ⟨10617859371933787871717507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078572914622525247811671 10617859371933787871717507)
              ·
                refine ⟨15926789057900681807576261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617859371933787871717507 15926789057900681807576261)
                ·
                  refine ⟨2986272948356377838920549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15926789057900681807576261 2986272948356377838920549)
                  ·
                    refine ⟨559926177816820844797603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986272948356377838920549 559926177816820844797603)
                    ·
                      rfl

theorem cell23_3271357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_3271357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271357 prefixEnd_3271357 := by exact prefixLift 3271357
  have htrace : WordTrace (prefixWord ++ tailWord_3271357) baseStart_3271357 baseEnd_3271357 := by
    simpa [prefixWord, tailWord_3271357, baseEnd_3271357] using wordTrace_append hprefix tailTrace_3271357
  have hstable : (prefixWord ++ tailWord_3271357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271357).length < 2 ^ (prefixWord ++ tailWord_3271357).sum := by decide
  have hdescent : baseEnd_3271357 < baseStart_3271357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271381 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3271381 : Nat := 118140960795 + 3271381 * 2 ^ 59
def prefixEnd_3271381 : Nat := 4983230072969 + 3 ^ 40 * 3271381 * 2
def baseEnd_3271381 : Nat := 1679790856986170440492699

theorem tailTrace_3271381 : CollatzResearch.WordTrace tailWord_3271381 prefixEnd_3271381 1679790856986170440492699 := by
  unfold tailWord_3271381
  simp only [CollatzResearch.WordTrace]
  refine ⟨119317067361352819238941997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79544711574235212825961331 119317067361352819238941997)
  ·
    refine ⟨44743900260507307214603249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119317067361352819238941997 44743900260507307214603249)
    ·
      refine ⟨33557925195380480410952437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44743900260507307214603249 33557925195380480410952437)
      ·
        refine ⟨3146055487066920038526791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33557925195380480410952437 3146055487066920038526791)
        ·
          refine ⟨4719083230600380057790187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146055487066920038526791 4719083230600380057790187)
          ·
            refine ⟨7078624845900570086685281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719083230600380057790187 7078624845900570086685281)
            ·
              refine ⟨5308968634425427565013961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078624845900570086685281 5308968634425427565013961)
              ·
                refine ⟨3981726475819070673760471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308968634425427565013961 3981726475819070673760471)
                ·
                  refine ⟨5972589713728606010640707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981726475819070673760471 5972589713728606010640707)
                  ·
                    refine ⟨8958884570592909015961061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5972589713728606010640707 8958884570592909015961061)
                    ·
                      refine ⟨1679790856986170440492699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8958884570592909015961061 1679790856986170440492699)
                      ·
                        rfl

theorem cell23_3271381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3271381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271381 prefixEnd_3271381 := by exact prefixLift 3271381
  have htrace : WordTrace (prefixWord ++ tailWord_3271381) baseStart_3271381 baseEnd_3271381 := by
    simpa [prefixWord, tailWord_3271381, baseEnd_3271381] using wordTrace_append hprefix tailTrace_3271381
  have hstable : (prefixWord ++ tailWord_3271381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271381).length < 2 ^ (prefixWord ++ tailWord_3271381).sum := by decide
  have hdescent : baseEnd_3271381 < baseStart_3271381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271384 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3271384 : Nat := 118140960795 + 3271384 * 2 ^ 59
def prefixEnd_3271384 : Nat := 4983230072969 + 3 ^ 40 * 3271384 * 2
def baseEnd_3271384 : Nat := 1679792397428133928755185

theorem tailTrace_3271384 : CollatzResearch.WordTrace tailWord_3271384 prefixEnd_3271384 1679792397428133928755185 := by
  unfold tailWord_3271384
  simp only [CollatzResearch.WordTrace]
  refine ⟨59658588390170975375650603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79544784520227967167534137 59658588390170975375650603)
  ·
    refine ⟨89487882585256463063475905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59658588390170975375650603 89487882585256463063475905)
    ·
      refine ⟨67115911938942347297606929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89487882585256463063475905 67115911938942347297606929)
      ·
        refine ⟨50336933954206760473205197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67115911938942347297606929 50336933954206760473205197)
        ·
          refine ⟨18876350232827535177451949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50336933954206760473205197 18876350232827535177451949)
          ·
            refine ⟨7078631337310325691544481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18876350232827535177451949 7078631337310325691544481)
            ·
              refine ⟨5308973502982744268658361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7078631337310325691544481 5308973502982744268658361)
              ·
                refine ⟨3981730127237058201493771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308973502982744268658361 3981730127237058201493771)
                ·
                  refine ⟨5972595190855587302240657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981730127237058201493771 5972595190855587302240657)
                  ·
                    refine ⟨4479446393141690476680493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5972595190855587302240657 4479446393141690476680493)
                    ·
                      refine ⟨1679792397428133928755185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479446393141690476680493 1679792397428133928755185)
                      ·
                        rfl

theorem cell23_3271384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3271384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271384 prefixEnd_3271384 := by exact prefixLift 3271384
  have htrace : WordTrace (prefixWord ++ tailWord_3271384) baseStart_3271384 baseEnd_3271384 := by
    simpa [prefixWord, tailWord_3271384, baseEnd_3271384] using wordTrace_append hprefix tailTrace_3271384
  have hstable : (prefixWord ++ tailWord_3271384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271384).length < 2 ^ (prefixWord ++ tailWord_3271384).sum := by decide
  have hdescent : baseEnd_3271384 < baseStart_3271384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271414 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3271414 : Nat := 118140960795 + 3271414 * 2 ^ 59
def prefixEnd_3271414 : Nat := 4983230072969 + 3 ^ 40 * 3271414 * 2
def baseEnd_3271414 : Nat := 1679807801847768811380047

theorem tailTrace_3271414 : CollatzResearch.WordTrace tailWord_3271414 prefixEnd_3271414 1679807801847768811380047 := by
  unfold tailWord_3271414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457391935639579117180831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79545513980155510583262197 7457391935639579117180831)
  ·
    refine ⟨11186087903459368675771247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7457391935639579117180831 11186087903459368675771247)
    ·
      refine ⟨16779131855189053013656871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11186087903459368675771247 16779131855189053013656871)
      ·
        refine ⟨25168697782783579520485307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779131855189053013656871 25168697782783579520485307)
        ·
          refine ⟨37753046674175369280727961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25168697782783579520485307 37753046674175369280727961)
          ·
            refine ⟨28314785005631526960545971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37753046674175369280727961 28314785005631526960545971)
            ·
              refine ⟨42472177508447290440818957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28314785005631526960545971 42472177508447290440818957)
              ·
                refine ⟨15927066565667733915307109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42472177508447290440818957 15927066565667733915307109)
                ·
                  refine ⟨2986324981062700109120083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15927066565667733915307109 2986324981062700109120083)
                  ·
                    refine ⟨4479487471594050163680125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986324981062700109120083 4479487471594050163680125)
                    ·
                      refine ⟨1679807801847768811380047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479487471594050163680125 1679807801847768811380047)
                      ·
                        rfl

theorem cell23_3271414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3271414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271414 prefixEnd_3271414 := by exact prefixLift 3271414
  have htrace : WordTrace (prefixWord ++ tailWord_3271414) baseStart_3271414 baseEnd_3271414 := by
    simpa [prefixWord, tailWord_3271414, baseEnd_3271414] using wordTrace_append hprefix tailTrace_3271414
  have hstable : (prefixWord ++ tailWord_3271414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271414).length < 2 ^ (prefixWord ++ tailWord_3271414).sum := by decide
  have hdescent : baseEnd_3271414 < baseStart_3271414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271431 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3271431 : Nat := 118140960795 + 3271431 * 2 ^ 59
def prefixEnd_3271431 : Nat := 4983230072969 + 3 ^ 40 * 3271431 * 2
def baseEnd_3271431 : Nat := 1679816531018895244867469

theorem tailTrace_3271431 : CollatzResearch.WordTrace tailWord_3271431 prefixEnd_3271431 1679816531018895244867469 := by
  unfold tailWord_3271431
  simp only [CollatzResearch.WordTrace]
  refine ⟨119318891011171677778262147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79545927340781118518841431 119318891011171677778262147)
  ·
    refine ⟨178978336516757516667393221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119318891011171677778262147 178978336516757516667393221)
    ·
      refine ⟨33558438096892034375136229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178978336516757516667393221 33558438096892034375136229)
      ·
        refine ⟨6292207143167256445338043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33558438096892034375136229 6292207143167256445338043)
        ·
          refine ⟨9438310714750884668007065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292207143167256445338043 9438310714750884668007065)
          ·
            refine ⟨7078733036063163501005299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438310714750884668007065 7078733036063163501005299)
            ·
              refine ⟨10618099554094745251507949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7078733036063163501005299 10618099554094745251507949)
              ·
                refine ⟨3981787332785529469315481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10618099554094745251507949 3981787332785529469315481)
                ·
                  refine ⟨2986340499589147101986611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3981787332785529469315481 2986340499589147101986611)
                  ·
                    refine ⟨4479510749383720652979917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986340499589147101986611 4479510749383720652979917)
                    ·
                      refine ⟨1679816531018895244867469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479510749383720652979917 1679816531018895244867469)
                      ·
                        rfl

theorem cell23_3271431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3271431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271431 prefixEnd_3271431 := by exact prefixLift 3271431
  have htrace : WordTrace (prefixWord ++ tailWord_3271431) baseStart_3271431 baseEnd_3271431 := by
    simpa [prefixWord, tailWord_3271431, baseEnd_3271431] using wordTrace_append hprefix tailTrace_3271431
  have hstable : (prefixWord ++ tailWord_3271431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271431).length < 2 ^ (prefixWord ++ tailWord_3271431).sum := by decide
  have hdescent : baseEnd_3271431 < baseStart_3271431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271458 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_3271458 : Nat := 118140960795 + 3271458 * 2 ^ 59
def prefixEnd_3271458 : Nat := 4983230072969 + 3 ^ 40 * 3271458 * 2
def baseEnd_3271458 : Nat := 1679830394996566639229845

theorem tailTrace_3271458 : CollatzResearch.WordTrace tailWord_3271458 prefixEnd_3271458 1679830394996566639229845 := by
  unfold tailWord_3271458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829968945518465347373757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79546583854715907592996685 29829968945518465347373757)
  ·
    refine ⟨11186238354569424505265159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29829968945518465347373757 11186238354569424505265159)
    ·
      refine ⟨16779357531854136757897739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11186238354569424505265159 16779357531854136757897739)
      ·
        refine ⟨25169036297781205136846609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779357531854136757897739 25169036297781205136846609)
        ·
          refine ⟨18876777223335903852634957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25169036297781205136846609 18876777223335903852634957)
          ·
            refine ⟨7078791458750963944738109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18876777223335903852634957 7078791458750963944738109)
            ·
              refine ⟨2654546797031611479276791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7078791458750963944738109 2654546797031611479276791)
              ·
                refine ⟨3981820195547417218915187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654546797031611479276791 3981820195547417218915187)
                ·
                  refine ⟨5972730293321125828372781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981820195547417218915187 5972730293321125828372781)
                  ·
                    refine ⟨2239773859995422185639793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5972730293321125828372781 2239773859995422185639793)
                    ·
                      refine ⟨1679830394996566639229845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239773859995422185639793 1679830394996566639229845)
                      ·
                        rfl

theorem cell23_3271458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_3271458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271458 prefixEnd_3271458 := by exact prefixLift 3271458
  have htrace : WordTrace (prefixWord ++ tailWord_3271458) baseStart_3271458 baseEnd_3271458 := by
    simpa [prefixWord, tailWord_3271458, baseEnd_3271458] using wordTrace_append hprefix tailTrace_3271458
  have hstable : (prefixWord ++ tailWord_3271458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271458).length < 2 ^ (prefixWord ++ tailWord_3271458).sum := by decide
  have hdescent : baseEnd_3271458 < baseStart_3271458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271487 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_3271487 : Nat := 118140960795 + 3271487 * 2 ^ 59
def prefixEnd_3271487 : Nat := 4983230072969 + 3 ^ 40 * 3271487 * 2
def baseEnd_3271487 : Nat := 1679845285935547025767211

theorem tailTrace_3271487 : CollatzResearch.WordTrace tailWord_3271487 prefixEnd_3271487 1679845285935547025767211 := by
  unfold tailWord_3271487
  simp only [CollatzResearch.WordTrace]
  refine ⟨119320933498968799342300715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79547288999312532894867143 119320933498968799342300715)
  ·
    refine ⟨178981400248453199013451073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119320933498968799342300715 178981400248453199013451073)
    ·
      refine ⟨134236050186339899260088305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178981400248453199013451073 134236050186339899260088305)
      ·
        refine ⟨100677037639754924445066229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134236050186339899260088305 100677037639754924445066229)
        ·
          refine ⟨9438472278727024166724959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100677037639754924445066229 9438472278727024166724959)
          ·
            refine ⟨14157708418090536250087439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438472278727024166724959 14157708418090536250087439)
            ·
              refine ⟨21236562627135804375131159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157708418090536250087439 21236562627135804375131159)
              ·
                refine ⟨31854843940703706562696739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21236562627135804375131159 31854843940703706562696739)
                ·
                  refine ⟨47782265911055559844045109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31854843940703706562696739 47782265911055559844045109)
                  ·
                    refine ⟨4479587429161458735379229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47782265911055559844045109 4479587429161458735379229)
                    ·
                      refine ⟨1679845285935547025767211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479587429161458735379229 1679845285935547025767211)
                      ·
                        rfl

theorem cell23_3271487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_3271487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271487 prefixEnd_3271487 := by exact prefixLift 3271487
  have htrace : WordTrace (prefixWord ++ tailWord_3271487) baseStart_3271487 baseEnd_3271487 := by
    simpa [prefixWord, tailWord_3271487, baseEnd_3271487] using wordTrace_append hprefix tailTrace_3271487
  have hstable : (prefixWord ++ tailWord_3271487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271487).length < 2 ^ (prefixWord ++ tailWord_3271487).sum := by decide
  have hdescent : baseEnd_3271487 < baseStart_3271487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271522 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3271522 : Nat := 118140960795 + 3271522 * 2 ^ 59
def prefixEnd_3271522 : Nat := 4983230072969 + 3 ^ 40 * 3271522 * 2
def baseEnd_3271522 : Nat := 1679863257758454388829551

theorem tailTrace_3271522 : CollatzResearch.WordTrace tailWord_3271522 prefixEnd_3271522 1679863257758454388829551 := by
  unfold tailWord_3271522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830552513460500079956205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79548140035894666879883213 29830552513460500079956205)
  ·
    refine ⟨11186457192547687529983577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29830552513460500079956205 11186457192547687529983577)
    ·
      refine ⟨8389842894410765647487683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11186457192547687529983577 8389842894410765647487683)
      ·
        refine ⟨12584764341616148471231525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389842894410765647487683 12584764341616148471231525)
        ·
          refine ⟨2359643314053027838355911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12584764341616148471231525 2359643314053027838355911)
          ·
            refine ⟨3539464971079541757533867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359643314053027838355911 3539464971079541757533867)
            ·
              refine ⟨5309197456619312636300801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539464971079541757533867 5309197456619312636300801)
              ·
                refine ⟨3981898092464484477225601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309197456619312636300801 3981898092464484477225601)
                ·
                  refine ⟨2986423569348363357919201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3981898092464484477225601 2986423569348363357919201)
                  ·
                    refine ⟨2239817677011272518439401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2986423569348363357919201 2239817677011272518439401)
                    ·
                      refine ⟨1679863257758454388829551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239817677011272518439401 1679863257758454388829551)
                      ·
                        rfl

theorem cell23_3271522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3271522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271522 prefixEnd_3271522 := by exact prefixLift 3271522
  have htrace : WordTrace (prefixWord ++ tailWord_3271522) baseStart_3271522 baseEnd_3271522 := by
    simpa [prefixWord, tailWord_3271522, baseEnd_3271522] using wordTrace_append hprefix tailTrace_3271522
  have hstable : (prefixWord ++ tailWord_3271522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271522).length < 2 ^ (prefixWord ++ tailWord_3271522).sum := by decide
  have hdescent : baseEnd_3271522 < baseStart_3271522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271547 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3]
def baseStart_3271547 : Nat := 118140960795 + 3271547 * 2 ^ 59
def prefixEnd_3271547 : Nat := 4983230072969 + 3 ^ 40 * 3271547 * 2
def baseEnd_3271547 : Nat := 1679876094774816791016935

theorem tailTrace_3271547 : CollatzResearch.WordTrace tailWord_3271547 prefixEnd_3271547 1679876094774816791016935 := by
  unfold tailWord_3271547
  simp only [CollatzResearch.WordTrace]
  refine ⟨119323121878751429589484895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79548747919167619726323263 119323121878751429589484895)
  ·
    refine ⟨178984682818127144384227343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119323121878751429589484895 178984682818127144384227343)
    ·
      refine ⟨268477024227190716576341015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178984682818127144384227343 268477024227190716576341015)
      ·
        refine ⟨402715536340786074864511523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268477024227190716576341015 402715536340786074864511523)
        ·
          refine ⟨604073304511179112296767285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402715536340786074864511523 604073304511179112296767285)
          ·
            refine ⟨56631872297923041777821933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 604073304511179112296767285 56631872297923041777821933)
            ·
              refine ⟨21236952111721140666683225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56631872297923041777821933 21236952111721140666683225)
              ·
                refine ⟨15927714083790855500012419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21236952111721140666683225 15927714083790855500012419)
                ·
                  refine ⟨23891571125686283250018629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15927714083790855500012419 23891571125686283250018629)
                  ·
                    refine ⟨4479669586066178109378493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23891571125686283250018629 4479669586066178109378493)
                    ·
                      refine ⟨1679876094774816791016935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479669586066178109378493 1679876094774816791016935)
                      ·
                        rfl

theorem cell23_3271547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 3].length) (baseStart_3271547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271547 prefixEnd_3271547 := by exact prefixLift 3271547
  have htrace : WordTrace (prefixWord ++ tailWord_3271547) baseStart_3271547 baseEnd_3271547 := by
    simpa [prefixWord, tailWord_3271547, baseEnd_3271547] using wordTrace_append hprefix tailTrace_3271547
  have hstable : (prefixWord ++ tailWord_3271547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271547).length < 2 ^ (prefixWord ++ tailWord_3271547).sum := by decide
  have hdescent : baseEnd_3271547 < baseStart_3271547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271588 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_3271588 : Nat := 118140960795 + 3271588 * 2 ^ 59
def prefixEnd_3271588 : Nat := 4983230072969 + 3 ^ 40 * 3271588 * 2
def baseEnd_3271588 : Nat := 559965715827217043534749

theorem tailTrace_3271588 : CollatzResearch.WordTrace tailWord_3271588 prefixEnd_3271588 559965715827217043534749 := by
  unfold tailWord_3271588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59662308635801446795863709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79549744847735262394484945 59662308635801446795863709)
  ·
    refine ⟨22373365738425542548448891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59662308635801446795863709 22373365738425542548448891)
    ·
      refine ⟨33560048607638313822673337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22373365738425542548448891 33560048607638313822673337)
      ·
        refine ⟨25170036455728735367005003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33560048607638313822673337 25170036455728735367005003)
        ·
          refine ⟨37755054683593103050507505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25170036455728735367005003 37755054683593103050507505)
          ·
            refine ⟨28316291012694827287880629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37755054683593103050507505 28316291012694827287880629)
            ·
              refine ⟨2654652282440140058238809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28316291012694827287880629 2654652282440140058238809)
              ·
                refine ⟨1990989211830105043679107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654652282440140058238809 1990989211830105043679107)
                ·
                  refine ⟨2986483817745157565518661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990989211830105043679107 2986483817745157565518661)
                  ·
                    refine ⟨559965715827217043534749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986483817745157565518661 559965715827217043534749)
                    ·
                      rfl

theorem cell23_3271588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_3271588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271588 prefixEnd_3271588 := by exact prefixLift 3271588
  have htrace : WordTrace (prefixWord ++ tailWord_3271588) baseStart_3271588 baseEnd_3271588 := by
    simpa [prefixWord, tailWord_3271588, baseEnd_3271588] using wordTrace_append hprefix tailTrace_3271588
  have hstable : (prefixWord ++ tailWord_3271588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271588).length < 2 ^ (prefixWord ++ tailWord_3271588).sum := by decide
  have hdescent : baseEnd_3271588 < baseStart_3271588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271614 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_3271614 : Nat := 118140960795 + 3271614 * 2 ^ 59
def prefixEnd_3271614 : Nat := 4983230072969 + 3 ^ 40 * 3271614 * 2
def baseEnd_3271614 : Nat := 559970165992889342959709

theorem tailTrace_3271614 : CollatzResearch.WordTrace tailWord_3271614 prefixEnd_3271614 559970165992889342959709 := by
  unfold tailWord_3271614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915695696188587504021737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79550377046339133354782597 14915695696188587504021737)
  ·
    refine ⟨11186771772141440628016303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14915695696188587504021737 11186771772141440628016303)
    ·
      refine ⟨16780157658212160942024455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11186771772141440628016303 16780157658212160942024455)
      ·
        refine ⟨25170236487318241413036683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780157658212160942024455 25170236487318241413036683)
        ·
          refine ⟨37755354730977362119555025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25170236487318241413036683 37755354730977362119555025)
          ·
            refine ⟨28316516048233021589666269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37755354730977362119555025 28316516048233021589666269)
            ·
              refine ⟨10618693518087383096124851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28316516048233021589666269 10618693518087383096124851)
              ·
                refine ⟨15928040277131074644187277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618693518087383096124851 15928040277131074644187277)
                ·
                  refine ⟨5973015103924152991570229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15928040277131074644187277 5973015103924152991570229)
                  ·
                    refine ⟨559970165992889342959709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973015103924152991570229 559970165992889342959709)
                    ·
                      rfl

theorem cell23_3271614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_3271614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271614 prefixEnd_3271614 := by exact prefixLift 3271614
  have htrace : WordTrace (prefixWord ++ tailWord_3271614) baseStart_3271614 baseEnd_3271614 := by
    simpa [prefixWord, tailWord_3271614, baseEnd_3271614] using wordTrace_append hprefix tailTrace_3271614
  have hstable : (prefixWord ++ tailWord_3271614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271614).length < 2 ^ (prefixWord ++ tailWord_3271614).sum := by decide
  have hdescent : baseEnd_3271614 < baseStart_3271614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271627 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 6]
def baseStart_3271627 : Nat := 118140960795 + 3271627 * 2 ^ 59
def prefixEnd_3271627 : Nat := 4983230072969 + 3 ^ 40 * 3271627 * 2
def baseEnd_3271627 : Nat := 559972391075725492672189

theorem tailTrace_3271627 : CollatzResearch.WordTrace tailWord_3271627 prefixEnd_3271627 559972391075725492672189 := by
  unfold tailWord_3271627
  simp only [CollatzResearch.WordTrace]
  refine ⟨119326039718461603252397135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79550693145641068834931423 119326039718461603252397135)
  ·
    refine ⟨178989059577692404878595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119326039718461603252397135 178989059577692404878595703)
    ·
      refine ⟨268483589366538607317893555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178989059577692404878595703 268483589366538607317893555)
      ·
        refine ⟨402725384049807910976840333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268483589366538607317893555 402725384049807910976840333)
        ·
          refine ⟨151022019018677966616315125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402725384049807910976840333 151022019018677966616315125)
          ·
            refine ⟨14158314283001059370279543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151022019018677966616315125 14158314283001059370279543)
            ·
              refine ⟨21237471424501589055419315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158314283001059370279543 21237471424501589055419315)
              ·
                refine ⟨31856207136752383583128973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21237471424501589055419315 31856207136752383583128973)
                ·
                  refine ⟨11946077676282143843673365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31856207136752383583128973 11946077676282143843673365)
                  ·
                    refine ⟨559972391075725492672189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11946077676282143843673365 559972391075725492672189)
                    ·
                      rfl

theorem cell23_3271627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_3271627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271627 prefixEnd_3271627 := by exact prefixLift 3271627
  have htrace : WordTrace (prefixWord ++ tailWord_3271627) baseStart_3271627 baseEnd_3271627 := by
    simpa [prefixWord, tailWord_3271627, baseEnd_3271627] using wordTrace_append hprefix tailTrace_3271627
  have hstable : (prefixWord ++ tailWord_3271627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271627).length < 2 ^ (prefixWord ++ tailWord_3271627).sum := by decide
  have hdescent : baseEnd_3271627 < baseStart_3271627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271628 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3271628 : Nat := 118140960795 + 3271628 * 2 ^ 59
def prefixEnd_3271628 : Nat := 4983230072969 + 3 ^ 40 * 3271628 * 2
def baseEnd_3271628 : Nat := 1679917686707830974104063

theorem tailTrace_3271628 : CollatzResearch.WordTrace tailWord_3271628 prefixEnd_3271628 1679917686707830974104063 := by
  unfold tailWord_3271628
  simp only [CollatzResearch.WordTrace]
  refine ⟨59663038095728990211591769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79550717460971986948789025 59663038095728990211591769)
  ·
    refine ⟨44747278571796742658693827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59663038095728990211591769 44747278571796742658693827)
    ·
      refine ⟨67120917857695113988040741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44747278571796742658693827 67120917857695113988040741)
      ·
        refine ⟨12585172098317833872757639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67120917857695113988040741 12585172098317833872757639)
        ·
          refine ⟨18877758147476750809136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12585172098317833872757639 18877758147476750809136459)
          ·
            refine ⟨28316637221215126213704689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18877758147476750809136459 28316637221215126213704689)
            ·
              refine ⟨21237477915911344660278517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28316637221215126213704689 21237477915911344660278517)
              ·
                refine ⟨1991013554616688561901111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21237477915911344660278517 1991013554616688561901111)
                ·
                  refine ⟨2986520331925032842851667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991013554616688561901111 2986520331925032842851667)
                  ·
                    refine ⟨4479780497887549264277501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986520331925032842851667 4479780497887549264277501)
                    ·
                      refine ⟨1679917686707830974104063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479780497887549264277501 1679917686707830974104063)
                      ·
                        rfl

theorem cell23_3271628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3271628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271628 prefixEnd_3271628 := by exact prefixLift 3271628
  have htrace : WordTrace (prefixWord ++ tailWord_3271628) baseStart_3271628 baseEnd_3271628 := by
    simpa [prefixWord, tailWord_3271628, baseEnd_3271628] using wordTrace_append hprefix tailTrace_3271628
  have hstable : (prefixWord ++ tailWord_3271628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271628).length < 2 ^ (prefixWord ++ tailWord_3271628).sum := by decide
  have hdescent : baseEnd_3271628 < baseStart_3271628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271631 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 1, 5]
def baseStart_3271631 : Nat := 118140960795 + 3271631 * 2 ^ 59
def prefixEnd_3271631 : Nat := 4983230072969 + 3 ^ 40 * 3271631 * 2
def baseEnd_3271631 : Nat := 559973075716598154122183

theorem tailTrace_3271631 : CollatzResearch.WordTrace tailWord_3271631 prefixEnd_3271631 559973075716598154122183 := by
  unfold tailWord_3271631
  simp only [CollatzResearch.WordTrace]
  refine ⟨119326185610447111935542747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79550790406964741290361831 119326185610447111935542747)
  ·
    refine ⟨178989278415670667903314121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119326185610447111935542747 178989278415670667903314121)
    ·
      refine ⟨134241958811753000927485591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178989278415670667903314121 134241958811753000927485591)
      ·
        refine ⟨201362938217629501391228387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134241958811753000927485591 201362938217629501391228387)
        ·
          refine ⟨302044407326444252086842581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201362938217629501391228387 302044407326444252086842581)
          ·
            refine ⟨7079165796713537158285373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 302044407326444252086842581 7079165796713537158285373)
            ·
              refine ⟨2654687173767576434357015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7079165796713537158285373 2654687173767576434357015)
              ·
                refine ⟨3982030760651364651535523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654687173767576434357015 3982030760651364651535523)
                ·
                  refine ⟨5973046140977046977303285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982030760651364651535523 5973046140977046977303285)
                  ·
                    refine ⟨559973075716598154122183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973046140977046977303285 559973075716598154122183)
                    ·
                      rfl

theorem cell23_3271631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_3271631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271631 prefixEnd_3271631 := by exact prefixLift 3271631
  have htrace : WordTrace (prefixWord ++ tailWord_3271631) baseStart_3271631 baseEnd_3271631 := by
    simpa [prefixWord, tailWord_3271631, baseEnd_3271631] using wordTrace_append hprefix tailTrace_3271631
  have hstable : (prefixWord ++ tailWord_3271631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271631).length < 2 ^ (prefixWord ++ tailWord_3271631).sum := by decide
  have hdescent : baseEnd_3271631 < baseStart_3271631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271645 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_3271645 : Nat := 118140960795 + 3271645 * 2 ^ 59
def prefixEnd_3271645 : Nat := 4983230072969 + 3 ^ 40 * 3271645 * 2
def baseEnd_3271645 : Nat := 1679926415878957407591485

theorem tailTrace_3271645 : CollatzResearch.WordTrace tailWord_3271645 prefixEnd_3271645 1679926415878957407591485 := by
  unfold tailWord_3271645
  simp only [CollatzResearch.WordTrace]
  refine ⟨119326696232396392326552389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79551130821597594884368259 119326696232396392326552389)
  ·
    refine ⟨22373755543574323561228573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119326696232396392326552389 22373755543574323561228573)
    ·
      refine ⟨8390158328840371335460715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22373755543574323561228573 8390158328840371335460715)
      ·
        refine ⟨12585237493260557003191073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8390158328840371335460715 12585237493260557003191073)
        ·
          refine ⟨9438928119945417752393305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12585237493260557003191073 9438928119945417752393305)
          ·
            refine ⟨7079196089959063314294979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438928119945417752393305 7079196089959063314294979)
            ·
              refine ⟨10618794134938594971442469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079196089959063314294979 10618794134938594971442469)
              ·
                refine ⟨1991023900300986557145463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10618794134938594971442469 1991023900300986557145463)
                ·
                  refine ⟨2986535850451479835718195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991023900300986557145463 2986535850451479835718195)
                  ·
                    refine ⟨4479803775677219753577293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986535850451479835718195 4479803775677219753577293)
                    ·
                      refine ⟨1679926415878957407591485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479803775677219753577293 1679926415878957407591485)
                      ·
                        rfl

theorem cell23_3271645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_3271645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271645 prefixEnd_3271645 := by exact prefixLift 3271645
  have htrace : WordTrace (prefixWord ++ tailWord_3271645) baseStart_3271645 baseEnd_3271645 := by
    simpa [prefixWord, tailWord_3271645, baseEnd_3271645] using wordTrace_append hprefix tailTrace_3271645
  have hstable : (prefixWord ++ tailWord_3271645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271645).length < 2 ^ (prefixWord ++ tailWord_3271645).sum := by decide
  have hdescent : baseEnd_3271645 < baseStart_3271645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271682 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3271682 : Nat := 118140960795 + 3271682 * 2 ^ 59
def prefixEnd_3271682 : Nat := 4983230072969 + 3 ^ 40 * 3271682 * 2
def baseEnd_3271682 : Nat := 559981804887724587609605

theorem tailTrace_3271682 : CollatzResearch.WordTrace tailWord_3271682 prefixEnd_3271682 559981804887724587609605 := by
  unfold tailWord_3271682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29832011433315586911412325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79552030488841565097099533 29832011433315586911412325)
  ·
    refine ⟨5593502143746672545889811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29832011433315586911412325 5593502143746672545889811)
    ·
      refine ⟨8390253215620008818834717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5593502143746672545889811 8390253215620008818834717)
      ·
        refine ⟨3146344955857503307063019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8390253215620008818834717 3146344955857503307063019)
        ·
          refine ⟨4719517433786254960594529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146344955857503307063019 4719517433786254960594529)
          ·
            refine ⟨3539638075339691220445897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719517433786254960594529 3539638075339691220445897)
            ·
              refine ⟨2654728556504768415334423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539638075339691220445897 2654728556504768415334423)
              ·
                refine ⟨3982092834757152623001635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654728556504768415334423 3982092834757152623001635)
                ·
                  refine ⟨5973139252135728934502453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982092834757152623001635 5973139252135728934502453)
                  ·
                    refine ⟨559981804887724587609605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973139252135728934502453 559981804887724587609605)
                    ·
                      rfl

theorem cell23_3271682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3271682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271682 prefixEnd_3271682 := by exact prefixLift 3271682
  have htrace : WordTrace (prefixWord ++ tailWord_3271682) baseStart_3271682 baseEnd_3271682 := by
    simpa [prefixWord, tailWord_3271682, baseEnd_3271682] using wordTrace_append hprefix tailTrace_3271682
  have hstable : (prefixWord ++ tailWord_3271682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271682).length < 2 ^ (prefixWord ++ tailWord_3271682).sum := by decide
  have hdescent : baseEnd_3271682 < baseStart_3271682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271685 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_3271685 : Nat := 118140960795 + 3271685 * 2 ^ 59
def prefixEnd_3271685 : Nat := 4983230072969 + 3 ^ 40 * 3271685 * 2
def baseEnd_3271685 : Nat := 1679946955105137251091301

theorem tailTrace_3271685 : CollatzResearch.WordTrace tailWord_3271685 prefixEnd_3271685 1679946955105137251091301 := by
  unfold tailWord_3271685
  simp only [CollatzResearch.WordTrace]
  refine ⟨119328155152251479158008509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79552103434834319438672339 119328155152251479158008509)
  ·
    refine ⟨44748058182094304684253191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119328155152251479158008509 44748058182094304684253191)
    ·
      refine ⟨67122087273141457026379787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44748058182094304684253191 67122087273141457026379787)
      ·
        refine ⟨100683130909712185539569681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67122087273141457026379787 100683130909712185539569681)
        ·
          refine ⟨75512348182284139154677261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100683130909712185539569681 75512348182284139154677261)
          ·
            refine ⟨28317130568356552183003973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75512348182284139154677261 28317130568356552183003973)
            ·
              refine ⟨5309461981566853534313245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28317130568356552183003973 5309461981566853534313245)
              ·
                refine ⟨1991048243087570075367467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5309461981566853534313245 1991048243087570075367467)
                ·
                  refine ⟨2986572364631355113051201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991048243087570075367467 2986572364631355113051201)
                  ·
                    refine ⟨2239929273473516334788401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2986572364631355113051201 2239929273473516334788401)
                    ·
                      refine ⟨1679946955105137251091301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239929273473516334788401 1679946955105137251091301)
                      ·
                        rfl

theorem cell23_3271685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_3271685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271685 prefixEnd_3271685 := by exact prefixLift 3271685
  have htrace : WordTrace (prefixWord ++ tailWord_3271685) baseStart_3271685 baseEnd_3271685 := by
    simpa [prefixWord, tailWord_3271685, baseEnd_3271685] using wordTrace_append hprefix tailTrace_3271685
  have hstable : (prefixWord ++ tailWord_3271685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271685).length < 2 ^ (prefixWord ++ tailWord_3271685).sum := by decide
  have hdescent : baseEnd_3271685 < baseStart_3271685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271688 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_3271688 : Nat := 118140960795 + 3271688 * 2 ^ 59
def prefixEnd_3271688 : Nat := 4983230072969 + 3 ^ 40 * 3271688 * 2
def baseEnd_3271688 : Nat := 1679948495547100739353787

theorem tailTrace_3271688 : CollatzResearch.WordTrace tailWord_3271688 prefixEnd_3271688 1679948495547100739353787 := by
  unfold tailWord_3271688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59664132285620305335183859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79552176380827073780245145 59664132285620305335183859)
  ·
    refine ⟨89496198428430458002775789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59664132285620305335183859 89496198428430458002775789)
    ·
      refine ⟨33561074410661421751040921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89496198428430458002775789 33561074410661421751040921)
      ·
        refine ⟨25170805807996066313280691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33561074410661421751040921 25170805807996066313280691)
        ·
          refine ⟨37756208711994099469921037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25170805807996066313280691 37756208711994099469921037)
          ·
            refine ⟨14158578266997787301220389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37756208711994099469921037 14158578266997787301220389)
            ·
              refine ⟨2654733425062085118978823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14158578266997787301220389 2654733425062085118978823)
              ·
                refine ⟨3982100137593127678468235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654733425062085118978823 3982100137593127678468235)
                ·
                  refine ⟨5973150206389691517702353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982100137593127678468235 5973150206389691517702353)
                  ·
                    refine ⟨4479862654792268638276765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5973150206389691517702353 4479862654792268638276765)
                    ·
                      refine ⟨1679948495547100739353787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4479862654792268638276765 1679948495547100739353787)
                      ·
                        rfl

theorem cell23_3271688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_3271688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271688 prefixEnd_3271688 := by exact prefixLift 3271688
  have htrace : WordTrace (prefixWord ++ tailWord_3271688) baseStart_3271688 baseEnd_3271688 := by
    simpa [prefixWord, tailWord_3271688, baseEnd_3271688] using wordTrace_append hprefix tailTrace_3271688
  have hstable : (prefixWord ++ tailWord_3271688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271688).length < 2 ^ (prefixWord ++ tailWord_3271688).sum := by decide
  have hdescent : baseEnd_3271688 < baseStart_3271688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271728 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2]
def baseStart_3271728 : Nat := 118140960795 + 3271728 * 2 ^ 59
def prefixEnd_3271728 : Nat := 4983230072969 + 3 ^ 40 * 3271728 * 2
def baseEnd_3271728 : Nat := 1679969034773280582853603

theorem tailTrace_3271728 : CollatzResearch.WordTrace tailWord_3271728 prefixEnd_3271728 1679969034773280582853603 := by
  unfold tailWord_3271728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59664861745547848750911919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79553148994063798334549225 59664861745547848750911919)
  ·
    refine ⟨89497292618321773126367879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59664861745547848750911919 89497292618321773126367879)
    ·
      refine ⟨134245938927482659689551819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89497292618321773126367879 134245938927482659689551819)
      ·
        refine ⟨201368908391223989534327729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134245938927482659689551819 201368908391223989534327729)
        ·
          refine ⟨151026681293417992150745797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201368908391223989534327729 151026681293417992150745797)
          ·
            refine ⟨28317502742515873528264837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151026681293417992150745797 28317502742515873528264837)
            ·
              refine ⟨5309531764221726286549657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28317502742515873528264837 5309531764221726286549657)
              ·
                refine ⟨3982148823166294714912243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309531764221726286549657 3982148823166294714912243)
                ·
                  refine ⟨5973223234749442072368365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982148823166294714912243 5973223234749442072368365)
                  ·
                    refine ⟨2239958713031040777138137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5973223234749442072368365 2239958713031040777138137)
                    ·
                      refine ⟨1679969034773280582853603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239958713031040777138137 1679969034773280582853603)
                      ·
                        rfl

theorem cell23_3271728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2].length) (baseStart_3271728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271728 prefixEnd_3271728 := by exact prefixLift 3271728
  have htrace : WordTrace (prefixWord ++ tailWord_3271728) baseStart_3271728 baseEnd_3271728 := by
    simpa [prefixWord, tailWord_3271728, baseEnd_3271728] using wordTrace_append hprefix tailTrace_3271728
  have hstable : (prefixWord ++ tailWord_3271728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271728).length < 2 ^ (prefixWord ++ tailWord_3271728).sum := by decide
  have hdescent : baseEnd_3271728 < baseStart_3271728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271744 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_3271744 : Nat := 118140960795 + 3271744 * 2 ^ 59
def prefixEnd_3271744 : Nat := 4983230072969 + 3 ^ 40 * 3271744 * 2
def baseEnd_3271744 : Nat := 1679977250463752520253529

theorem tailTrace_3271744 : CollatzResearch.WordTrace tailWord_3271744 prefixEnd_3271744 1679977250463752520253529 := by
  unfold tailWord_3271744
  simp only [CollatzResearch.WordTrace]
  refine ⟨59665153529518866117203143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79553538039358488156270857 59665153529518866117203143)
  ·
    refine ⟨89497730294278299175804715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59665153529518866117203143 89497730294278299175804715)
    ·
      refine ⟨134246595441417448763707073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89497730294278299175804715 134246595441417448763707073)
      ·
        refine ⟨100684946581063086572780305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134246595441417448763707073 100684946581063086572780305)
        ·
          refine ⟨75513709935797314929585229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100684946581063086572780305 75513709935797314929585229)
          ·
            refine ⟨28317641225923993098594461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75513709935797314929585229 28317641225923993098594461)
            ·
              refine ⟨10619115459721497411972923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28317641225923993098594461 10619115459721497411972923)
              ·
                refine ⟨15928673189582246117959385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619115459721497411972923 15928673189582246117959385)
                ·
                  refine ⟨11946504892186684588469539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15928673189582246117959385 11946504892186684588469539)
                  ·
                    refine ⟨17919757338280026882704309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11946504892186684588469539 17919757338280026882704309)
                    ·
                      refine ⟨1679977250463752520253529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17919757338280026882704309 1679977250463752520253529)
                      ·
                        rfl

theorem cell23_3271744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_3271744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271744 prefixEnd_3271744 := by exact prefixLift 3271744
  have htrace : WordTrace (prefixWord ++ tailWord_3271744) baseStart_3271744 baseEnd_3271744 := by
    simpa [prefixWord, tailWord_3271744, baseEnd_3271744] using wordTrace_append hprefix tailTrace_3271744
  have hstable : (prefixWord ++ tailWord_3271744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271744).length < 2 ^ (prefixWord ++ tailWord_3271744).sum := by decide
  have hdescent : baseEnd_3271744 < baseStart_3271744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271754 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3271754 : Nat := 118140960795 + 3271754 * 2 ^ 59
def prefixEnd_3271754 : Nat := 4983230072969 + 3 ^ 40 * 3271754 * 2
def baseEnd_3271754 : Nat := 1679982385270297481128483

theorem tailTrace_3271754 : CollatzResearch.WordTrace tailWord_3271754 prefixEnd_3271754 1679982385270297481128483 := by
  unfold tailWord_3271754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29832667947250375985567579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79553781192667669294846877 29832667947250375985567579)
  ·
    refine ⟨44749001920875563978351369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29832667947250375985567579 44749001920875563978351369)
    ·
      refine ⟨33561751440656672983763527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44749001920875563978351369 33561751440656672983763527)
      ·
        refine ⟨50342627160985009475645291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33561751440656672983763527 50342627160985009475645291)
        ·
          refine ⟨75513940741477514213467937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50342627160985009475645291 75513940741477514213467937)
          ·
            refine ⟨56635455556108135660100953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75513940741477514213467937 56635455556108135660100953)
            ·
              refine ⟨42476591667081101745075715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56635455556108135660100953 42476591667081101745075715)
              ·
                refine ⟨63714887500621652617613573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42476591667081101745075715 63714887500621652617613573)
                ·
                  refine ⟨11946541406366559865802545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63714887500621652617613573 11946541406366559865802545)
                  ·
                    refine ⟨8959906054774919899351909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11946541406366559865802545 8959906054774919899351909)
                    ·
                      refine ⟨1679982385270297481128483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8959906054774919899351909 1679982385270297481128483)
                      ·
                        rfl

theorem cell23_3271754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3271754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271754 prefixEnd_3271754 := by exact prefixLift 3271754
  have htrace : WordTrace (prefixWord ++ tailWord_3271754) baseStart_3271754 baseEnd_3271754 := by
    simpa [prefixWord, tailWord_3271754, baseEnd_3271754] using wordTrace_append hprefix tailTrace_3271754
  have hstable : (prefixWord ++ tailWord_3271754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271754).length < 2 ^ (prefixWord ++ tailWord_3271754).sum := by decide
  have hdescent : baseEnd_3271754 < baseStart_3271754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271758 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_3271758 : Nat := 118140960795 + 3271758 * 2 ^ 59
def prefixEnd_3271758 : Nat := 4983230072969 + 3 ^ 40 * 3271758 * 2
def baseEnd_3271758 : Nat := 1679984439192915465478465

theorem tailTrace_3271758 : CollatzResearch.WordTrace tailWord_3271758 prefixEnd_3271758 1679984439192915465478465 := by
  unfold tailWord_3271758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916352210123376578176991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79553878453991341750277285 14916352210123376578176991)
  ·
    refine ⟨22374528315185064867265487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14916352210123376578176991 22374528315185064867265487)
    ·
      refine ⟨33561792472777597300898231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22374528315185064867265487 33561792472777597300898231)
      ·
        refine ⟨50342688709166395951347347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33561792472777597300898231 50342688709166395951347347)
        ·
          refine ⟨75514033063749593927021021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50342688709166395951347347 75514033063749593927021021)
          ·
            refine ⟨28317762398906097722632883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75514033063749593927021021 28317762398906097722632883)
            ·
              refine ⟨42476643598359146583949325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28317762398906097722632883 42476643598359146583949325)
              ·
                refine ⟨15928741349384679968980997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42476643598359146583949325 15928741349384679968980997)
                ·
                  refine ⟨2986639003009627494183937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15928741349384679968980997 2986639003009627494183937)
                  ·
                    refine ⟨2239979252257220620637953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2986639003009627494183937 2239979252257220620637953)
                    ·
                      refine ⟨1679984439192915465478465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2239979252257220620637953 1679984439192915465478465)
                      ·
                        rfl

theorem cell23_3271758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_3271758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271758 prefixEnd_3271758 := by exact prefixLift 3271758
  have htrace : WordTrace (prefixWord ++ tailWord_3271758) baseStart_3271758 baseEnd_3271758 := by
    simpa [prefixWord, tailWord_3271758, baseEnd_3271758] using wordTrace_append hprefix tailTrace_3271758
  have hstable : (prefixWord ++ tailWord_3271758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271758).length < 2 ^ (prefixWord ++ tailWord_3271758).sum := by decide
  have hdescent : baseEnd_3271758 < baseStart_3271758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271798 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3271798 : Nat := 118140960795 + 3271798 * 2 ^ 59
def prefixEnd_3271798 : Nat := 4983230072969 + 3 ^ 40 * 3271798 * 2
def baseEnd_3271798 : Nat := 186667219824343923219809

theorem tailTrace_3271798 : CollatzResearch.WordTrace tailWord_3271798 prefixEnd_3271798 186667219824343923219809 := by
  unfold tailWord_3271798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458267287552631216054503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79554851067228066304581365 7458267287552631216054503)
  ·
    refine ⟨11187400931328946824081755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7458267287552631216054503 11187400931328946824081755)
    ·
      refine ⟨16781101396993420236122633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187400931328946824081755 16781101396993420236122633)
      ·
        refine ⟨12585826047745065177091975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16781101396993420236122633 12585826047745065177091975)
        ·
          refine ⟨18878739071617597765637963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12585826047745065177091975 18878739071617597765637963)
          ·
            refine ⟨28318108607426396648456945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18878739071617597765637963 28318108607426396648456945)
            ·
              refine ⟨21238581455569797486342709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28318108607426396648456945 21238581455569797486342709)
              ·
                refine ⟨1991117011459668514344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21238581455569797486342709 1991117011459668514344629)
                ·
                  refine ⟨186667219824343923219809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991117011459668514344629 186667219824343923219809)
                  ·
                    rfl

theorem cell23_3271798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3271798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271798 prefixEnd_3271798 := by exact prefixLift 3271798
  have htrace : WordTrace (prefixWord ++ tailWord_3271798) baseStart_3271798 baseEnd_3271798 := by
    simpa [prefixWord, tailWord_3271798, baseEnd_3271798] using wordTrace_append hprefix tailTrace_3271798
  have hstable : (prefixWord ++ tailWord_3271798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271798).length < 2 ^ (prefixWord ++ tailWord_3271798).sum := by decide
  have hdescent : baseEnd_3271798 < baseStart_3271798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271804 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3271804 : Nat := 118140960795 + 3271804 * 2 ^ 59
def prefixEnd_3271804 : Nat := 4983230072969 + 3 ^ 40 * 3271804 * 2
def baseEnd_3271804 : Nat := 1680008059303022285503253

theorem tailTrace_3271804 : CollatzResearch.WordTrace tailWord_3271804 prefixEnd_3271804 1680008059303022285503253 := by
  unfold tailWord_3271804
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666247719410181240795233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79554996959213574987726977 59666247719410181240795233)
  ·
    refine ⟨44749685789557635930596425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59666247719410181240795233 44749685789557635930596425)
    ·
      refine ⟨33562264342168226947947319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44749685789557635930596425 33562264342168226947947319)
      ·
        refine ⟨50343396513252340421920979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33562264342168226947947319 50343396513252340421920979)
        ·
          refine ⟨75515094769878510632881469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50343396513252340421920979 75515094769878510632881469)
          ·
            refine ⟨28318160538704441487330551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75515094769878510632881469 28318160538704441487330551)
            ·
              refine ⟨42477240808056662230995827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28318160538704441487330551 42477240808056662230995827)
              ·
                refine ⟨63715861212084993346493741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42477240808056662230995827 63715861212084993346493741)
                ·
                  refine ⟨23893447954531872504935153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63715861212084993346493741 23893447954531872504935153)
                  ·
                    refine ⟨17920085965898904378701365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23893447954531872504935153 17920085965898904378701365)
                    ·
                      refine ⟨1680008059303022285503253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17920085965898904378701365 1680008059303022285503253)
                      ·
                        rfl

theorem cell23_3271804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3271804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271804 prefixEnd_3271804 := by exact prefixLift 3271804
  have htrace : WordTrace (prefixWord ++ tailWord_3271804) baseStart_3271804 baseEnd_3271804 := by
    simpa [prefixWord, tailWord_3271804, baseEnd_3271804] using wordTrace_append hprefix tailTrace_3271804
  have hstable : (prefixWord ++ tailWord_3271804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271804).length < 2 ^ (prefixWord ++ tailWord_3271804).sum := by decide
  have hdescent : baseEnd_3271804 < baseStart_3271804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271871 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 6]
def baseStart_3271871 : Nat := 118140960795 + 3271871 * 2 ^ 59
def prefixEnd_3271871 : Nat := 4983230072969 + 3 ^ 40 * 3271871 * 2
def baseEnd_3271871 : Nat := 186671384722985947040605

theorem tailTrace_3271871 : CollatzResearch.WordTrace tailWord_3271871 prefixEnd_3271871 186671384722985947040605 := by
  unfold tailWord_3271871
  simp only [CollatzResearch.WordTrace]
  refine ⟨119334939129577632924279467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79556626086385088616186311 119334939129577632924279467)
  ·
    refine ⟨179002408694366449386419201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119334939129577632924279467 179002408694366449386419201)
    ·
      refine ⟨134251806520774837039814401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179002408694366449386419201 134251806520774837039814401)
      ·
        refine ⟨100688854890581127779860801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134251806520774837039814401 100688854890581127779860801)
        ·
          refine ⟨75516641167935845834895601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100688854890581127779860801 75516641167935845834895601)
          ·
            refine ⟨56637480875951884376171701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75516641167935845834895601 56637480875951884376171701)
            ·
              refine ⟨5309763832120489160266097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56637480875951884376171701 5309763832120489160266097)
              ·
                refine ⟨3982322874090366870199573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309763832120489160266097 3982322874090366870199573)
                ·
                  refine ⟨186671384722985947040605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3982322874090366870199573 186671384722985947040605)
                  ·
                    rfl

theorem cell23_3271871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 6].length) (baseStart_3271871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271871 prefixEnd_3271871 := by exact prefixLift 3271871
  have htrace : WordTrace (prefixWord ++ tailWord_3271871) baseStart_3271871 baseEnd_3271871 := by
    simpa [prefixWord, tailWord_3271871, baseEnd_3271871] using wordTrace_append hprefix tailTrace_3271871
  have hstable : (prefixWord ++ tailWord_3271871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271871).length < 2 ^ (prefixWord ++ tailWord_3271871).sum := by decide
  have hdescent : baseEnd_3271871 < baseStart_3271871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271908 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_3271908 : Nat := 118140960795 + 3271908 * 2 ^ 59
def prefixEnd_3271908 : Nat := 4983230072969 + 3 ^ 40 * 3271908 * 2
def baseEnd_3271908 : Nat := 1680061461291089878602775

theorem tailTrace_3271908 : CollatzResearch.WordTrace tailWord_3271908 prefixEnd_3271908 1680061461291089878602775 := by
  unfold tailWord_3271908
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668144315221794121688189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79557525753629058828917585 59668144315221794121688189)
  ·
    refine ⟨22375554118208172795633071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59668144315221794121688189 22375554118208172795633071)
    ·
      refine ⟨33563331177312259193449607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22375554118208172795633071 33563331177312259193449607)
      ·
        refine ⟨50344996765968388790174411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33563331177312259193449607 50344996765968388790174411)
        ·
          refine ⟨75517495148952583185261617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50344996765968388790174411 75517495148952583185261617)
          ·
            refine ⟨56638121361714437388946213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75517495148952583185261617 56638121361714437388946213)
            ·
              refine ⟨10619647755321457010427415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56638121361714437388946213 10619647755321457010427415)
              ·
                refine ⟨15929471632982185515641123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10619647755321457010427415 15929471632982185515641123)
                ·
                  refine ⟨23894207449473278273461685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15929471632982185515641123 23894207449473278273461685)
                  ·
                    refine ⟨2240081948388119838137033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23894207449473278273461685 2240081948388119838137033)
                    ·
                      refine ⟨1680061461291089878602775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240081948388119838137033 1680061461291089878602775)
                      ·
                        rfl

theorem cell23_3271908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_3271908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271908 prefixEnd_3271908 := by exact prefixLift 3271908
  have htrace : WordTrace (prefixWord ++ tailWord_3271908) baseStart_3271908 baseEnd_3271908 := by
    simpa [prefixWord, tailWord_3271908, baseEnd_3271908] using wordTrace_append hprefix tailTrace_3271908
  have hstable : (prefixWord ++ tailWord_3271908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271908).length < 2 ^ (prefixWord ++ tailWord_3271908).sum := by decide
  have hdescent : baseEnd_3271908 < baseStart_3271908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271909 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_3271909 : Nat := 118140960795 + 3271909 * 2 ^ 59
def prefixEnd_3271909 : Nat := 4983230072969 + 3 ^ 40 * 3271909 * 2
def baseEnd_3271909 : Nat := 560020658257248124896757

theorem tailTrace_3271909 : CollatzResearch.WordTrace tailWord_3271909 prefixEnd_3271909 560020658257248124896757 := by
  unfold tailWord_3271909
  simp only [CollatzResearch.WordTrace]
  refine ⟨119336325103439965414162781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79557550068959976942775187 119336325103439965414162781)
  ·
    refine ⟨44751121913789987030311043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119336325103439965414162781 44751121913789987030311043)
    ·
      refine ⟨67126682870684980545466565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44751121913789987030311043 67126682870684980545466565)
      ·
        refine ⟨12586253038253433852274981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67126682870684980545466565 12586253038253433852274981)
        ·
          refine ⟨2359922444672518847301559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12586253038253433852274981 2359922444672518847301559)
          ·
            refine ⟨3539883667008778270952339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359922444672518847301559 3539883667008778270952339)
            ·
              refine ⟨5309825500513167406428509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539883667008778270952339 5309825500513167406428509)
              ·
                refine ⟨1991184562692437777410691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5309825500513167406428509 1991184562692437777410691)
                ·
                  refine ⟨2986776844038656666116037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991184562692437777410691 2986776844038656666116037)
                  ·
                    refine ⟨560020658257248124896757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2986776844038656666116037 560020658257248124896757)
                    ·
                      rfl

theorem cell23_3271909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_3271909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271909 prefixEnd_3271909 := by exact prefixLift 3271909
  have htrace : WordTrace (prefixWord ++ tailWord_3271909) baseStart_3271909 baseEnd_3271909 := by
    simpa [prefixWord, tailWord_3271909, baseEnd_3271909] using wordTrace_append hprefix tailTrace_3271909
  have hstable : (prefixWord ++ tailWord_3271909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271909).length < 2 ^ (prefixWord ++ tailWord_3271909).sum := by decide
  have hdescent : baseEnd_3271909 < baseStart_3271909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271918 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3271918 : Nat := 118140960795 + 3271918 * 2 ^ 59
def prefixEnd_3271918 : Nat := 4983230072969 + 3 ^ 40 * 3271918 * 2
def baseEnd_3271918 : Nat := 560022198699211613159243

theorem tailTrace_3271918 : CollatzResearch.WordTrace tailWord_3271918 prefixEnd_3271918 560022198699211613159243 := by
  unfold tailWord_3271918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14917081670050919993905051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79557768906938239967493605 14917081670050919993905051)
  ·
    refine ⟨22375622505076379990857577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14917081670050919993905051 22375622505076379990857577)
    ·
      refine ⟨16781716878807284993143183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22375622505076379990857577 16781716878807284993143183)
      ·
        refine ⟨25172575318210927489714775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781716878807284993143183 25172575318210927489714775)
        ·
          refine ⟨37758862977316391234572163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25172575318210927489714775 37758862977316391234572163)
          ·
            refine ⟨56638294465974586851858245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37758862977316391234572163 56638294465974586851858245)
            ·
              refine ⟨10619680212370235034723421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56638294465974586851858245 10619680212370235034723421)
              ·
                refine ⟨3982380079638838138021283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10619680212370235034723421 3982380079638838138021283)
                ·
                  refine ⟨5973570119458257207031925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982380079638838138021283 5973570119458257207031925)
                  ·
                    refine ⟨560022198699211613159243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973570119458257207031925 560022198699211613159243)
                    ·
                      rfl

theorem cell23_3271918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3271918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271918 prefixEnd_3271918 := by exact prefixLift 3271918
  have htrace : WordTrace (prefixWord ++ tailWord_3271918) baseStart_3271918 baseEnd_3271918 := by
    simpa [prefixWord, tailWord_3271918, baseEnd_3271918] using wordTrace_append hprefix tailTrace_3271918
  have hstable : (prefixWord ++ tailWord_3271918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271918).length < 2 ^ (prefixWord ++ tailWord_3271918).sum := by decide
  have hdescent : baseEnd_3271918 < baseStart_3271918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271921 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3271921 : Nat := 118140960795 + 3271921 * 2 ^ 59
def prefixEnd_3271921 : Nat := 4983230072969 + 3 ^ 40 * 3271921 * 2
def baseEnd_3271921 : Nat := 1680068136539598327740215

theorem tailTrace_3271921 : CollatzResearch.WordTrace tailWord_3271921 prefixEnd_3271921 1680068136539598327740215 := by
  unfold tailWord_3271921
  simp only [CollatzResearch.WordTrace]
  refine ⟨119336762779396491463599617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79557841852930994309066411 119336762779396491463599617)
  ·
    refine ⟨89502572084547368597699713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119336762779396491463599617 89502572084547368597699713)
    ·
      refine ⟨67126929063410526448274785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89502572084547368597699713 67126929063410526448274785)
      ·
        refine ⟨50345196797557894836206089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67126929063410526448274785 50345196797557894836206089)
        ·
          refine ⟨37758897598168421127154567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50345196797557894836206089 37758897598168421127154567)
          ·
            refine ⟨56638346397252631690731851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37758897598168421127154567 56638346397252631690731851)
            ·
              refine ⟨84957519595878947536097777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56638346397252631690731851 84957519595878947536097777)
              ·
                refine ⟨63718139696909210652073333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84957519595878947536097777 63718139696909210652073333)
                ·
                  refine ⟨5973575596585238498631875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63718139696909210652073333 5973575596585238498631875)
                  ·
                    refine ⟨8960363394877857747947813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973575596585238498631875 8960363394877857747947813)
                    ·
                      refine ⟨1680068136539598327740215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8960363394877857747947813 1680068136539598327740215)
                      ·
                        rfl

theorem cell23_3271921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3271921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271921 prefixEnd_3271921 := by exact prefixLift 3271921
  have htrace : WordTrace (prefixWord ++ tailWord_3271921) baseStart_3271921 baseEnd_3271921 := by
    simpa [prefixWord, tailWord_3271921, baseEnd_3271921] using wordTrace_append hprefix tailTrace_3271921
  have hstable : (prefixWord ++ tailWord_3271921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271921).length < 2 ^ (prefixWord ++ tailWord_3271921).sum := by decide
  have hdescent : baseEnd_3271921 < baseStart_3271921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271932 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3271932 : Nat := 118140960795 + 3271932 * 2 ^ 59
def prefixEnd_3271932 : Nat := 4983230072969 + 3 ^ 40 * 3271932 * 2
def baseEnd_3271932 : Nat := 1680073784826797784702665

theorem tailTrace_3271932 : CollatzResearch.WordTrace tailWord_3271932 prefixEnd_3271932 1680073784826797784702665 := by
  unfold tailWord_3271932
  simp only [CollatzResearch.WordTrace]
  refine ⟨59668581991178320171125025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79558109321571093561500033 59668581991178320171125025)
  ·
    refine ⟨44751436493383740128343769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59668581991178320171125025 44751436493383740128343769)
    ·
      refine ⟨33563577370037805096257827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44751436493383740128343769 33563577370037805096257827)
      ·
        refine ⟨50345366055056707644386741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33563577370037805096257827 50345366055056707644386741)
        ·
          refine ⟨4719878067661566341661257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50345366055056707644386741 4719878067661566341661257)
          ·
            refine ⟨3539908550746174756245943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719878067661566341661257 3539908550746174756245943)
            ·
              refine ⟨5309862826119262134368915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539908550746174756245943 5309862826119262134368915)
              ·
                refine ⟨7964794239178893201553373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309862826119262134368915 7964794239178893201553373)
                ·
                  refine ⟨2986797839692084950582515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7964794239178893201553373 2986797839692084950582515)
                  ·
                    refine ⟨4480196759538127425873773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986797839692084950582515 4480196759538127425873773)
                    ·
                      refine ⟨1680073784826797784702665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480196759538127425873773 1680073784826797784702665)
                      ·
                        rfl

theorem cell23_3271932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3271932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271932 prefixEnd_3271932 := by exact prefixLift 3271932
  have htrace : WordTrace (prefixWord ++ tailWord_3271932) baseStart_3271932 baseEnd_3271932 := by
    simpa [prefixWord, tailWord_3271932, baseEnd_3271932] using wordTrace_append hprefix tailTrace_3271932
  have hstable : (prefixWord ++ tailWord_3271932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271932).length < 2 ^ (prefixWord ++ tailWord_3271932).sum := by decide
  have hdescent : baseEnd_3271932 < baseStart_3271932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271941 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_3271941 : Nat := 118140960795 + 3271941 * 2 ^ 59
def prefixEnd_3271941 : Nat := 4983230072969 + 3 ^ 40 * 3271941 * 2
def baseEnd_3271941 : Nat := 1680078406152688249490123

theorem tailTrace_3271941 : CollatzResearch.WordTrace tailWord_3271941 prefixEnd_3271941 1680078406152688249490123 := by
  unfold tailWord_3271941
  simp only [CollatzResearch.WordTrace]
  refine ⟨119337492239324034879327677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79558328159549356586218451 119337492239324034879327677)
  ·
    refine ⟨44751559589746513079747879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119337492239324034879327677 44751559589746513079747879)
    ·
      refine ⟨67127339384619769619621819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44751559589746513079747879 67127339384619769619621819)
      ·
        refine ⟨100691009076929654429432729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67127339384619769619621819 100691009076929654429432729)
        ·
          refine ⟨75518256807697240822074547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100691009076929654429432729 75518256807697240822074547)
          ·
            refine ⟨113277385211545861233111821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75518256807697240822074547 113277385211545861233111821)
            ·
              refine ⟨42479019454329697962416933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113277385211545861233111821 42479019454329697962416933)
              ·
                refine ⟨7964816147686818367953175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42479019454329697962416933 7964816147686818367953175)
                ·
                  refine ⟨11947224221530227551929763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964816147686818367953175 11947224221530227551929763)
                  ·
                    refine ⟨17920836332295341327894645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11947224221530227551929763 17920836332295341327894645)
                    ·
                      refine ⟨1680078406152688249490123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17920836332295341327894645 1680078406152688249490123)
                      ·
                        rfl

theorem cell23_3271941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_3271941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271941 prefixEnd_3271941 := by exact prefixLift 3271941
  have htrace : WordTrace (prefixWord ++ tailWord_3271941) baseStart_3271941 baseEnd_3271941 := by
    simpa [prefixWord, tailWord_3271941, baseEnd_3271941] using wordTrace_append hprefix tailTrace_3271941
  have hstable : (prefixWord ++ tailWord_3271941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271941).length < 2 ^ (prefixWord ++ tailWord_3271941).sum := by decide
  have hdescent : baseEnd_3271941 < baseStart_3271941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271989 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_3271989 : Nat := 118140960795 + 3271989 * 2 ^ 59
def prefixEnd_3271989 : Nat := 4983230072969 + 3 ^ 40 * 3271989 * 2
def baseEnd_3271989 : Nat := 1680103053224104061689903

theorem tailTrace_3271989 : CollatzResearch.WordTrace tailWord_3271989 prefixEnd_3271989 1680103053224104061689903 := by
  unfold tailWord_3271989
  simp only [CollatzResearch.WordTrace]
  refine ⟨119339242943150139077075021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79559495295433426051383347 119339242943150139077075021)
  ·
    refine ⟨44752216103681302153903133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119339242943150139077075021 44752216103681302153903133)
    ·
      refine ⟨16782081038880488307713675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44752216103681302153903133 16782081038880488307713675)
      ·
        refine ⟨25173121558320732461570513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782081038880488307713675 25173121558320732461570513)
        ·
          refine ⟨18879841168740549346177885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25173121558320732461570513 18879841168740549346177885)
          ·
            refine ⟨7079940438277706004816707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18879841168740549346177885 7079940438277706004816707)
            ·
              refine ⟨10619910657416559007225061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079940438277706004816707 10619910657416559007225061)
              ·
                refine ⟨1991233248265604813854699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10619910657416559007225061 1991233248265604813854699)
                ·
                  refine ⟨2986849872398407220782049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991233248265604813854699 2986849872398407220782049)
                  ·
                    refine ⟨2240137404298805415586537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2986849872398407220782049 2240137404298805415586537)
                    ·
                      refine ⟨1680103053224104061689903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240137404298805415586537 1680103053224104061689903)
                      ·
                        rfl

theorem cell23_3271989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_3271989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3271989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3271989 prefixEnd_3271989 := by exact prefixLift 3271989
  have htrace : WordTrace (prefixWord ++ tailWord_3271989) baseStart_3271989 baseEnd_3271989 := by
    simpa [prefixWord, tailWord_3271989, baseEnd_3271989] using wordTrace_append hprefix tailTrace_3271989
  have hstable : (prefixWord ++ tailWord_3271989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271989).length < 2 ^ (prefixWord ++ tailWord_3271989).sum := by decide
  have hdescent : baseEnd_3271989 < baseStart_3271989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272031 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3272031 : Nat := 118140960795 + 3272031 * 2 ^ 59
def prefixEnd_3272031 : Nat := 4983230072969 + 3 ^ 40 * 3272031 * 2
def baseEnd_3272031 : Nat := 1680124619411592897364709

theorem tailTrace_3272031 : CollatzResearch.WordTrace tailWord_3272031 prefixEnd_3272031 1680124619411592897364709 := by
  unfold tailWord_3272031
  simp only [CollatzResearch.WordTrace]
  refine ⟨119340774808997980250103947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79560516539331986833402631 119340774808997980250103947)
  ·
    refine ⟨179011162213496970375155921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119340774808997980250103947 179011162213496970375155921)
    ·
      refine ⟨134258371660122727781366941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179011162213496970375155921 134258371660122727781366941)
      ·
        refine ⟨50346889372546022918012603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134258371660122727781366941 50346889372546022918012603)
        ·
          refine ⟨75520334058819034377018905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50346889372546022918012603 75520334058819034377018905)
          ·
            refine ⟨56640250544114275782764179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75520334058819034377018905 56640250544114275782764179)
            ·
              refine ⟨84960375816171413674146269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56640250544114275782764179 84960375816171413674146269)
              ·
                refine ⟨31860140931064280127804851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84960375816171413674146269 31860140931064280127804851)
                ·
                  refine ⟨47790211396596420191707277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31860140931064280127804851 47790211396596420191707277)
                  ·
                    refine ⟨17921329273723657571890229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47790211396596420191707277 17921329273723657571890229)
                    ·
                      refine ⟨1680124619411592897364709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17921329273723657571890229 1680124619411592897364709)
                      ·
                        rfl

theorem cell23_3272031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3272031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272031 prefixEnd_3272031 := by exact prefixLift 3272031
  have htrace : WordTrace (prefixWord ++ tailWord_3272031) baseStart_3272031 baseEnd_3272031 := by
    simpa [prefixWord, tailWord_3272031, baseEnd_3272031] using wordTrace_append hprefix tailTrace_3272031
  have hstable : (prefixWord ++ tailWord_3272031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272031).length < 2 ^ (prefixWord ++ tailWord_3272031).sum := by decide
  have hdescent : baseEnd_3272031 < baseStart_3272031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272032 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2]
def baseStart_3272032 : Nat := 118140960795 + 3272032 * 2 ^ 59
def prefixEnd_3272032 : Nat := 4983230072969 + 3 ^ 40 * 3272032 * 2
def baseEnd_3272032 : Nat := 1680125132892247393452205

theorem tailTrace_3272032 : CollatzResearch.WordTrace tailWord_3272032 prefixEnd_3272032 1680125132892247393452205 := by
  unfold tailWord_3272032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59670405640997178710445175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79560540854662904947260233 59670405640997178710445175)
  ·
    refine ⟨89505608461495768065667763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59670405640997178710445175 89505608461495768065667763)
    ·
      refine ⟨134258412692243652098501645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89505608461495768065667763 134258412692243652098501645)
      ·
        refine ⟨50346904759591369536938117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134258412692243652098501645 50346904759591369536938117)
        ·
          refine ⟨9440044642423381788175897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50346904759591369536938117 9440044642423381788175897)
          ·
            refine ⟨7080033481817536341131923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440044642423381788175897 7080033481817536341131923)
            ·
              refine ⟨10620050222726304511697885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080033481817536341131923 10620050222726304511697885)
              ·
                refine ⟨3982518833522364191886707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10620050222726304511697885 3982518833522364191886707)
                ·
                  refine ⟨5973778250283546287830061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982518833522364191886707 5973778250283546287830061)
                  ·
                    refine ⟨2240166843856329857936273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5973778250283546287830061 2240166843856329857936273)
                    ·
                      refine ⟨1680125132892247393452205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240166843856329857936273 1680125132892247393452205)
                      ·
                        rfl

theorem cell23_3272032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_3272032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272032 prefixEnd_3272032 := by exact prefixLift 3272032
  have htrace : WordTrace (prefixWord ++ tailWord_3272032) baseStart_3272032 baseEnd_3272032 := by
    simpa [prefixWord, tailWord_3272032, baseEnd_3272032] using wordTrace_append hprefix tailTrace_3272032
  have hstable : (prefixWord ++ tailWord_3272032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272032).length < 2 ^ (prefixWord ++ tailWord_3272032).sum := by decide
  have hdescent : baseEnd_3272032 < baseStart_3272032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272039 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3272039 : Nat := 118140960795 + 3272039 * 2 ^ 59
def prefixEnd_3272039 : Nat := 4983230072969 + 3 ^ 40 * 3272039 * 2
def baseEnd_3272039 : Nat := 1680128727256828866064673

theorem tailTrace_3272039 : CollatzResearch.WordTrace tailWord_3272039 prefixEnd_3272039 1680128727256828866064673 := by
  unfold tailWord_3272039
  simp only [CollatzResearch.WordTrace]
  refine ⟨119341066592968997616395171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79560711061979331744263447 119341066592968997616395171)
  ·
    refine ⟨179011599889453496424592757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119341066592968997616395171 179011599889453496424592757)
    ·
      refine ⟨16782337489636265289805571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179011599889453496424592757 16782337489636265289805571)
      ·
        refine ⟨25173506234454397934708357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782337489636265289805571 25173506234454397934708357)
        ·
          refine ⟨4720032418960199612757817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25173506234454397934708357 4720032418960199612757817)
          ·
            refine ⟨3540024314220149709568363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720032418960199612757817 3540024314220149709568363)
            ·
              refine ⟨5310036471330224564352545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540024314220149709568363 5310036471330224564352545)
              ·
                refine ⟨3982527353497668423264409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310036471330224564352545 3982527353497668423264409)
                ·
                  refine ⟨2986895515123251317448307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982527353497668423264409 2986895515123251317448307)
                  ·
                    refine ⟨4480343272684876976172461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986895515123251317448307 4480343272684876976172461)
                    ·
                      refine ⟨1680128727256828866064673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480343272684876976172461 1680128727256828866064673)
                      ·
                        rfl

theorem cell23_3272039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3272039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272039 prefixEnd_3272039 := by exact prefixLift 3272039
  have htrace : WordTrace (prefixWord ++ tailWord_3272039) baseStart_3272039 baseEnd_3272039 := by
    simpa [prefixWord, tailWord_3272039, baseEnd_3272039] using wordTrace_append hprefix tailTrace_3272039
  have hstable : (prefixWord ++ tailWord_3272039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272039).length < 2 ^ (prefixWord ++ tailWord_3272039).sum := by decide
  have hdescent : baseEnd_3272039 < baseStart_3272039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272066 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3272066 : Nat := 118140960795 + 3272066 * 2 ^ 59
def prefixEnd_3272066 : Nat := 4983230072969 + 3 ^ 40 * 3272066 * 2
def baseEnd_3272066 : Nat := 1680142591234500260427049

theorem tailTrace_3272066 : CollatzResearch.WordTrace tailWord_3272066 prefixEnd_3272066 1680142591234500260427049 := by
  unfold tailWord_3272066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29835512840967795306907013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79561367575914120818418701 29835512840967795306907013)
  ·
    refine ⟨5594158657681461620045065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29835512840967795306907013 5594158657681461620045065)
    ·
      refine ⟨4195618993261096215033799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5594158657681461620045065 4195618993261096215033799)
      ·
        refine ⟨6293428489891644322550699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195618993261096215033799 6293428489891644322550699)
        ·
          refine ⟨9440142734837466483826049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293428489891644322550699 9440142734837466483826049)
          ·
            refine ⟨7080107051128099862869537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440142734837466483826049 7080107051128099862869537)
            ·
              refine ⟨5310080288346074897152153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7080107051128099862869537 5310080288346074897152153)
              ·
                refine ⟨3982560216259556172864115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310080288346074897152153 3982560216259556172864115)
                ·
                  refine ⟨5973840324389334259296173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982560216259556172864115 5973840324389334259296173)
                  ·
                    refine ⟨2240190121646000347236065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5973840324389334259296173 2240190121646000347236065)
                    ·
                      refine ⟨1680142591234500260427049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240190121646000347236065 1680142591234500260427049)
                      ·
                        rfl

theorem cell23_3272066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3272066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272066 prefixEnd_3272066 := by exact prefixLift 3272066
  have htrace : WordTrace (prefixWord ++ tailWord_3272066) baseStart_3272066 baseEnd_3272066 := by
    simpa [prefixWord, tailWord_3272066, baseEnd_3272066] using wordTrace_append hprefix tailTrace_3272066
  have hstable : (prefixWord ++ tailWord_3272066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272066).length < 2 ^ (prefixWord ++ tailWord_3272066).sum := by decide
  have hdescent : baseEnd_3272066 < baseStart_3272066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272068 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 7]
def baseStart_3272068 : Nat := 118140960795 + 3272068 * 2 ^ 59
def prefixEnd_3272068 : Nat := 4983230072969 + 3 ^ 40 * 3272068 * 2
def baseEnd_3272068 : Nat := 186682624243978805844671

theorem tailTrace_3272068 : CollatzResearch.WordTrace tailWord_3272068 prefixEnd_3272068 186682624243978805844671 := by
  unfold tailWord_3272068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59671062154931967784600429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79561416206575957046133905 59671062154931967784600429)
  ·
    refine ⟨22376648308099487919225161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59671062154931967784600429 22376648308099487919225161)
    ·
      refine ⟨16782486231074615939418871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22376648308099487919225161 16782486231074615939418871)
      ·
        refine ⟨25173729346611923909128307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16782486231074615939418871 25173729346611923909128307)
        ·
          refine ⟨37760594019917885863692461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25173729346611923909128307 37760594019917885863692461)
          ·
            refine ⟨14160222757469207198884673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37760594019917885863692461 14160222757469207198884673)
            ·
              refine ⟨10620167068101905399163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14160222757469207198884673 10620167068101905399163505)
              ·
                refine ⟨7965125301076429049372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620167068101905399163505 7965125301076429049372629)
                ·
                  refine ⟨186682624243978805844671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7965125301076429049372629 186682624243978805844671)
                  ·
                    rfl

theorem cell23_3272068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_3272068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272068 prefixEnd_3272068 := by exact prefixLift 3272068
  have htrace : WordTrace (prefixWord ++ tailWord_3272068) baseStart_3272068 baseEnd_3272068 := by
    simpa [prefixWord, tailWord_3272068, baseEnd_3272068] using wordTrace_append hprefix tailTrace_3272068
  have hstable : (prefixWord ++ tailWord_3272068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272068).length < 2 ^ (prefixWord ++ tailWord_3272068).sum := by decide
  have hdescent : baseEnd_3272068 < baseStart_3272068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272082 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3272082 : Nat := 118140960795 + 3272082 * 2 ^ 59
def prefixEnd_3272082 : Nat := 4983230072969 + 3 ^ 40 * 3272082 * 2
def baseEnd_3272082 : Nat := 1680150806924972197826975

theorem tailTrace_3272082 : CollatzResearch.WordTrace tailWord_3272082 prefixEnd_3272082 1680150806924972197826975 := by
  unfold tailWord_3272082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29835658732953303990052625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79561756621208810640140333 29835658732953303990052625)
  ·
    refine ⟨22376744049714977992539469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29835658732953303990052625 22376744049714977992539469)
    ·
      refine ⟨8391279018643116747202301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22376744049714977992539469 8391279018643116747202301)
      ·
        refine ⟨3146729631991168780200863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8391279018643116747202301 3146729631991168780200863)
        ·
          refine ⟨4720094447986753170301295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146729631991168780200863 4720094447986753170301295)
          ·
            refine ⟨7080141671980129755451943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720094447986753170301295 7080141671980129755451943)
            ·
              refine ⟨10620212507970194633177915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080141671980129755451943 10620212507970194633177915)
              ·
                refine ⟨15930318761955291949766873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10620212507970194633177915 15930318761955291949766873)
                ·
                  refine ⟨11947739071466468962325155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15930318761955291949766873 11947739071466468962325155)
                  ·
                    refine ⟨17921608607199703443487733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11947739071466468962325155 17921608607199703443487733)
                    ·
                      refine ⟨1680150806924972197826975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17921608607199703443487733 1680150806924972197826975)
                      ·
                        rfl

theorem cell23_3272082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3272082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272082 prefixEnd_3272082 := by exact prefixLift 3272082
  have htrace : WordTrace (prefixWord ++ tailWord_3272082) baseStart_3272082 baseEnd_3272082 := by
    simpa [prefixWord, tailWord_3272082, baseEnd_3272082] using wordTrace_append hprefix tailTrace_3272082
  have hstable : (prefixWord ++ tailWord_3272082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272082).length < 2 ^ (prefixWord ++ tailWord_3272082).sum := by decide
  have hdescent : baseEnd_3272082 < baseStart_3272082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272085 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 5]
def baseStart_3272085 : Nat := 118140960795 + 3272085 * 2 ^ 59
def prefixEnd_3272085 : Nat := 4983230072969 + 3 ^ 40 * 3272085 * 2
def baseEnd_3272085 : Nat := 186683594151881742898829

theorem tailTrace_3272085 : CollatzResearch.WordTrace tailWord_3272085 prefixEnd_3272085 186683594151881742898829 := by
  unfold tailWord_3272085
  simp only [CollatzResearch.WordTrace]
  refine ⟨119342744350802347472569709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79561829567201564981713139 119342744350802347472569709)
  ·
    refine ⟨44753529131550880302213641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119342744350802347472569709 44753529131550880302213641)
    ·
      refine ⟨33565146848663160226660231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44753529131550880302213641 33565146848663160226660231)
      ·
        refine ⟨50347720272994740339990347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33565146848663160226660231 50347720272994740339990347)
        ·
          refine ⟨75521580409492110509985521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50347720272994740339990347 75521580409492110509985521)
          ·
            refine ⟨56641185307119082882489141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75521580409492110509985521 56641185307119082882489141)
            ·
              refine ⟨5310111122542414020233357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56641185307119082882489141 5310111122542414020233357)
              ·
                refine ⟨1991291670953405257587509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310111122542414020233357 1991291670953405257587509)
                ·
                  refine ⟨186683594151881742898829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991291670953405257587509 186683594151881742898829)
                  ·
                    rfl

theorem cell23_3272085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_3272085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272085 prefixEnd_3272085 := by exact prefixLift 3272085
  have htrace : WordTrace (prefixWord ++ tailWord_3272085) baseStart_3272085 baseEnd_3272085 := by
    simpa [prefixWord, tailWord_3272085, baseEnd_3272085] using wordTrace_append hprefix tailTrace_3272085
  have hstable : (prefixWord ++ tailWord_3272085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272085).length < 2 ^ (prefixWord ++ tailWord_3272085).sum := by decide
  have hdescent : baseEnd_3272085 < baseStart_3272085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272132 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3272132 : Nat := 118140960795 + 3272132 * 2 ^ 59
def prefixEnd_3272132 : Nat := 4983230072969 + 3 ^ 40 * 3272132 * 2
def baseEnd_3272132 : Nat := 560058826985899000733915

theorem tailTrace_3272132 : CollatzResearch.WordTrace tailWord_3272132 prefixEnd_3272132 560058826985899000733915 := by
  unfold tailWord_3272132
  simp only [CollatzResearch.WordTrace]
  refine ⟨59672229290816037249765325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79562972387754716333020433 59672229290816037249765325)
  ·
    refine ⟨22377085984056013968661997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59672229290816037249765325 22377085984056013968661997)
    ·
      refine ⟨8391407244021005238248249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22377085984056013968661997 8391407244021005238248249)
      ·
        refine ⟨6293555433015753928686187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8391407244021005238248249 6293555433015753928686187)
        ·
          refine ⟨9440333149523630893029281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293555433015753928686187 9440333149523630893029281)
          ·
            refine ⟨7080249862142723169771961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440333149523630893029281 7080249862142723169771961)
            ·
              refine ⟨5310187396607042377328971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7080249862142723169771961 5310187396607042377328971)
              ·
                refine ⟨7965281094910563565993457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310187396607042377328971 7965281094910563565993457)
                ·
                  refine ⟨5973960821182922674495093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965281094910563565993457 5973960821182922674495093)
                  ·
                    refine ⟨560058826985899000733915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5973960821182922674495093 560058826985899000733915)
                    ·
                      rfl

theorem cell23_3272132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3272132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272132 prefixEnd_3272132 := by exact prefixLift 3272132
  have htrace : WordTrace (prefixWord ++ tailWord_3272132) baseStart_3272132 baseEnd_3272132 := by
    simpa [prefixWord, tailWord_3272132, baseEnd_3272132] using wordTrace_append hprefix tailTrace_3272132
  have hstable : (prefixWord ++ tailWord_3272132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272132).length < 2 ^ (prefixWord ++ tailWord_3272132).sum := by decide
  have hdescent : baseEnd_3272132 < baseStart_3272132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272135 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3272135 : Nat := 118140960795 + 3272135 * 2 ^ 59
def prefixEnd_3272135 : Nat := 4983230072969 + 3 ^ 40 * 3272135 * 2
def baseEnd_3272135 : Nat := 1680178021399660490464231

theorem tailTrace_3272135 : CollatzResearch.WordTrace tailWord_3272135 prefixEnd_3272135 1680178021399660490464231 := by
  unfold tailWord_3272135
  simp only [CollatzResearch.WordTrace]
  refine ⟨119344568000621206011889859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79563045333747470674593239 119344568000621206011889859)
  ·
    refine ⟨179016852000931809017834789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119344568000621206011889859 179016852000931809017834789)
    ·
      refine ⟨33565659750174714190844023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179016852000931809017834789 33565659750174714190844023)
      ·
        refine ⟨50348489625262071286266035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33565659750174714190844023 50348489625262071286266035)
        ·
          refine ⟨75522734437893106929399053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50348489625262071286266035 75522734437893106929399053)
          ·
            refine ⟨28321025414209915098524645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75522734437893106929399053 28321025414209915098524645)
            ·
              refine ⟨5310192265164359080973371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28321025414209915098524645 5310192265164359080973371)
              ·
                refine ⟨7965288397746538621460057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310192265164359080973371 7965288397746538621460057)
                ·
                  refine ⟨5973966298309903966095043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7965288397746538621460057 5973966298309903966095043)
                  ·
                    refine ⟨8960949447464855949142565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5973966298309903966095043 8960949447464855949142565)
                    ·
                      refine ⟨1680178021399660490464231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8960949447464855949142565 1680178021399660490464231)
                      ·
                        rfl

theorem cell23_3272135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3272135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272135 prefixEnd_3272135 := by exact prefixLift 3272135
  have htrace : WordTrace (prefixWord ++ tailWord_3272135) baseStart_3272135 baseEnd_3272135 := by
    simpa [prefixWord, tailWord_3272135, baseEnd_3272135] using wordTrace_append hprefix tailTrace_3272135
  have hstable : (prefixWord ++ tailWord_3272135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272135).length < 2 ^ (prefixWord ++ tailWord_3272135).sum := by decide
  have hdescent : baseEnd_3272135 < baseStart_3272135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272196 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_3272196 : Nat := 118140960795 + 3272196 * 2 ^ 59
def prefixEnd_3272196 : Nat := 4983230072969 + 3 ^ 40 * 3272196 * 2
def baseEnd_3272196 : Nat := 560069781239861583933817

theorem tailTrace_3272196 : CollatzResearch.WordTrace tailWord_3272196 prefixEnd_3272196 560069781239861583933817 := by
  unfold tailWord_3272196
  simp only [CollatzResearch.WordTrace]
  refine ⟨59673396426700106714930221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79564528568933475619906961 59673396426700106714930221)
  ·
    refine ⟨22377523660012540018098833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59673396426700106714930221 22377523660012540018098833)
    ·
      refine ⟨16783142745009405013574125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22377523660012540018098833 16783142745009405013574125)
      ·
        refine ⟨6293678529378526880090297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16783142745009405013574125 6293678529378526880090297)
        ·
          refine ⟨4720258897033895160067723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6293678529378526880090297 4720258897033895160067723)
          ·
            refine ⟨7080388345550842740101585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720258897033895160067723 7080388345550842740101585)
            ·
              refine ⟨5310291259163132055076189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7080388345550842740101585 5310291259163132055076189)
              ·
                refine ⟨1991359222186174520653571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310291259163132055076189 1991359222186174520653571)
                ·
                  refine ⟨2987038833279261780980357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991359222186174520653571 2987038833279261780980357)
                  ·
                    refine ⟨560069781239861583933817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987038833279261780980357 560069781239861583933817)
                    ·
                      rfl

theorem cell23_3272196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_3272196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272196 prefixEnd_3272196 := by exact prefixLift 3272196
  have htrace : WordTrace (prefixWord ++ tailWord_3272196) baseStart_3272196 baseEnd_3272196 := by
    simpa [prefixWord, tailWord_3272196, baseEnd_3272196] using wordTrace_append hprefix tailTrace_3272196
  have hstable : (prefixWord ++ tailWord_3272196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272196).length < 2 ^ (prefixWord ++ tailWord_3272196).sum := by decide
  have hdescent : baseEnd_3272196 < baseStart_3272196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272253 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_3272253 : Nat := 118140960795 + 3272253 * 2 ^ 59
def prefixEnd_3272253 : Nat := 4983230072969 + 3 ^ 40 * 3272253 * 2
def baseEnd_3272253 : Nat := 1680238612116891028788689

theorem tailTrace_3272253 : CollatzResearch.WordTrace tailWord_3272253 prefixEnd_3272253 1680238612116891028788689 := by
  unfold tailWord_3272253
  simp only [CollatzResearch.WordTrace]
  refine ⟨119348871814193712164685413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79565914542795808109790275 119348871814193712164685413)
  ·
    refine ⟨22377913465161321030878515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119348871814193712164685413 22377913465161321030878515)
    ·
      refine ⟨33566870197741981546317773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22377913465161321030878515 33566870197741981546317773)
      ·
        refine ⟨12587576324153243079869165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33566870197741981546317773 12587576324153243079869165)
        ·
          refine ⟨4720341121557466154950937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12587576324153243079869165 4720341121557466154950937)
          ·
            refine ⟨3540255841168099616213203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720341121557466154950937 3540255841168099616213203)
            ·
              refine ⟨5310383761752149424319805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540255841168099616213203 5310383761752149424319805)
              ·
                refine ⟨1991393910657056034119927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310383761752149424319805 1991393910657056034119927)
                ·
                  refine ⟨2987090865985584051179891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991393910657056034119927 2987090865985584051179891)
                  ·
                    refine ⟨4480636298978376076769837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987090865985584051179891 4480636298978376076769837)
                    ·
                      refine ⟨1680238612116891028788689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480636298978376076769837 1680238612116891028788689)
                      ·
                        rfl

theorem cell23_3272253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_3272253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272253 prefixEnd_3272253 := by exact prefixLift 3272253
  have htrace : WordTrace (prefixWord ++ tailWord_3272253) baseStart_3272253 baseEnd_3272253 := by
    simpa [prefixWord, tailWord_3272253, baseEnd_3272253] using wordTrace_append hprefix tailTrace_3272253
  have hstable : (prefixWord ++ tailWord_3272253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272253).length < 2 ^ (prefixWord ++ tailWord_3272253).sum := by decide
  have hdescent : baseEnd_3272253 < baseStart_3272253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272296 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3272296 : Nat := 118140960795 + 3272296 * 2 ^ 59
def prefixEnd_3272296 : Nat := 4983230072969 + 3 ^ 40 * 3272296 * 2
def baseEnd_3272296 : Nat := 1680260691785034360550991

theorem tailTrace_3272296 : CollatzResearch.WordTrace tailWord_3272296 prefixEnd_3272296 1680260691785034360550991 := by
  unfold tailWord_3272296
  simp only [CollatzResearch.WordTrace]
  refine ⟨59675220076518965254250371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79566960102025287005667161 59675220076518965254250371)
  ·
    refine ⟨89512830114778447881375557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59675220076518965254250371 89512830114778447881375557)
    ·
      refine ⟨16783655646520958977757917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89512830114778447881375557 16783655646520958977757917)
      ·
        refine ⟨6293870867445359616659219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16783655646520958977757917 6293870867445359616659219)
        ·
          refine ⟨9440806301168039424988829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293870867445359616659219 9440806301168039424988829)
          ·
            refine ⟨3540302362938014784370811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9440806301168039424988829 3540302362938014784370811)
            ·
              refine ⟨5310453544407022176556217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540302362938014784370811 5310453544407022176556217)
              ·
                refine ⟨3982840158305266632417163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310453544407022176556217 3982840158305266632417163)
                ·
                  refine ⟨5974260237457899948625745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982840158305266632417163 5974260237457899948625745)
                  ·
                    refine ⟨4480695178093424961469309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974260237457899948625745 4480695178093424961469309)
                    ·
                      refine ⟨1680260691785034360550991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480695178093424961469309 1680260691785034360550991)
                      ·
                        rfl

theorem cell23_3272296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3272296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272296 prefixEnd_3272296 := by exact prefixLift 3272296
  have htrace : WordTrace (prefixWord ++ tailWord_3272296) baseStart_3272296 baseEnd_3272296 := by
    simpa [prefixWord, tailWord_3272296, baseEnd_3272296] using wordTrace_append hprefix tailTrace_3272296
  have hstable : (prefixWord ++ tailWord_3272296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272296).length < 2 ^ (prefixWord ++ tailWord_3272296).sum := by decide
  have hdescent : baseEnd_3272296 < baseStart_3272296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272309 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3272309 : Nat := 118140960795 + 3272309 * 2 ^ 59
def prefixEnd_3272309 : Nat := 4983230072969 + 3 ^ 40 * 3272309 * 2
def baseEnd_3272309 : Nat := 1680267367033542809688431

theorem tailTrace_3272309 : CollatzResearch.WordTrace tailWord_3272309 prefixEnd_3272309 1680267367033542809688431 := by
  unfold tailWord_3272309
  simp only [CollatzResearch.WordTrace]
  refine ⟨119350914301990833728723981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79567276201327222485815987 119350914301990833728723981)
  ·
    refine ⟨44756592863246562648271493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119350914301990833728723981 44756592863246562648271493)
    ·
      refine ⟨8391861161858730496550905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44756592863246562648271493 8391861161858730496550905)
      ·
        refine ⟨6293895871394047872413179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8391861161858730496550905 6293895871394047872413179)
        ·
          refine ⟨9440843807091071808619769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293895871394047872413179 9440843807091071808619769)
          ·
            refine ⟨7080632855318303856464827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9440843807091071808619769 7080632855318303856464827)
            ·
              refine ⟨10620949282977455784697241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080632855318303856464827 10620949282977455784697241)
              ·
                refine ⟨7965711962233091838522931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620949282977455784697241 7965711962233091838522931)
                ·
                  refine ⟨11948567943349637757784397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7965711962233091838522931 11948567943349637757784397)
                  ·
                    refine ⟨4480712978756114159169149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11948567943349637757784397 4480712978756114159169149)
                    ·
                      refine ⟨1680267367033542809688431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480712978756114159169149 1680267367033542809688431)
                      ·
                        rfl

theorem cell23_3272309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3272309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272309 prefixEnd_3272309 := by exact prefixLift 3272309
  have htrace : WordTrace (prefixWord ++ tailWord_3272309) baseStart_3272309 baseEnd_3272309 := by
    simpa [prefixWord, tailWord_3272309, baseEnd_3272309] using wordTrace_append hprefix tailTrace_3272309
  have hstable : (prefixWord ++ tailWord_3272309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272309).length < 2 ^ (prefixWord ++ tailWord_3272309).sum := by decide
  have hdescent : baseEnd_3272309 < baseStart_3272309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272325 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_3272325 : Nat := 118140960795 + 3272325 * 2 ^ 59
def prefixEnd_3272325 : Nat := 4983230072969 + 3 ^ 40 * 3272325 * 2
def baseEnd_3272325 : Nat := 560091860908004915696119

theorem tailTrace_3272325 : CollatzResearch.WordTrace tailWord_3272325 prefixEnd_3272325 560091860908004915696119 := by
  unfold tailWord_3272325
  simp only [CollatzResearch.WordTrace]
  refine ⟨119351497869932868461306429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79567665246621912307537619 119351497869932868461306429)
  ·
    refine ⟨44756811701224825672989911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119351497869932868461306429 44756811701224825672989911)
    ·
      refine ⟨67135217551837238509484867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44756811701224825672989911 67135217551837238509484867)
      ·
        refine ⟨100702826327755857764227301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67135217551837238509484867 100702826327755857764227301)
        ·
          refine ⟨18881779936454223330792619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100702826327755857764227301 18881779936454223330792619)
          ·
            refine ⟨28322669904681334996188929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18881779936454223330792619 28322669904681334996188929)
            ·
              refine ⟨21242002428511001247141697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28322669904681334996188929 21242002428511001247141697)
              ·
                refine ⟨15931501821383250935356273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21242002428511001247141697 15931501821383250935356273)
                ·
                  refine ⟨11948626366037438201517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15931501821383250935356273 11948626366037438201517205)
                  ·
                    refine ⟨560091860908004915696119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11948626366037438201517205 560091860908004915696119)
                    ·
                      rfl

theorem cell23_3272325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_3272325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272325 prefixEnd_3272325 := by exact prefixLift 3272325
  have htrace : WordTrace (prefixWord ++ tailWord_3272325) baseStart_3272325 baseEnd_3272325 := by
    simpa [prefixWord, tailWord_3272325, baseEnd_3272325] using wordTrace_append hprefix tailTrace_3272325
  have hstable : (prefixWord ++ tailWord_3272325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272325).length < 2 ^ (prefixWord ++ tailWord_3272325).sum := by decide
  have hdescent : baseEnd_3272325 < baseStart_3272325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272332 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 4, 2]
def baseStart_3272332 : Nat := 118140960795 + 3272332 * 2 ^ 59
def prefixEnd_3272332 : Nat := 4983230072969 + 3 ^ 40 * 3272332 * 2
def baseEnd_3272332 : Nat := 1680279177088596219700825

theorem tailTrace_3272332 : CollatzResearch.WordTrace tailWord_3272332 prefixEnd_3272332 1680279177088596219700825 := by
  unfold tailWord_3272332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59675876590453754328405625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79567835453938339104540833 59675876590453754328405625)
  ·
    refine ⟨44756907442840315746304219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59675876590453754328405625 44756907442840315746304219)
    ·
      refine ⟨67135361164260473619456329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44756907442840315746304219 67135361164260473619456329)
      ·
        refine ⟨50351520873195355214592247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67135361164260473619456329 50351520873195355214592247)
        ·
          refine ⟨75527281309793032821888371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50351520873195355214592247 75527281309793032821888371)
          ·
            refine ⟨113290921964689549232832557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75527281309793032821888371 113290921964689549232832557)
            ·
              refine ⟨42484095736758580962312209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113290921964689549232832557 42484095736758580962312209)
              ·
                refine ⟨31863071802568935721734157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42484095736758580962312209 31863071802568935721734157)
                ·
                  refine ⟨11948651925963350895650309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31863071802568935721734157 11948651925963350895650309)
                  ·
                    refine ⟨2240372236118128292934433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11948651925963350895650309 2240372236118128292934433)
                    ·
                      refine ⟨1680279177088596219700825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240372236118128292934433 1680279177088596219700825)
                      ·
                        rfl

theorem cell23_3272332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_3272332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272332 prefixEnd_3272332 := by exact prefixLift 3272332
  have htrace : WordTrace (prefixWord ++ tailWord_3272332) baseStart_3272332 baseEnd_3272332 := by
    simpa [prefixWord, tailWord_3272332, baseEnd_3272332] using wordTrace_append hprefix tailTrace_3272332
  have hstable : (prefixWord ++ tailWord_3272332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272332).length < 2 ^ (prefixWord ++ tailWord_3272332).sum := by decide
  have hdescent : baseEnd_3272332 < baseStart_3272332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272349 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_3272349 : Nat := 118140960795 + 3272349 * 2 ^ 59
def prefixEnd_3272349 : Nat := 4983230072969 + 3 ^ 40 * 3272349 * 2
def baseEnd_3272349 : Nat := 1680287906259722653188247

theorem tailTrace_3272349 : CollatzResearch.WordTrace tailWord_3272349 prefixEnd_3272349 1680287906259722653188247 := by
  unfold tailWord_3272349
  simp only [CollatzResearch.WordTrace]
  refine ⟨119352373221845920560180101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79568248814563947040120067 119352373221845920560180101)
  ·
    refine ⟨22378569979096110105033769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119352373221845920560180101 22378569979096110105033769)
    ·
      refine ⟨16783927484322082578775327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22378569979096110105033769 16783927484322082578775327)
      ·
        refine ⟨25175891226483123868162991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783927484322082578775327 25175891226483123868162991)
        ·
          refine ⟨37763836839724685802244487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25175891226483123868162991 37763836839724685802244487)
          ·
            refine ⟨56645755259587028703366731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37763836839724685802244487 56645755259587028703366731)
            ·
              refine ⟨84968632889380543055050097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56645755259587028703366731 84968632889380543055050097)
              ·
                refine ⟨63726474667035407291287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84968632889380543055050097 63726474667035407291287573)
                ·
                  refine ⟨2987178500017284716779105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63726474667035407291287573 2987178500017284716779105)
                  ·
                    refine ⟨2240383875012963537584329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2987178500017284716779105 2240383875012963537584329)
                    ·
                      refine ⟨1680287906259722653188247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240383875012963537584329 1680287906259722653188247)
                      ·
                        rfl

theorem cell23_3272349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_3272349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272349 prefixEnd_3272349 := by exact prefixLift 3272349
  have htrace : WordTrace (prefixWord ++ tailWord_3272349) baseStart_3272349 baseEnd_3272349 := by
    simpa [prefixWord, tailWord_3272349, baseEnd_3272349] using wordTrace_append hprefix tailTrace_3272349
  have hstable : (prefixWord ++ tailWord_3272349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272349).length < 2 ^ (prefixWord ++ tailWord_3272349).sum := by decide
  have hdescent : baseEnd_3272349 < baseStart_3272349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272355 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 7]
def baseStart_3272355 : Nat := 118140960795 + 3272355 * 2 ^ 59
def prefixEnd_3272355 : Nat := 4983230072969 + 3 ^ 40 * 3272355 * 2
def baseEnd_3272355 : Nat := 186698998571516625523691

theorem tailTrace_3272355 : CollatzResearch.WordTrace tailWord_3272355 prefixEnd_3272355 186698998571516625523691 := by
  unfold tailWord_3272355
  simp only [CollatzResearch.WordTrace]
  refine ⟨119352592059824183584898519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79568394706549455723265679 119352592059824183584898519)
  ·
    refine ⟨179028888089736275377347779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119352592059824183584898519 179028888089736275377347779)
    ·
      refine ⟨268543332134604413066021669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179028888089736275377347779 268543332134604413066021669)
      ·
        refine ⟨50351874775238327449879063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268543332134604413066021669 50351874775238327449879063)
        ·
          refine ⟨75527812162857491174818595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50351874775238327449879063 75527812162857491174818595)
          ·
            refine ⟨113291718244286236762227893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75527812162857491174818595 113291718244286236762227893)
            ·
              refine ⟨10621098585401834696458865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113291718244286236762227893 10621098585401834696458865)
              ·
                refine ⟨7965823939051376022344149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10621098585401834696458865 7965823939051376022344149)
                ·
                  refine ⟨186698998571516625523691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7965823939051376022344149 186698998571516625523691)
                  ·
                    rfl

theorem cell23_3272355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 7].length) (baseStart_3272355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272355 prefixEnd_3272355 := by exact prefixLift 3272355
  have htrace : WordTrace (prefixWord ++ tailWord_3272355) baseStart_3272355 baseEnd_3272355 := by
    simpa [prefixWord, tailWord_3272355, baseEnd_3272355] using wordTrace_append hprefix tailTrace_3272355
  have hstable : (prefixWord ++ tailWord_3272355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272355).length < 2 ^ (prefixWord ++ tailWord_3272355).sum := by decide
  have hdescent : baseEnd_3272355 < baseStart_3272355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272395 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5]
def baseStart_3272395 : Nat := 118140960795 + 3272395 * 2 ^ 59
def prefixEnd_3272395 : Nat := 4983230072969 + 3 ^ 40 * 3272395 * 2
def baseEnd_3272395 : Nat := 1680311526369829473213035

theorem tailTrace_3272395 : CollatzResearch.WordTrace tailWord_3272395 prefixEnd_3272395 1680311526369829473213035 := by
  unfold tailWord_3272395
  simp only [CollatzResearch.WordTrace]
  refine ⟨119354050979679270416354639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79569367319786180277569759 119354050979679270416354639)
  ·
    refine ⟨179031076469518905624531959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119354050979679270416354639 179031076469518905624531959)
    ·
      refine ⟨268546614704278358436797939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179031076469518905624531959 268546614704278358436797939)
      ·
        refine ⟨402819922056417537655196909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268546614704278358436797939 402819922056417537655196909)
        ·
          refine ⟨151057470771156576620698841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402819922056417537655196909 151057470771156576620698841)
          ·
            refine ⟨113293103078367432465524131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151057470771156576620698841 113293103078367432465524131)
            ·
              refine ⟨169939654617551148698286197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113293103078367432465524131 169939654617551148698286197)
              ·
                refine ⟨15931842620395420190464331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169939654617551148698286197 15931842620395420190464331)
                ·
                  refine ⟨23897763930593130285696497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15931842620395420190464331 23897763930593130285696497)
                  ·
                    refine ⟨17923322947944847714272373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23897763930593130285696497 17923322947944847714272373)
                    ·
                      refine ⟨1680311526369829473213035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17923322947944847714272373 1680311526369829473213035)
                      ·
                        rfl

theorem cell23_3272395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 5].length) (baseStart_3272395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272395 prefixEnd_3272395 := by exact prefixLift 3272395
  have htrace : WordTrace (prefixWord ++ tailWord_3272395) baseStart_3272395 baseEnd_3272395 := by
    simpa [prefixWord, tailWord_3272395, baseEnd_3272395] using wordTrace_append hprefix tailTrace_3272395
  have hstable : (prefixWord ++ tailWord_3272395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272395).length < 2 ^ (prefixWord ++ tailWord_3272395).sum := by decide
  have hdescent : baseEnd_3272395 < baseStart_3272395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272402 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3272402 : Nat := 118140960795 + 3272402 * 2 ^ 59
def prefixEnd_3272402 : Nat := 4983230072969 + 3 ^ 40 * 3272402 * 2
def baseEnd_3272402 : Nat := 560105040244803648608501

theorem tailTrace_3272402 : CollatzResearch.WordTrace tailWord_3272402 prefixEnd_3272402 560105040244803648608501 := by
  unfold tailWord_3272402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29838576572663477652964865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79569537527102607074572973 29838576572663477652964865)
  ·
    refine ⟨22378932429497608239723649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29838576572663477652964865 22378932429497608239723649)
    ·
      refine ⟨16784199322123206179792737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22378932429497608239723649 16784199322123206179792737)
      ·
        refine ⟨12588149491592404634844553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784199322123206179792737 12588149491592404634844553)
        ·
          refine ⟨9441112118694303476133415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12588149491592404634844553 9441112118694303476133415)
          ·
            refine ⟨14161668178041455214200123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441112118694303476133415 14161668178041455214200123)
            ·
              refine ⟨21242502267062182821300185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14161668178041455214200123 21242502267062182821300185)
              ·
                refine ⟨15931876700296637115975139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21242502267062182821300185 15931876700296637115975139)
                ·
                  refine ⟨23897815050444955673962709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15931876700296637115975139 23897815050444955673962709)
                  ·
                    refine ⟨560105040244803648608501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23897815050444955673962709 560105040244803648608501)
                    ·
                      rfl

theorem cell23_3272402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3272402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272402 prefixEnd_3272402 := by exact prefixLift 3272402
  have htrace : WordTrace (prefixWord ++ tailWord_3272402) baseStart_3272402 baseEnd_3272402 := by
    simpa [prefixWord, tailWord_3272402, baseEnd_3272402] using wordTrace_append hprefix tailTrace_3272402
  have hstable : (prefixWord ++ tailWord_3272402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272402).length < 2 ^ (prefixWord ++ tailWord_3272402).sum := by decide
  have hdescent : baseEnd_3272402 < baseStart_3272402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272415 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 8]
def baseStart_3272415 : Nat := 118140960795 + 3272415 * 2 ^ 59
def prefixEnd_3272415 : Nat := 4983230072969 + 3 ^ 40 * 3272415 * 2
def baseEnd_3272415 : Nat := 560107265327639798320981

theorem tailTrace_3272415 : CollatzResearch.WordTrace tailWord_3272415 prefixEnd_3272415 560107265327639798320981 := by
  unfold tailWord_3272415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119354780439606813832082699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79569853626404542554721799 119354780439606813832082699)
  ·
    refine ⟨179032170659410220748124049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119354780439606813832082699 179032170659410220748124049)
    ·
      refine ⟨134274127994557665561093037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179032170659410220748124049 134274127994557665561093037)
      ·
        refine ⟨50352797997959124585409889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134274127994557665561093037 50352797997959124585409889)
        ·
          refine ⟨37764598498469343439057417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50352797997959124585409889 37764598498469343439057417)
          ·
            refine ⟨28323448873852007579293063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37764598498469343439057417 28323448873852007579293063)
            ·
              refine ⟨42485173310778011368939595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28323448873852007579293063 42485173310778011368939595)
              ·
                refine ⟨63727759966167017053409393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42485173310778011368939595 63727759966167017053409393)
                ·
                  refine ⟨47795819974625262790057045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63727759966167017053409393 47795819974625262790057045)
                  ·
                    refine ⟨560107265327639798320981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47795819974625262790057045 560107265327639798320981)
                    ·
                      rfl

theorem cell23_3272415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_3272415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272415 prefixEnd_3272415 := by exact prefixLift 3272415
  have htrace : WordTrace (prefixWord ++ tailWord_3272415) baseStart_3272415 baseEnd_3272415 := by
    simpa [prefixWord, tailWord_3272415, baseEnd_3272415] using wordTrace_append hprefix tailTrace_3272415
  have hstable : (prefixWord ++ tailWord_3272415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272415).length < 2 ^ (prefixWord ++ tailWord_3272415).sum := by decide
  have hdescent : baseEnd_3272415 < baseStart_3272415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272423 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 5]
def baseStart_3272423 : Nat := 118140960795 + 3272423 * 2 ^ 59
def prefixEnd_3272423 : Nat := 4983230072969 + 3 ^ 40 * 3272423 * 2
def baseEnd_3272423 : Nat := 186702878203128373740323

theorem tailTrace_3272423 : CollatzResearch.WordTrace tailWord_3272423 prefixEnd_3272423 186702878203128373740323 := by
  unfold tailWord_3272423
  simp only [CollatzResearch.WordTrace]
  refine ⟨119355072223577831198373923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79570048149051887465582615 119355072223577831198373923)
  ·
    refine ⟨179032608335366746797560885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119355072223577831198373923 179032608335366746797560885)
    ·
      refine ⟨16784307031440632512271333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179032608335366746797560885 16784307031440632512271333)
      ·
        refine ⟨3147057568395118596050875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16784307031440632512271333 3147057568395118596050875)
        ·
          refine ⟨4720586352592677894076313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147057568395118596050875 4720586352592677894076313)
          ·
            refine ⟨3540439764444508420557235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4720586352592677894076313 3540439764444508420557235)
            ·
              refine ⟨5310659646666762630835853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540439764444508420557235 5310659646666762630835853)
              ·
                refine ⟨1991497367500035986563445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310659646666762630835853 1991497367500035986563445)
                ·
                  refine ⟨186702878203128373740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991497367500035986563445 186702878203128373740323)
                  ·
                    rfl

theorem cell23_3272423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 5].length) (baseStart_3272423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272423 prefixEnd_3272423 := by exact prefixLift 3272423
  have htrace : WordTrace (prefixWord ++ tailWord_3272423) baseStart_3272423 baseEnd_3272423 := by
    simpa [prefixWord, tailWord_3272423, baseEnd_3272423] using wordTrace_append hprefix tailTrace_3272423
  have hstable : (prefixWord ++ tailWord_3272423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272423).length < 2 ^ (prefixWord ++ tailWord_3272423).sum := by decide
  have hdescent : baseEnd_3272423 < baseStart_3272423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272425 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3272425 : Nat := 118140960795 + 3272425 * 2 ^ 59
def prefixEnd_3272425 : Nat := 4983230072969 + 3 ^ 40 * 3272425 * 2
def baseEnd_3272425 : Nat := 1680326930789464355837897

theorem tailTrace_3272425 : CollatzResearch.WordTrace tailWord_3272425 prefixEnd_3272425 1680326930789464355837897 := by
  unfold tailWord_3272425
  simp only [CollatzResearch.WordTrace]
  refine ⟨119355145169570585539946729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79570096779713723693297819 119355145169570585539946729)
  ·
    refine ⟨89516358877177939154960047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119355145169570585539946729 89516358877177939154960047)
    ·
      refine ⟨134274538315766908732440071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89516358877177939154960047 134274538315766908732440071)
      ·
        refine ⟨201411807473650363098660107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134274538315766908732440071 201411807473650363098660107)
        ·
          refine ⟨302117711210475544647990161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201411807473650363098660107 302117711210475544647990161)
          ·
            refine ⟨226588283407856658485992621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302117711210475544647990161 226588283407856658485992621)
            ·
              refine ⟨84970606277946246932247233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226588283407856658485992621 84970606277946246932247233)
              ·
                refine ⟨63727954708459685199185425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84970606277946246932247233 63727954708459685199185425)
                ·
                  refine ⟨47795966031344763899389069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63727954708459685199185425 47795966031344763899389069)
                  ·
                    refine ⟨17923487261754286462270901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47795966031344763899389069 17923487261754286462270901)
                    ·
                      refine ⟨1680326930789464355837897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17923487261754286462270901 1680326930789464355837897)
                      ·
                        rfl

theorem cell23_3272425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3272425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272425 prefixEnd_3272425 := by exact prefixLift 3272425
  have htrace : WordTrace (prefixWord ++ tailWord_3272425) baseStart_3272425 baseEnd_3272425 := by
    simpa [prefixWord, tailWord_3272425, baseEnd_3272425] using wordTrace_append hprefix tailTrace_3272425
  have hstable : (prefixWord ++ tailWord_3272425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272425).length < 2 ^ (prefixWord ++ tailWord_3272425).sum := by decide
  have hdescent : baseEnd_3272425 < baseStart_3272425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272435 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_3272435 : Nat := 118140960795 + 3272435 * 2 ^ 59
def prefixEnd_3272435 : Nat := 4983230072969 + 3 ^ 40 * 3272435 * 2
def baseEnd_3272435 : Nat := 1680332065596009316712851

theorem tailTrace_3272435 : CollatzResearch.WordTrace tailWord_3272435 prefixEnd_3272435 1680332065596009316712851 := by
  unfold tailWord_3272435
  simp only [CollatzResearch.WordTrace]
  refine ⟨119355509899534357247810759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79570339933022904831873839 119355509899534357247810759)
  ·
    refine ⟨179033264849301535871716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119355509899534357247810759 179033264849301535871716139)
    ·
      refine ⟨268549897273952303807574209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179033264849301535871716139 268549897273952303807574209)
      ·
        refine ⟨201412422955464227855680657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268549897273952303807574209 201412422955464227855680657)
        ·
          refine ⟨151059317216598170891760493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201412422955464227855680657 151059317216598170891760493)
          ·
            refine ⟨56647243956224314084410185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151059317216598170891760493 56647243956224314084410185)
            ·
              refine ⟨42485432967168235563307639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56647243956224314084410185 42485432967168235563307639)
              ·
                refine ⟨63728149450752353344961459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42485432967168235563307639 63728149450752353344961459)
                ·
                  refine ⟨95592224176128530017442189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63728149450752353344961459 95592224176128530017442189)
                  ·
                    refine ⟨35847084066048198756540821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95592224176128530017442189 35847084066048198756540821)
                    ·
                      refine ⟨1680332065596009316712851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35847084066048198756540821 1680332065596009316712851)
                      ·
                        rfl

theorem cell23_3272435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_3272435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272435 prefixEnd_3272435 := by exact prefixLift 3272435
  have htrace : WordTrace (prefixWord ++ tailWord_3272435) baseStart_3272435 baseEnd_3272435 := by
    simpa [prefixWord, tailWord_3272435, baseEnd_3272435] using wordTrace_append hprefix tailTrace_3272435
  have hstable : (prefixWord ++ tailWord_3272435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272435).length < 2 ^ (prefixWord ++ tailWord_3272435).sum := by decide
  have hdescent : baseEnd_3272435 < baseStart_3272435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272436 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3272436 : Nat := 118140960795 + 3272436 * 2 ^ 59
def prefixEnd_3272436 : Nat := 4983230072969 + 3 ^ 40 * 3272436 * 2
def baseEnd_3272436 : Nat := 560110859692221270933449

theorem tailTrace_3272436 : CollatzResearch.WordTrace tailWord_3272436 prefixEnd_3272436 560110859692221270933449 := by
  unfold tailWord_3272436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677773186265367209298581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79570364248353822945731441 59677773186265367209298581)
  ·
    refine ⟨2797395618106189087935871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59677773186265367209298581 2797395618106189087935871)
    ·
      refine ⟨4196093427159283631903807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797395618106189087935871 4196093427159283631903807)
      ·
        refine ⟨6294140140738925447855711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196093427159283631903807 6294140140738925447855711)
        ·
          refine ⟨9441210211108388171783567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294140140738925447855711 9441210211108388171783567)
          ·
            refine ⟨14161815316662582257675351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441210211108388171783567 14161815316662582257675351)
            ·
              refine ⟨21242722974993873386513027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14161815316662582257675351 21242722974993873386513027)
              ·
                refine ⟨31864084462490810079769541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21242722974993873386513027 31864084462490810079769541)
                ·
                  refine ⟨5974515836717026889956789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31864084462490810079769541 5974515836717026889956789)
                  ·
                    refine ⟨560110859692221270933449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5974515836717026889956789 560110859692221270933449)
                    ·
                      rfl

theorem cell23_3272436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3272436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272436 prefixEnd_3272436 := by exact prefixLift 3272436
  have htrace : WordTrace (prefixWord ++ tailWord_3272436) baseStart_3272436 baseEnd_3272436 := by
    simpa [prefixWord, tailWord_3272436, baseEnd_3272436] using wordTrace_append hprefix tailTrace_3272436
  have hstable : (prefixWord ++ tailWord_3272436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272436).length < 2 ^ (prefixWord ++ tailWord_3272436).sum := by decide
  have hdescent : baseEnd_3272436 < baseStart_3272436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272449 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3272449 : Nat := 118140960795 + 3272449 * 2 ^ 59
def prefixEnd_3272449 : Nat := 4983230072969 + 3 ^ 40 * 3272449 * 2
def baseEnd_3272449 : Nat := 560113084775057420645929

theorem tailTrace_3272449 : CollatzResearch.WordTrace tailWord_3272449 prefixEnd_3272449 560113084775057420645929 := by
  unfold tailWord_3272449
  simp only [CollatzResearch.WordTrace]
  refine ⟨119356020521483637638820401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79570680347655758425880267 119356020521483637638820401)
  ·
    refine ⟨89517015391112728229115301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119356020521483637638820401 89517015391112728229115301)
    ·
      refine ⟨16784440385833636542959119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89517015391112728229115301 16784440385833636542959119)
      ·
        refine ⟨25176660578750454814438679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16784440385833636542959119 25176660578750454814438679)
        ·
          refine ⟨37764990868125682221658019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176660578750454814438679 37764990868125682221658019)
          ·
            refine ⟨56647486302188523332487029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37764990868125682221658019 56647486302188523332487029)
            ·
              refine ⟨5310701840830174062420659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56647486302188523332487029 5310701840830174062420659)
              ·
                refine ⟨7966052761245261093630989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310701840830174062420659 7966052761245261093630989)
                ·
                  refine ⟨2987269785466972910111621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7966052761245261093630989 2987269785466972910111621)
                  ·
                    refine ⟨560113084775057420645929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987269785466972910111621 560113084775057420645929)
                    ·
                      rfl

theorem cell23_3272449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3272449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272449 prefixEnd_3272449 := by exact prefixLift 3272449
  have htrace : WordTrace (prefixWord ++ tailWord_3272449) baseStart_3272449 baseEnd_3272449 := by
    simpa [prefixWord, tailWord_3272449, baseEnd_3272449] using wordTrace_append hprefix tailTrace_3272449
  have hstable : (prefixWord ++ tailWord_3272449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272449).length < 2 ^ (prefixWord ++ tailWord_3272449).sum := by decide
  have hdescent : baseEnd_3272449 < baseStart_3272449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272472 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3272472 : Nat := 118140960795 + 3272472 * 2 ^ 59
def prefixEnd_3272472 : Nat := 4983230072969 + 3 ^ 40 * 3272472 * 2
def baseEnd_3272472 : Nat := 1680351064380225671950181

theorem tailTrace_3272472 : CollatzResearch.WordTrace tailWord_3272472 prefixEnd_3272472 1680351064380225671950181 := by
  unfold tailWord_3272472
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678429700200156283453835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79571239600266875044605113 59678429700200156283453835)
  ·
    refine ⟨89517644550300234425180753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59678429700200156283453835 89517644550300234425180753)
    ·
      refine ⟨67138233412725175818885565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89517644550300234425180753 67138233412725175818885565)
      ·
        refine ⟨25176837529771940932082087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67138233412725175818885565 25176837529771940932082087)
        ·
          refine ⟨37765256294657911398123131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176837529771940932082087 37765256294657911398123131)
          ·
            refine ⟨56647884441986867097184697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37765256294657911398123131 56647884441986867097184697)
            ·
              refine ⟨42485913331490150322888523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56647884441986867097184697 42485913331490150322888523)
              ·
                refine ⟨63728869997235225484332785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42485913331490150322888523 63728869997235225484332785)
                ·
                  refine ⟨47796652497926419113249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63728869997235225484332785 47796652497926419113249589)
                  ·
                    refine ⟨4480936171680601791867149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47796652497926419113249589 4480936171680601791867149)
                    ·
                      refine ⟨1680351064380225671950181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4480936171680601791867149 1680351064380225671950181)
                      ·
                        rfl

theorem cell23_3272472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3272472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272472 prefixEnd_3272472 := by exact prefixLift 3272472
  have htrace : WordTrace (prefixWord ++ tailWord_3272472) baseStart_3272472 baseEnd_3272472 := by
    simpa [prefixWord, tailWord_3272472, baseEnd_3272472] using wordTrace_append hprefix tailTrace_3272472
  have hstable : (prefixWord ++ tailWord_3272472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272472).length < 2 ^ (prefixWord ++ tailWord_3272472).sum := by decide
  have hdescent : baseEnd_3272472 < baseStart_3272472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272475 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 9]
def baseStart_3272475 : Nat := 118140960795 + 3272475 * 2 ^ 59
def prefixEnd_3272475 : Nat := 4983230072969 + 3 ^ 40 * 3272475 * 2
def baseEnd_3272475 : Nat := 560117534940729720070889

theorem tailTrace_3272475 : CollatzResearch.WordTrace tailWord_3272475 prefixEnd_3272475 560117534940729720070889 := by
  unfold tailWord_3272475
  simp only [CollatzResearch.WordTrace]
  refine ⟨119356968819389444079266879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79571312546259629386177919 119356968819389444079266879)
  ·
    refine ⟨179035453229084166118900319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119356968819389444079266879 179035453229084166118900319)
    ·
      refine ⟨268553179843626249178350479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179035453229084166118900319 268553179843626249178350479)
      ·
        refine ⟨402829769765439373767525719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268553179843626249178350479 402829769765439373767525719)
        ·
          refine ⟨604244654648159060651288579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402829769765439373767525719 604244654648159060651288579)
          ·
            refine ⟨906366981972238590976932869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604244654648159060651288579 906366981972238590976932869)
            ·
              refine ⟨169943809119794735808174913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 906366981972238590976932869 169943809119794735808174913)
              ·
                refine ⟨127457856839846051856131185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169943809119794735808174913 127457856839846051856131185)
                ·
                  refine ⟨95593392629884538892098389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127457856839846051856131185 95593392629884538892098389)
                  ·
                    refine ⟨560117534940729720070889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95593392629884538892098389 560117534940729720070889)
                    ·
                      rfl

theorem cell23_3272475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_3272475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272475 prefixEnd_3272475 := by exact prefixLift 3272475
  have htrace : WordTrace (prefixWord ++ tailWord_3272475) baseStart_3272475 baseEnd_3272475 := by
    simpa [prefixWord, tailWord_3272475, baseEnd_3272475] using wordTrace_append hprefix tailTrace_3272475
  have hstable : (prefixWord ++ tailWord_3272475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272475).length < 2 ^ (prefixWord ++ tailWord_3272475).sum := by decide
  have hdescent : baseEnd_3272475 < baseStart_3272475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272500 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3272500 : Nat := 118140960795 + 3272500 * 2 ^ 59
def prefixEnd_3272500 : Nat := 4983230072969 + 3 ^ 40 * 3272500 * 2
def baseEnd_3272500 : Nat := 560121813946183854133351

theorem tailTrace_3272500 : CollatzResearch.WordTrace tailWord_3272500 prefixEnd_3272500 560121813946183854133351 := by
  unfold tailWord_3272500
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678940322149436674463477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79571920429532582232617969 59678940322149436674463477)
  ·
    refine ⟨5594900655201509688230951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59678940322149436674463477 5594900655201509688230951)
    ·
      refine ⟨8392350982802264532346427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594900655201509688230951 8392350982802264532346427)
      ·
        refine ⟨12588526474203396798519641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8392350982802264532346427 12588526474203396798519641)
        ·
          refine ⟨9441394855652547598889731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12588526474203396798519641 9441394855652547598889731)
          ·
            refine ⟨14162092283478821398334597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441394855652547598889731 14162092283478821398334597)
            ·
              refine ⟨2655392303152279012187737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14162092283478821398334597 2655392303152279012187737)
              ·
                refine ⟨1991544227364209259140803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655392303152279012187737 1991544227364209259140803)
                ·
                  refine ⟨2987316341046313888711205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991544227364209259140803 2987316341046313888711205)
                  ·
                    refine ⟨560121813946183854133351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987316341046313888711205 560121813946183854133351)
                    ·
                      rfl

theorem cell23_3272500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3272500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272500 prefixEnd_3272500 := by exact prefixLift 3272500
  have htrace : WordTrace (prefixWord ++ tailWord_3272500) baseStart_3272500 baseEnd_3272500 := by
    simpa [prefixWord, tailWord_3272500, baseEnd_3272500] using wordTrace_append hprefix tailTrace_3272500
  have hstable : (prefixWord ++ tailWord_3272500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272500).length < 2 ^ (prefixWord ++ tailWord_3272500).sum := by decide
  have hdescent : baseEnd_3272500 < baseStart_3272500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272509 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_3272509 : Nat := 118140960795 + 3272509 * 2 ^ 59
def prefixEnd_3272509 : Nat := 4983230072969 + 3 ^ 40 * 3272509 * 2
def baseEnd_3272509 : Nat := 560123354388147342395837

theorem tailTrace_3272509 : CollatzResearch.WordTrace tailWord_3272509 prefixEnd_3272509 560123354388147342395837 := by
  unfold tailWord_3272509
  simp only [CollatzResearch.WordTrace]
  refine ⟨119358208901266267886004581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79572139267510845257336387 119358208901266267886004581)
  ·
    refine ⟨22379664168987425228625859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119358208901266267886004581 22379664168987425228625859)
    ·
      refine ⟨33569496253481137842938789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22379664168987425228625859 33569496253481137842938789)
      ·
        refine ⟨6294280547527713345551023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33569496253481137842938789 6294280547527713345551023)
        ·
          refine ⟨9441420821291570018326535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294280547527713345551023 9441420821291570018326535)
          ·
            refine ⟨14162131231937355027489803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441420821291570018326535 14162131231937355027489803)
            ·
              refine ⟨21243196847906032541234705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162131231937355027489803 21243196847906032541234705)
              ·
                refine ⟨15932397635929524405926029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21243196847906032541234705 15932397635929524405926029)
                ·
                  refine ⟨5974649113473571652222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15932397635929524405926029 5974649113473571652222261)
                  ·
                    refine ⟨560123354388147342395837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5974649113473571652222261 560123354388147342395837)
                    ·
                      rfl

theorem cell23_3272509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_3272509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272509 prefixEnd_3272509 := by exact prefixLift 3272509
  have htrace : WordTrace (prefixWord ++ tailWord_3272509) baseStart_3272509 baseEnd_3272509 := by
    simpa [prefixWord, tailWord_3272509, baseEnd_3272509] using wordTrace_append hprefix tailTrace_3272509
  have hstable : (prefixWord ++ tailWord_3272509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272509).length < 2 ^ (prefixWord ++ tailWord_3272509).sum := by decide
  have hdescent : baseEnd_3272509 < baseStart_3272509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272529 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3272529 : Nat := 118140960795 + 3272529 * 2 ^ 59
def prefixEnd_3272529 : Nat := 4983230072969 + 3 ^ 40 * 3272529 * 2
def baseEnd_3272529 : Nat := 1680380332777531948937419

theorem tailTrace_3272529 : CollatzResearch.WordTrace tailWord_3272529 prefixEnd_3272529 1680380332777531948937419 := by
  unfold tailWord_3272529
  simp only [CollatzResearch.WordTrace]
  refine ⟨119358938361193811301732641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79572625574129207534488427 119358938361193811301732641)
  ·
    refine ⟨89519203770895358476299481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119358938361193811301732641 89519203770895358476299481)
    ·
      refine ⟨67139402828171518857224611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89519203770895358476299481 67139402828171518857224611)
      ·
        refine ⟨100709104242257278285836917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67139402828171518857224611 100709104242257278285836917)
        ·
          refine ⟨9441478522711619839297211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100709104242257278285836917 9441478522711619839297211)
          ·
            refine ⟨14162217784067429758945817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441478522711619839297211 14162217784067429758945817)
            ·
              refine ⟨10621663338050572319209363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14162217784067429758945817 10621663338050572319209363)
              ·
                refine ⟨15932495007075858478814045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621663338050572319209363 15932495007075858478814045)
                ·
                  refine ⟨5974685627653446929555267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15932495007075858478814045 5974685627653446929555267)
                  ·
                    refine ⟨8962028441480170394332901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5974685627653446929555267 8962028441480170394332901)
                    ·
                      refine ⟨1680380332777531948937419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8962028441480170394332901 1680380332777531948937419)
                      ·
                        rfl

theorem cell23_3272529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3272529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272529 prefixEnd_3272529 := by exact prefixLift 3272529
  have htrace : WordTrace (prefixWord ++ tailWord_3272529) baseStart_3272529 baseEnd_3272529 := by
    simpa [prefixWord, tailWord_3272529, baseEnd_3272529] using wordTrace_append hprefix tailTrace_3272529
  have hstable : (prefixWord ++ tailWord_3272529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272529).length < 2 ^ (prefixWord ++ tailWord_3272529).sum := by decide
  have hdescent : baseEnd_3272529 < baseStart_3272529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272533 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3272533 : Nat := 118140960795 + 3272533 * 2 ^ 59
def prefixEnd_3272533 : Nat := 4983230072969 + 3 ^ 40 * 3272533 * 2
def baseEnd_3272533 : Nat := 1680382386700149933287401

theorem tailTrace_3272533 : CollatzResearch.WordTrace tailWord_3272533 prefixEnd_3272533 1680382386700149933287401 := by
  unfold tailWord_3272533
  simp only [CollatzResearch.WordTrace]
  refine ⟨119359084253179319984878253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79572722835452879989918835 119359084253179319984878253)
  ·
    refine ⟨44759656594942244994329345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119359084253179319984878253 44759656594942244994329345)
    ·
      refine ⟨33569742446206683745747009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44759656594942244994329345 33569742446206683745747009)
      ·
        refine ⟨25177306834655012809310257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33569742446206683745747009 25177306834655012809310257)
        ·
          refine ⟨18882980125991259606982693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25177306834655012809310257 18882980125991259606982693)
          ·
            refine ⟨3540558773623361176309255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18882980125991259606982693 3540558773623361176309255)
            ·
              refine ⟨5310838160435041764463883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540558773623361176309255 5310838160435041764463883)
              ·
                refine ⟨7966257240652562646695825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5310838160435041764463883 7966257240652562646695825)
                ·
                  refine ⟨5974692930489421985021869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966257240652562646695825 5974692930489421985021869)
                  ·
                    refine ⟨2240509848933533244383201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5974692930489421985021869 2240509848933533244383201)
                    ·
                      refine ⟨1680382386700149933287401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240509848933533244383201 1680382386700149933287401)
                      ·
                        rfl

theorem cell23_3272533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3272533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272533 prefixEnd_3272533 := by exact prefixLift 3272533
  have htrace : WordTrace (prefixWord ++ tailWord_3272533) baseStart_3272533 baseEnd_3272533 := by
    simpa [prefixWord, tailWord_3272533, baseEnd_3272533] using wordTrace_append hprefix tailTrace_3272533
  have hstable : (prefixWord ++ tailWord_3272533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272533).length < 2 ^ (prefixWord ++ tailWord_3272533).sum := by decide
  have hdescent : baseEnd_3272533 < baseStart_3272533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272552 : List Nat := [2, 1, 4, 2, 1, 1, 12]
def baseStart_3272552 : Nat := 118140960795 + 3272552 * 2 ^ 59
def prefixEnd_3272552 : Nat := 4983230072969 + 3 ^ 40 * 3272552 * 2
def baseEnd_3272552 : Nat := 20745582010278831591973

theorem tailTrace_3272552 : CollatzResearch.WordTrace tailWord_3272552 prefixEnd_3272552 20745582010278831591973 := by
  unfold tailWord_3272552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59679888620055243114909955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79573184826740324153213273 59679888620055243114909955)
  ·
    refine ⟨89519832930082864672364933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59679888620055243114909955 89519832930082864672364933)
    ·
      refine ⟨16784968674390537126068425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89519832930082864672364933 16784968674390537126068425)
      ·
        refine ⟨12588726505792902844551319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784968674390537126068425 12588726505792902844551319)
        ·
          refine ⟨18883089758689354266826979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12588726505792902844551319 18883089758689354266826979)
          ·
            refine ⟨28324634638034031400240469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18883089758689354266826979 28324634638034031400240469)
            ·
              refine ⟨20745582010278831591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 28324634638034031400240469 20745582010278831591973)
              ·
                rfl

theorem cell23_3272552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 12].length) (baseStart_3272552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272552 prefixEnd_3272552 := by exact prefixLift 3272552
  have htrace : WordTrace (prefixWord ++ tailWord_3272552) baseStart_3272552 baseEnd_3272552 := by
    simpa [prefixWord, tailWord_3272552, baseEnd_3272552] using wordTrace_append hprefix tailTrace_3272552
  have hstable : (prefixWord ++ tailWord_3272552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272552).length < 2 ^ (prefixWord ++ tailWord_3272552).sum := by decide
  have hdescent : baseEnd_3272552 < baseStart_3272552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272556 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 2, 4]
def baseStart_3272556 : Nat := 118140960795 + 3272556 * 2 ^ 59
def prefixEnd_3272556 : Nat := 4983230072969 + 3 ^ 40 * 3272556 * 2
def baseEnd_3272556 : Nat := 560131398918401114433265

theorem tailTrace_3272556 : CollatzResearch.WordTrace tailWord_3272556 prefixEnd_3272556 560131398918401114433265 := by
  unfold tailWord_3272556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59679961566047997456482761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79573282088063996608643681 59679961566047997456482761)
  ·
    refine ⟨44759971174535998092362071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59679961566047997456482761 44759971174535998092362071)
    ·
      refine ⟨67139956761803997138543107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44759971174535998092362071 67139956761803997138543107)
      ·
        refine ⟨100709935142705995707814661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67139956761803997138543107 100709935142705995707814661)
        ·
          refine ⟨18883112839257374195215249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100709935142705995707814661 18883112839257374195215249)
          ·
            refine ⟨14162334629443030646411437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18883112839257374195215249 14162334629443030646411437)
            ·
              refine ⟨5310875486041136492404289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14162334629443030646411437 5310875486041136492404289)
              ·
                refine ⟨3983156614530852369303217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310875486041136492404289 3983156614530852369303217)
                ·
                  refine ⟨2987367460898139276977413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983156614530852369303217 2987367460898139276977413)
                  ·
                    refine ⟨560131398918401114433265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987367460898139276977413 560131398918401114433265)
                    ·
                      rfl

theorem cell23_3272556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_3272556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272556 prefixEnd_3272556 := by exact prefixLift 3272556
  have htrace : WordTrace (prefixWord ++ tailWord_3272556) baseStart_3272556 baseEnd_3272556 := by
    simpa [prefixWord, tailWord_3272556, baseEnd_3272556] using wordTrace_append hprefix tailTrace_3272556
  have hstable : (prefixWord ++ tailWord_3272556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272556).length < 2 ^ (prefixWord ++ tailWord_3272556).sum := by decide
  have hdescent : baseEnd_3272556 < baseStart_3272556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3272562 : Nat := 118140960795 + 3272562 * 2 ^ 59
def prefixEnd_3272562 : Nat := 4983230072969 + 3 ^ 40 * 3272562 * 2
def baseEnd_3272562 : Nat := 1680397277639130319824767

theorem tailTrace_3272562 : CollatzResearch.WordTrace tailWord_3272562 prefixEnd_3272562 1680397277639130319824767 := by
  unfold tailWord_3272562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29840035492518564484420985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79573427980049505291789293 29840035492518564484420985)
  ·
    refine ⟨22380026619388923363315739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29840035492518564484420985 22380026619388923363315739)
    ·
      refine ⟨33570039929083385044973609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22380026619388923363315739 33570039929083385044973609)
      ·
        refine ⟨25177529946812538783730207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33570039929083385044973609 25177529946812538783730207)
        ·
          refine ⟨37766294920218808175595311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25177529946812538783730207 37766294920218808175595311)
          ·
            refine ⟨56649442380328212263392967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37766294920218808175595311 56649442380328212263392967)
            ·
              refine ⟨84974163570492318395089451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56649442380328212263392967 84974163570492318395089451)
              ·
                refine ⟨127461245355738477592634177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84974163570492318395089451 127461245355738477592634177)
                ·
                  refine ⟨95595934016803858194475633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127461245355738477592634177 95595934016803858194475633)
                  ·
                    refine ⟨71696950512602893645856725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95595934016803858194475633 71696950512602893645856725)
                    ·
                      refine ⟨1680397277639130319824767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71696950512602893645856725 1680397277639130319824767)
                      ·
                        rfl

theorem cell23_3272562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3272562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272562 prefixEnd_3272562 := by exact prefixLift 3272562
  have htrace : WordTrace (prefixWord ++ tailWord_3272562) baseStart_3272562 baseEnd_3272562 := by
    simpa [prefixWord, tailWord_3272562, baseEnd_3272562] using wordTrace_append hprefix tailTrace_3272562
  have hstable : (prefixWord ++ tailWord_3272562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272562).length < 2 ^ (prefixWord ++ tailWord_3272562).sum := by decide
  have hdescent : baseEnd_3272562 < baseStart_3272562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272583 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3272583 : Nat := 118140960795 + 3272583 * 2 ^ 59
def prefixEnd_3272583 : Nat := 4983230072969 + 3 ^ 40 * 3272583 * 2
def baseEnd_3272583 : Nat := 1680408060732874737662171

theorem tailTrace_3272583 : CollatzResearch.WordTrace tailWord_3272583 prefixEnd_3272583 1680408060732874737662171 := by
  unfold tailWord_3272583
  simp only [CollatzResearch.WordTrace]
  refine ⟨119360907902998178524198403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79573938601998785682798935 119360907902998178524198403)
  ·
    refine ⟨179041361854497267786297605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119360907902998178524198403 179041361854497267786297605)
    ·
      refine ⟨33570255347718237709930801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179041361854497267786297605 33570255347718237709930801)
      ·
        refine ⟨25177691510788678282448101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33570255347718237709930801 25177691510788678282448101)
        ·
          refine ⟨4720817158272877177959019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25177691510788678282448101 4720817158272877177959019)
          ·
            refine ⟨7081225737409315766938529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720817158272877177959019 7081225737409315766938529)
            ·
              refine ⟨5310919303056986825203897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7081225737409315766938529 5310919303056986825203897)
              ·
                refine ⟨3983189477292740118902923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310919303056986825203897 3983189477292740118902923)
                ·
                  refine ⟨5974784215939110178354385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983189477292740118902923 5974784215939110178354385)
                  ·
                    refine ⟨4481088161954332633765789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5974784215939110178354385 4481088161954332633765789)
                    ·
                      refine ⟨1680408060732874737662171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481088161954332633765789 1680408060732874737662171)
                      ·
                        rfl

theorem cell23_3272583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3272583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272583 prefixEnd_3272583 := by exact prefixLift 3272583
  have htrace : WordTrace (prefixWord ++ tailWord_3272583) baseStart_3272583 baseEnd_3272583 := by
    simpa [prefixWord, tailWord_3272583, baseEnd_3272583] using wordTrace_append hprefix tailTrace_3272583
  have hstable : (prefixWord ++ tailWord_3272583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272583).length < 2 ^ (prefixWord ++ tailWord_3272583).sum := by decide
  have hdescent : baseEnd_3272583 < baseStart_3272583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272592 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_3272592 : Nat := 118140960795 + 3272592 * 2 ^ 59
def prefixEnd_3272592 : Nat := 4983230072969 + 3 ^ 40 * 3272592 * 2
def baseEnd_3272592 : Nat := 1680412682058765202449629

theorem tailTrace_3272592 : CollatzResearch.WordTrace tailWord_3272592 prefixEnd_3272592 1680412682058765202449629 := by
  unfold tailWord_3272592
  simp only [CollatzResearch.WordTrace]
  refine ⟨59680618079982786530638015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79574157439977048707517353 59680618079982786530638015)
  ·
    refine ⟨89520927119974179795957023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59680618079982786530638015 89520927119974179795957023)
    ·
      refine ⟨134281390679961269693935535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89520927119974179795957023 134281390679961269693935535)
      ·
        refine ⟨201422086019941904540903303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134281390679961269693935535 201422086019941904540903303)
        ·
          refine ⟨302133129029912856811354955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201422086019941904540903303 302133129029912856811354955)
          ·
            refine ⟨453199693544869285217032433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302133129029912856811354955 453199693544869285217032433)
            ·
              refine ⟨339899770158651963912774325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453199693544869285217032433 339899770158651963912774325)
              ·
                refine ⟨31865603452373621616822593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339899770158651963912774325 31865603452373621616822593)
                ·
                  refine ⟨23899202589280216212616945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31865603452373621616822593 23899202589280216212616945)
                  ·
                    refine ⟨17924401941960162159462709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23899202589280216212616945 17924401941960162159462709)
                    ·
                      refine ⟨1680412682058765202449629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17924401941960162159462709 1680412682058765202449629)
                      ·
                        rfl

theorem cell23_3272592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_3272592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272592 prefixEnd_3272592 := by exact prefixLift 3272592
  have htrace : WordTrace (prefixWord ++ tailWord_3272592) baseStart_3272592 baseEnd_3272592 := by
    simpa [prefixWord, tailWord_3272592, baseEnd_3272592] using wordTrace_append hprefix tailTrace_3272592
  have hstable : (prefixWord ++ tailWord_3272592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272592).length < 2 ^ (prefixWord ++ tailWord_3272592).sum := by decide
  have hdescent : baseEnd_3272592 < baseStart_3272592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 8, 2]
def baseStart_3272619 : Nat := 118140960795 + 3272619 * 2 ^ 59
def prefixEnd_3272619 : Nat := 4983230072969 + 3 ^ 40 * 3272619 * 2
def baseEnd_3272619 : Nat := 1680426546036436596812005

theorem tailTrace_3272619 : CollatzResearch.WordTrace tailWord_3272619 prefixEnd_3272619 1680426546036436596812005 := by
  unfold tailWord_3272619
  simp only [CollatzResearch.WordTrace]
  refine ⟨119362220930867756672508911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79574813953911837781672607 119362220930867756672508911)
  ·
    refine ⟨179043331396301635008763367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119362220930867756672508911 179043331396301635008763367)
    ·
      refine ⟨268564997094452452513145051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179043331396301635008763367 268564997094452452513145051)
      ·
        refine ⟨402847495641678678769717577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268564997094452452513145051 402847495641678678769717577)
        ·
          refine ⟨302135621731259009077288183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402847495641678678769717577 302135621731259009077288183)
          ·
            refine ⟨453203432596888513615932275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302135621731259009077288183 453203432596888513615932275)
            ·
              refine ⟨679805148895332770423898413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453203432596888513615932275 679805148895332770423898413)
              ·
                refine ⟨254926930835749788908961905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 679805148895332770423898413 254926930835749788908961905)
                ·
                  refine ⟨191195198126812341681721429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254926930835749788908961905 191195198126812341681721429)
                  ·
                    refine ⟨2240568728048582129082673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 191195198126812341681721429 2240568728048582129082673)
                    ·
                      refine ⟨1680426546036436596812005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240568728048582129082673 1680426546036436596812005)
                      ·
                        rfl

theorem cell23_3272619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8, 2].length) (baseStart_3272619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272619 prefixEnd_3272619 := by exact prefixLift 3272619
  have htrace : WordTrace (prefixWord ++ tailWord_3272619) baseStart_3272619 baseEnd_3272619 := by
    simpa [prefixWord, tailWord_3272619, baseEnd_3272619] using wordTrace_append hprefix tailTrace_3272619
  have hstable : (prefixWord ++ tailWord_3272619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272619).length < 2 ^ (prefixWord ++ tailWord_3272619).sum := by decide
  have hdescent : baseEnd_3272619 < baseStart_3272619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272676 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 5]
def baseStart_3272676 : Nat := 118140960795 + 3272676 * 2 ^ 59
def prefixEnd_3272676 : Nat := 4983230072969 + 3 ^ 40 * 3272676 * 2
def baseEnd_3272676 : Nat := 186717312714860319311027

theorem tailTrace_3272676 : CollatzResearch.WordTrace tailWord_3272676 prefixEnd_3272676 186717312714860319311027 := by
  unfold tailWord_3272676
  simp only [CollatzResearch.WordTrace]
  refine ⟨59682149945830627703666941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79576199927774170271555921 59682149945830627703666941)
  ·
    refine ⟨22380806229686485388875103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59682149945830627703666941 22380806229686485388875103)
    ·
      refine ⟨33571209344529728083312655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22380806229686485388875103 33571209344529728083312655)
      ·
        refine ⟨50356814016794592124968983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33571209344529728083312655 50356814016794592124968983)
        ·
          refine ⟨75535221025191888187453475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50356814016794592124968983 75535221025191888187453475)
          ·
            refine ⟨113302831537787832281180213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75535221025191888187453475 113302831537787832281180213)
            ·
              refine ⟨10622140456667609276360645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113302831537787832281180213 10622140456667609276360645)
              ·
                refine ⟨1991651335625176739317621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10622140456667609276360645 1991651335625176739317621)
                ·
                  refine ⟨186717312714860319311027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1991651335625176739317621 186717312714860319311027)
                  ·
                    rfl

theorem cell23_3272676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_3272676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272676 prefixEnd_3272676 := by exact prefixLift 3272676
  have htrace : WordTrace (prefixWord ++ tailWord_3272676) baseStart_3272676 baseEnd_3272676 := by
    simpa [prefixWord, tailWord_3272676, baseEnd_3272676] using wordTrace_append hprefix tailTrace_3272676
  have hstable : (prefixWord ++ tailWord_3272676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272676).length < 2 ^ (prefixWord ++ tailWord_3272676).sum := by decide
  have hdescent : baseEnd_3272676 < baseStart_3272676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272686 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_3272686 : Nat := 118140960795 + 3272686 * 2 ^ 59
def prefixEnd_3272686 : Nat := 4983230072969 + 3 ^ 40 * 3272686 * 2
def baseEnd_3272686 : Nat := 1680460949240287834674197

theorem tailTrace_3272686 : CollatzResearch.WordTrace tailWord_3272686 prefixEnd_3272686 1680460949240287834674197 := by
  unfold tailWord_3272686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14920583077703128389399739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79576443081083351410131941 14920583077703128389399739)
  ·
    refine ⟨22380874616554692584099609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14920583077703128389399739 22380874616554692584099609)
    ·
      refine ⟨16785655962416019438074707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22380874616554692584099609 16785655962416019438074707)
      ·
        refine ⟨25178483943624029157112061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16785655962416019438074707 25178483943624029157112061)
        ·
          refine ⟨9441931478859010933917023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25178483943624029157112061 9441931478859010933917023)
          ·
            refine ⟨14162897218288516400875535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9441931478859010933917023 14162897218288516400875535)
            ·
              refine ⟨21244345827432774601313303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14162897218288516400875535 21244345827432774601313303)
              ·
                refine ⟨31866518741149161901969955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21244345827432774601313303 31866518741149161901969955)
                ·
                  refine ⟨47799778111723742852954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31866518741149161901969955 47799778111723742852954933)
                  ·
                    refine ⟨4481229197974100892464525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47799778111723742852954933 4481229197974100892464525)
                    ·
                      refine ⟨1680460949240287834674197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481229197974100892464525 1680460949240287834674197)
                      ·
                        rfl

theorem cell23_3272686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_3272686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272686 prefixEnd_3272686 := by exact prefixLift 3272686
  have htrace : WordTrace (prefixWord ++ tailWord_3272686) baseStart_3272686 baseEnd_3272686 := by
    simpa [prefixWord, tailWord_3272686, baseEnd_3272686] using wordTrace_append hprefix tailTrace_3272686
  have hstable : (prefixWord ++ tailWord_3272686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272686).length < 2 ^ (prefixWord ++ tailWord_3272686).sum := by decide
  have hdescent : baseEnd_3272686 < baseStart_3272686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272739 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3272739 : Nat := 118140960795 + 3272739 * 2 ^ 59
def prefixEnd_3272739 : Nat := 4983230072969 + 3 ^ 40 * 3272739 * 2
def baseEnd_3272739 : Nat := 1680488163714976127311453

theorem tailTrace_3272739 : CollatzResearch.WordTrace tailWord_3272739 prefixEnd_3272739 1680488163714976127311453 := by
  unfold tailWord_3272739
  simp only [CollatzResearch.WordTrace]
  refine ⟨119366597690433017166877271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79577731793622011444584847 119366597690433017166877271)
  ·
    refine ⟨179049896535649525750315907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119366597690433017166877271 179049896535649525750315907)
    ·
      refine ⟨268574844803474288625473861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179049896535649525750315907 268574844803474288625473861)
      ·
        refine ⟨50357783400651429117276349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268574844803474288625473861 50357783400651429117276349)
        ·
          refine ⟨18884168775244285918978631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50357783400651429117276349 18884168775244285918978631)
          ·
            refine ⟨28326253162866428878467947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884168775244285918978631 28326253162866428878467947)
            ·
              refine ⟨42489379744299643317701921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28326253162866428878467947 42489379744299643317701921)
              ·
                refine ⟨31867034808224732488276441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42489379744299643317701921 31867034808224732488276441)
                ·
                  refine ⟨23900276106168549366207331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31867034808224732488276441 23900276106168549366207331)
                  ·
                    refine ⟨35850414159252824049310997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23900276106168549366207331 35850414159252824049310997)
                    ·
                      refine ⟨1680488163714976127311453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35850414159252824049310997 1680488163714976127311453)
                      ·
                        rfl

theorem cell23_3272739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3272739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272739 prefixEnd_3272739 := by exact prefixLift 3272739
  have htrace : WordTrace (prefixWord ++ tailWord_3272739) baseStart_3272739 baseEnd_3272739 := by
    simpa [prefixWord, tailWord_3272739, baseEnd_3272739] using wordTrace_append hprefix tailTrace_3272739
  have hstable : (prefixWord ++ tailWord_3272739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272739).length < 2 ^ (prefixWord ++ tailWord_3272739).sum := by decide
  have hdescent : baseEnd_3272739 < baseStart_3272739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272819 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_3272819 : Nat := 118140960795 + 3272819 * 2 ^ 59
def prefixEnd_3272819 : Nat := 4983230072969 + 3 ^ 40 * 3272819 * 2
def baseEnd_3272819 : Nat := 1680529242167335814311085

theorem tailTrace_3272819 : CollatzResearch.WordTrace tailWord_3272819 prefixEnd_3272819 1680529242167335814311085 := by
  unfold tailWord_3272819
  simp only [CollatzResearch.WordTrace]
  refine ⟨119369515530143190829789511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79579677020095460553193007 119369515530143190829789511)
  ·
    refine ⟨179054273295214786244684267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119369515530143190829789511 179054273295214786244684267)
    ·
      refine ⟨268581409942822179367026401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179054273295214786244684267 268581409942822179367026401)
      ·
        refine ⟨201436057457116634525269801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268581409942822179367026401 201436057457116634525269801)
        ·
          refine ⟨151077043092837475893952351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201436057457116634525269801 151077043092837475893952351)
          ·
            refine ⟨226615564639256213840928527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151077043092837475893952351 226615564639256213840928527)
            ·
              refine ⟨339923346958884320761392791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226615564639256213840928527 339923346958884320761392791)
              ·
                refine ⟨509885020438326481142089187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339923346958884320761392791 509885020438326481142089187)
                ·
                  refine ⟨764827530657489721713133781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509885020438326481142089187 764827530657489721713133781)
                  ·
                    refine ⟨17925645249784915352651573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 764827530657489721713133781 17925645249784915352651573)
                    ·
                      refine ⟨1680529242167335814311085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17925645249784915352651573 1680529242167335814311085)
                      ·
                        rfl

theorem cell23_3272819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_3272819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272819 prefixEnd_3272819 := by exact prefixLift 3272819
  have htrace : WordTrace (prefixWord ++ tailWord_3272819) baseStart_3272819 baseEnd_3272819 := by
    simpa [prefixWord, tailWord_3272819, baseEnd_3272819] using wordTrace_append hprefix tailTrace_3272819
  have hstable : (prefixWord ++ tailWord_3272819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272819).length < 2 ^ (prefixWord ++ tailWord_3272819).sum := by decide
  have hdescent : baseEnd_3272819 < baseStart_3272819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272863 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3272863 : Nat := 118140960795 + 3272863 * 2 ^ 59
def prefixEnd_3272863 : Nat := 4983230072969 + 3 ^ 40 * 3272863 * 2
def baseEnd_3272863 : Nat := 1680551835316133642160883

theorem tailTrace_3272863 : CollatzResearch.WordTrace tailWord_3272863 prefixEnd_3272863 1680551835316133642160883 := by
  unfold tailWord_3272863
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371120341983786344391243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79580746894655857562927495 119371120341983786344391243)
  ·
    refine ⟨179056680512975679516586865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119371120341983786344391243 179056680512975679516586865)
    ·
      refine ⟨134292510384731759637440149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179056680512975679516586865 134292510384731759637440149)
      ·
        refine ⟨6294961424284301233005007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134292510384731759637440149 6294961424284301233005007)
        ·
          refine ⟨9442442136426451849507511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294961424284301233005007 9442442136426451849507511)
          ·
            refine ⟨14163663204639677774261267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442442136426451849507511 14163663204639677774261267)
            ·
              refine ⟨21245494806959516661391901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14163663204639677774261267 21245494806959516661391901)
              ·
                refine ⟨7967060552609818748021963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21245494806959516661391901 7967060552609818748021963)
                ·
                  refine ⟨11950590828914728122032945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7967060552609818748021963 11950590828914728122032945)
                  ·
                    refine ⟨8962943121686046091524709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11950590828914728122032945 8962943121686046091524709)
                    ·
                      refine ⟨1680551835316133642160883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8962943121686046091524709 1680551835316133642160883)
                      ·
                        rfl

theorem cell23_3272863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3272863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272863 prefixEnd_3272863 := by exact prefixLift 3272863
  have htrace : WordTrace (prefixWord ++ tailWord_3272863) baseStart_3272863 baseEnd_3272863 := by
    simpa [prefixWord, tailWord_3272863, baseEnd_3272863] using wordTrace_append hprefix tailTrace_3272863
  have hstable : (prefixWord ++ tailWord_3272863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272863).length < 2 ^ (prefixWord ++ tailWord_3272863).sum := by decide
  have hdescent : baseEnd_3272863 < baseStart_3272863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272883 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 3]
def baseStart_3272883 : Nat := 118140960795 + 3272883 * 2 ^ 59
def prefixEnd_3272883 : Nat := 4983230072969 + 3 ^ 40 * 3272883 * 2
def baseEnd_3272883 : Nat := 1680562104929223563910791

theorem tailTrace_3272883 : CollatzResearch.WordTrace tailWord_3272883 prefixEnd_3272883 1680562104929223563910791 := by
  unfold tailWord_3272883
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371849801911329760119303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79581233201274219840079535 119371849801911329760119303)
  ·
    refine ⟨179057774702866994640178955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119371849801911329760119303 179057774702866994640178955)
    ·
      refine ⟨268586662054300491960268433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179057774702866994640178955 268586662054300491960268433)
      ·
        refine ⟨201439996540725368970201325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268586662054300491960268433 201439996540725368970201325)
        ·
          refine ⟨75539998702772013363825497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201439996540725368970201325 75539998702772013363825497)
          ·
            refine ⟨56654999027079010022869123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75539998702772013363825497 56654999027079010022869123)
            ·
              refine ⟨84982498540618515034303685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56654999027079010022869123 84982498540618515034303685)
              ·
                refine ⟨15934218476365971568931941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84982498540618515034303685 15934218476365971568931941)
                ·
                  refine ⟨2987665964318619669174739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15934218476365971568931941 2987665964318619669174739)
                  ·
                    refine ⟨4481498946477929503762109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987665964318619669174739 4481498946477929503762109)
                    ·
                      refine ⟨1680562104929223563910791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481498946477929503762109 1680562104929223563910791)
                      ·
                        rfl

theorem cell23_3272883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_3272883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272883 prefixEnd_3272883 := by exact prefixLift 3272883
  have htrace : WordTrace (prefixWord ++ tailWord_3272883) baseStart_3272883 baseEnd_3272883 := by
    simpa [prefixWord, tailWord_3272883, baseEnd_3272883] using wordTrace_append hprefix tailTrace_3272883
  have hstable : (prefixWord ++ tailWord_3272883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272883).length < 2 ^ (prefixWord ++ tailWord_3272883).sum := by decide
  have hdescent : baseEnd_3272883 < baseStart_3272883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272887 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_3272887 : Nat := 118140960795 + 3272887 * 2 ^ 59
def prefixEnd_3272887 : Nat := 4983230072969 + 3 ^ 40 * 3272887 * 2
def baseEnd_3272887 : Nat := 1680564158851841548260773

theorem tailTrace_3272887 : CollatzResearch.WordTrace tailWord_3272887 prefixEnd_3272887 1680564158851841548260773 := by
  unfold tailWord_3272887
  simp only [CollatzResearch.WordTrace]
  refine ⟨119371995693896838443264915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79581330462597892295509943 119371995693896838443264915)
  ·
    refine ⟨179057993540845257664897373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119371995693896838443264915 179057993540845257664897373)
    ·
      refine ⟨67146747577816971624336515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179057993540845257664897373 67146747577816971624336515)
      ·
        refine ⟨100720121366725457436504773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67146747577816971624336515 100720121366725457436504773)
        ·
          refine ⟨18885022756261023269344645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100720121366725457436504773 18885022756261023269344645)
          ·
            refine ⟨3540941766798941863002121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18885022756261023269344645 3540941766798941863002121)
            ·
              refine ⟨2655706325099206397251591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540941766798941863002121 2655706325099206397251591)
              ·
                refine ⟨3983559487648809595877387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655706325099206397251591 3983559487648809595877387)
                ·
                  refine ⟨5975339231473214393816081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983559487648809595877387 5975339231473214393816081)
                  ·
                    refine ⟨4481504423604910795362061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5975339231473214393816081 4481504423604910795362061)
                    ·
                      refine ⟨1680564158851841548260773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481504423604910795362061 1680564158851841548260773)
                      ·
                        rfl

theorem cell23_3272887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_3272887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272887 prefixEnd_3272887 := by exact prefixLift 3272887
  have htrace : WordTrace (prefixWord ++ tailWord_3272887) baseStart_3272887 baseEnd_3272887 := by
    simpa [prefixWord, tailWord_3272887, baseEnd_3272887] using wordTrace_append hprefix tailTrace_3272887
  have hstable : (prefixWord ++ tailWord_3272887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272887).length < 2 ^ (prefixWord ++ tailWord_3272887).sum := by decide
  have hdescent : baseEnd_3272887 < baseStart_3272887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272894 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_3272894 : Nat := 118140960795 + 3272894 * 2 ^ 59
def prefixEnd_3272894 : Nat := 4983230072969 + 3 ^ 40 * 3272894 * 2
def baseEnd_3272894 : Nat := 560189251072141006957747

theorem tailTrace_3272894 : CollatzResearch.WordTrace tailWord_3272894 prefixEnd_3272894 560189251072141006957747 := by
  unfold tailWord_3272894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921531375608934829846217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79581500669914319092513157 14921531375608934829846217)
  ·
    refine ⟨11191148531706701122384663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14921531375608934829846217 11191148531706701122384663)
    ·
      refine ⟨16786722797560051683576995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191148531706701122384663 16786722797560051683576995)
      ·
        refine ⟨25180084196340077525365493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16786722797560051683576995 25180084196340077525365493)
        ·
          refine ⟨2360632893406882268003015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25180084196340077525365493 2360632893406882268003015)
          ·
            refine ⟨3540949340110323402004523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360632893406882268003015 3540949340110323402004523)
            ·
              refine ⟨5311424010165485103006785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540949340110323402004523 5311424010165485103006785)
              ·
                refine ⟨3983568007624113827255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311424010165485103006785 3983568007624113827255089)
                ·
                  refine ⟨2987676005718085370441317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983568007624113827255089 2987676005718085370441317)
                  ·
                    refine ⟨560189251072141006957747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987676005718085370441317 560189251072141006957747)
                    ·
                      rfl

theorem cell23_3272894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_3272894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272894 prefixEnd_3272894 := by exact prefixLift 3272894
  have htrace : WordTrace (prefixWord ++ tailWord_3272894) baseStart_3272894 baseEnd_3272894 := by
    simpa [prefixWord, tailWord_3272894, baseEnd_3272894] using wordTrace_append hprefix tailTrace_3272894
  have hstable : (prefixWord ++ tailWord_3272894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272894).length < 2 ^ (prefixWord ++ tailWord_3272894).sum := by decide
  have hdescent : baseEnd_3272894 < baseStart_3272894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272917 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3272917 : Nat := 118140960795 + 3272917 * 2 ^ 59
def prefixEnd_3272917 : Nat := 4983230072969 + 3 ^ 40 * 3272917 * 2
def baseEnd_3272917 : Nat := 1680579563271476430885635

theorem tailTrace_3272917 : CollatzResearch.WordTrace tailWord_3272917 prefixEnd_3272917 1680579563271476430885635 := by
  unfold tailWord_3272917
  simp only [CollatzResearch.WordTrace]
  refine ⟨119373089883788153566857005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79582059922525435711238003 119373089883788153566857005)
  ·
    refine ⟨44764908706420557587571377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119373089883788153566857005 44764908706420557587571377)
    ·
      refine ⟨33573681529815418190678533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44764908706420557587571377 33573681529815418190678533)
      ·
        refine ⟨6295065286840390910752225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33573681529815418190678533 6295065286840390910752225)
        ·
          refine ⟨4721298965130293183064169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6295065286840390910752225 4721298965130293183064169)
          ·
            refine ⟨3540974223847719887298127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4721298965130293183064169 3540974223847719887298127)
            ·
              refine ⟨5311461335771579830947191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540974223847719887298127 5311461335771579830947191)
              ·
                refine ⟨7967192003657369746420787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311461335771579830947191 7967192003657369746420787)
                ·
                  refine ⟨11950788005486054619631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7967192003657369746420787 11950788005486054619631181)
                  ·
                    refine ⟨4481545502057270482361693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11950788005486054619631181 4481545502057270482361693)
                    ·
                      refine ⟨1680579563271476430885635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481545502057270482361693 1680579563271476430885635)
                      ·
                        rfl

theorem cell23_3272917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3272917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272917 prefixEnd_3272917 := by exact prefixLift 3272917
  have htrace : WordTrace (prefixWord ++ tailWord_3272917) baseStart_3272917 baseEnd_3272917 := by
    simpa [prefixWord, tailWord_3272917, baseEnd_3272917] using wordTrace_append hprefix tailTrace_3272917
  have hstable : (prefixWord ++ tailWord_3272917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272917).length < 2 ^ (prefixWord ++ tailWord_3272917).sum := by decide
  have hdescent : baseEnd_3272917 < baseStart_3272917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272924 : List Nat := [2, 2, 5, 2, 2, 1, 2, 7]
def baseStart_3272924 : Nat := 118140960795 + 3272924 * 2 ^ 59
def prefixEnd_3272924 : Nat := 4983230072969 + 3 ^ 40 * 3272924 * 2
def baseEnd_3272924 : Nat := 62243820653187329759189

theorem tailTrace_3272924 : CollatzResearch.WordTrace tailWord_3272924 prefixEnd_3272924 62243820653187329759189 := by
  unfold tailWord_3272924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59686672597381396881180913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79582230129841862508241217 59686672597381396881180913)
  ·
    refine ⟨44765004448036047660885685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59686672597381396881180913 44765004448036047660885685)
    ·
      refine ⟨4196719167003379468208033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44765004448036047660885685 4196719167003379468208033)
      ·
        refine ⟨3147539375252534601156025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4196719167003379468208033 3147539375252534601156025)
        ·
          refine ⟨2360654531439400950867019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147539375252534601156025 2360654531439400950867019)
          ·
            refine ⟨3540981797159101426300529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360654531439400950867019 3540981797159101426300529)
            ·
              refine ⟨2655736347869326069725397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540981797159101426300529 2655736347869326069725397)
              ·
                refine ⟨62243820653187329759189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2655736347869326069725397 62243820653187329759189)
                ·
                  rfl

theorem cell23_3272924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 7].length) (baseStart_3272924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272924 prefixEnd_3272924 := by exact prefixLift 3272924
  have htrace : WordTrace (prefixWord ++ tailWord_3272924) baseStart_3272924 baseEnd_3272924 := by
    simpa [prefixWord, tailWord_3272924, baseEnd_3272924] using wordTrace_append hprefix tailTrace_3272924
  have hstable : (prefixWord ++ tailWord_3272924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272924).length < 2 ^ (prefixWord ++ tailWord_3272924).sum := by decide
  have hdescent : baseEnd_3272924 < baseStart_3272924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272940 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 6, 2, 2]
def baseStart_3272940 : Nat := 118140960795 + 3272940 * 2 ^ 59
def prefixEnd_3272940 : Nat := 4983230072969 + 3 ^ 40 * 3272940 * 2
def baseEnd_3272940 : Nat := 1680591373326529840898029

theorem tailTrace_3272940 : CollatzResearch.WordTrace tailWord_3272940 prefixEnd_3272940 1680591373326529840898029 := by
  unfold tailWord_3272940
  simp only [CollatzResearch.WordTrace]
  refine ⟨59686964381352414247472137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79582619175136552329962849 59686964381352414247472137)
  ·
    refine ⟨44765223286014310685604103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59686964381352414247472137 44765223286014310685604103)
    ·
      refine ⟨67147834929021466028406155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44765223286014310685604103 67147834929021466028406155)
      ·
        refine ⟨100721752393532199042609233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67147834929021466028406155 100721752393532199042609233)
        ·
          refine ⟨75541314295149149281956925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100721752393532199042609233 75541314295149149281956925)
          ·
            refine ⟨28327992860680930980733847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75541314295149149281956925 28327992860680930980733847)
            ·
              refine ⟨42491989291021396471100771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28327992860680930980733847 42491989291021396471100771)
              ·
                refine ⟨63737983936532094706651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42491989291021396471100771 63737983936532094706651157)
                ·
                  refine ⟨2987717997024941939374273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63737983936532094706651157 2987717997024941939374273)
                  ·
                    refine ⟨2240788497768706454530705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2987717997024941939374273 2240788497768706454530705)
                    ·
                      refine ⟨1680591373326529840898029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240788497768706454530705 1680591373326529840898029)
                      ·
                        rfl

theorem cell23_3272940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_3272940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272940 prefixEnd_3272940 := by exact prefixLift 3272940
  have htrace : WordTrace (prefixWord ++ tailWord_3272940) baseStart_3272940 baseEnd_3272940 := by
    simpa [prefixWord, tailWord_3272940, baseEnd_3272940] using wordTrace_append hprefix tailTrace_3272940
  have hstable : (prefixWord ++ tailWord_3272940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272940).length < 2 ^ (prefixWord ++ tailWord_3272940).sum := by decide
  have hdescent : baseEnd_3272940 < baseStart_3272940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272943 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_3272943 : Nat := 118140960795 + 3272943 * 2 ^ 59
def prefixEnd_3272943 : Nat := 4983230072969 + 3 ^ 40 * 3272943 * 2
def baseEnd_3272943 : Nat := 1680592913768493329160515

theorem tailTrace_3272943 : CollatzResearch.WordTrace tailWord_3272943 prefixEnd_3272943 1680592913768493329160515 := by
  unfold tailWord_3272943
  simp only [CollatzResearch.WordTrace]
  refine ⟨119374038181693960007303483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79582692121129306671535655 119374038181693960007303483)
  ·
    refine ⟨179061057272540940010955225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119374038181693960007303483 179061057272540940010955225)
    ·
      refine ⟨134295792954405705008216419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179061057272540940010955225 134295792954405705008216419)
      ·
        refine ⟨201443689431608557512324629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134295792954405705008216419 201443689431608557512324629)
        ·
          refine ⟨9442672942106651133390217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201443689431608557512324629 9442672942106651133390217)
          ·
            refine ⟨7082004706579988350042663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9442672942106651133390217 7082004706579988350042663)
            ·
              refine ⟨10623007059869982525063995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082004706579988350042663 10623007059869982525063995)
              ·
                refine ⟨15934510589804973787595993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10623007059869982525063995 15934510589804973787595993)
                ·
                  refine ⟨11950882942353730340696995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15934510589804973787595993 11950882942353730340696995)
                  ·
                    refine ⟨17926324413530595511045493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11950882942353730340696995 17926324413530595511045493)
                    ·
                      refine ⟨1680592913768493329160515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17926324413530595511045493 1680592913768493329160515)
                      ·
                        rfl

theorem cell23_3272943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_3272943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272943 prefixEnd_3272943 := by exact prefixLift 3272943
  have htrace : WordTrace (prefixWord ++ tailWord_3272943) baseStart_3272943 baseEnd_3272943 := by
    simpa [prefixWord, tailWord_3272943, baseEnd_3272943] using wordTrace_append hprefix tailTrace_3272943
  have hstable : (prefixWord ++ tailWord_3272943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272943).length < 2 ^ (prefixWord ++ tailWord_3272943).sum := by decide
  have hdescent : baseEnd_3272943 < baseStart_3272943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272993 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3272993 : Nat := 118140960795 + 3272993 * 2 ^ 59
def prefixEnd_3272993 : Nat := 4983230072969 + 3 ^ 40 * 3272993 * 2
def baseEnd_3272993 : Nat := 560206195933739377845095

theorem tailTrace_3272993 : CollatzResearch.WordTrace tailWord_3272993 prefixEnd_3272993 560206195933739377845095 := by
  unfold tailWord_3272993
  simp only [CollatzResearch.WordTrace]
  refine ⟨119375861831512818546623633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79583907887675212364415755 119375861831512818546623633)
  ·
    refine ⟨89531896373634613909967725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119375861831512818546623633 89531896373634613909967725)
    ·
      refine ⟨33574461140112980216237897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89531896373634613909967725 33574461140112980216237897)
      ·
        refine ⟨25180845855084735162178423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33574461140112980216237897 25180845855084735162178423)
        ·
          refine ⟨37771268782627102743267635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25180845855084735162178423 37771268782627102743267635)
          ·
            refine ⟨56656903173940654114901453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37771268782627102743267635 56656903173940654114901453)
            ·
              refine ⟨21246338690227745293088045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56656903173940654114901453 21246338690227745293088045)
              ·
                refine ⟨7967377008835404484908017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21246338690227745293088045 7967377008835404484908017)
                ·
                  refine ⟨5975532756626553363681013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7967377008835404484908017 5975532756626553363681013)
                  ·
                    refine ⟨560206195933739377845095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5975532756626553363681013 560206195933739377845095)
                    ·
                      rfl

theorem cell23_3272993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3272993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3272993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3272993 prefixEnd_3272993 := by exact prefixLift 3272993
  have htrace : WordTrace (prefixWord ++ tailWord_3272993) baseStart_3272993 baseEnd_3272993 := by
    simpa [prefixWord, tailWord_3272993, baseEnd_3272993] using wordTrace_append hprefix tailTrace_3272993
  have hstable : (prefixWord ++ tailWord_3272993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272993).length < 2 ^ (prefixWord ++ tailWord_3272993).sum := by decide
  have hdescent : baseEnd_3272993 < baseStart_3272993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273033 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_3273033 : Nat := 118140960795 + 3273033 * 2 ^ 59
def prefixEnd_3273033 : Nat := 4983230072969 + 3 ^ 40 * 3273033 * 2
def baseEnd_3273033 : Nat := 1680639127027397977035101

theorem tailTrace_3273033 : CollatzResearch.WordTrace tailWord_3273033 prefixEnd_3273033 1680639127027397977035101 := by
  unfold tailWord_3273033
  simp only [CollatzResearch.WordTrace]
  refine ⟨119377320751367905378079753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79584880500911936918719835 119377320751367905378079753)
  ·
    refine ⟨89532990563525929033559815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119377320751367905378079753 89532990563525929033559815)
    ·
      refine ⟨134299485845288893550339723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89532990563525929033559815 134299485845288893550339723)
      ·
        refine ⟨201449228767933340325509585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134299485845288893550339723 201449228767933340325509585)
        ·
          refine ⟨151086921575950005244132189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201449228767933340325509585 151086921575950005244132189)
          ·
            refine ⟨56657595590981251966549571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151086921575950005244132189 56657595590981251966549571)
            ·
              refine ⟨84986393386471877949824357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56657595590981251966549571 84986393386471877949824357)
              ·
                refine ⟨15934948759963477115592067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84986393386471877949824357 15934948759963477115592067)
                ·
                  refine ⟨23902423139945215673388101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15934948759963477115592067 23902423139945215673388101)
                  ·
                    refine ⟨4481704338739727938760269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23902423139945215673388101 4481704338739727938760269)
                    ·
                      refine ⟨1680639127027397977035101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481704338739727938760269 1680639127027397977035101)
                      ·
                        rfl

theorem cell23_3273033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_3273033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273033 prefixEnd_3273033 := by exact prefixLift 3273033
  have htrace : WordTrace (prefixWord ++ tailWord_3273033) baseStart_3273033 baseEnd_3273033 := by
    simpa [prefixWord, tailWord_3273033, baseEnd_3273033] using wordTrace_append hprefix tailTrace_3273033
  have hstable : (prefixWord ++ tailWord_3273033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273033).length < 2 ^ (prefixWord ++ tailWord_3273033).sum := by decide
  have hdescent : baseEnd_3273033 < baseStart_3273033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273040 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_3273040 : Nat := 118140960795 + 3273040 * 2 ^ 59
def prefixEnd_3273040 : Nat := 4983230072969 + 3 ^ 40 * 3273040 * 2
def baseEnd_3273040 : Nat := 560214240463993149882523

theorem tailTrace_3273040 : CollatzResearch.WordTrace tailWord_3273040 prefixEnd_3273040 560214240463993149882523 := by
  unfold tailWord_3273040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59688788031171272786792287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79585050708228363715723049 59688788031171272786792287)
  ·
    refine ⟨89533182046756909180188431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59688788031171272786792287 89533182046756909180188431)
    ·
      refine ⟨134299773070135363770282647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89533182046756909180188431 134299773070135363770282647)
      ·
        refine ⟨201449659605203045655423971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134299773070135363770282647 201449659605203045655423971)
        ·
          refine ⟨302174489407804568483135957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201449659605203045655423971 302174489407804568483135957)
          ·
            refine ⟨7082214595495419573823499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 302174489407804568483135957 7082214595495419573823499)
            ·
              refine ⟨10623321893243129360735249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082214595495419573823499 10623321893243129360735249)
              ·
                refine ⟨7967491419932347020551437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10623321893243129360735249 7967491419932347020551437)
                ·
                  refine ⟨2987809282474630132706789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7967491419932347020551437 2987809282474630132706789)
                  ·
                    refine ⟨560214240463993149882523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987809282474630132706789 560214240463993149882523)
                    ·
                      rfl

theorem cell23_3273040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_3273040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273040 prefixEnd_3273040 := by exact prefixLift 3273040
  have htrace : WordTrace (prefixWord ++ tailWord_3273040) baseStart_3273040 baseEnd_3273040 := by
    simpa [prefixWord, tailWord_3273040, baseEnd_3273040] using wordTrace_append hprefix tailTrace_3273040
  have hstable : (prefixWord ++ tailWord_3273040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273040).length < 2 ^ (prefixWord ++ tailWord_3273040).sum := by decide
  have hdescent : baseEnd_3273040 < baseStart_3273040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273097 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_3273097 : Nat := 118140960795 + 3273097 * 2 ^ 59
def prefixEnd_3273097 : Nat := 4983230072969 + 3 ^ 40 * 3273097 * 2
def baseEnd_3273097 : Nat := 1680671989789285726634807

theorem tailTrace_3273097 : CollatzResearch.WordTrace tailWord_3273097 prefixEnd_3273097 1680671989789285726634807 := by
  unfold tailWord_3273097
  simp only [CollatzResearch.WordTrace]
  refine ⟨119379655023136044308409545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79586436682090696205606363 119379655023136044308409545)
  ·
    refine ⟨89534741267352033231307159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119379655023136044308409545 89534741267352033231307159)
    ·
      refine ⟨134302111901028049846960739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89534741267352033231307159 134302111901028049846960739)
      ·
        refine ⟨201453167851542074770441109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134302111901028049846960739 201453167851542074770441109)
        ·
          refine ⟨9443117243041034754864427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201453167851542074770441109 9443117243041034754864427)
          ·
            refine ⟨14164675864561552132296641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9443117243041034754864427 14164675864561552132296641)
            ·
              refine ⟨10623506898421164099222481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14164675864561552132296641 10623506898421164099222481)
              ·
                refine ⟨7967630173815873074416861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10623506898421164099222481 7967630173815873074416861)
                ·
                  refine ⟨2987861315180952402906323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7967630173815873074416861 2987861315180952402906323)
                  ·
                    refine ⟨4481791972771428604359485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2987861315180952402906323 4481791972771428604359485)
                    ·
                      refine ⟨1680671989789285726634807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4481791972771428604359485 1680671989789285726634807)
                      ·
                        rfl

theorem cell23_3273097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_3273097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273097 prefixEnd_3273097 := by exact prefixLift 3273097
  have htrace : WordTrace (prefixWord ++ tailWord_3273097) baseStart_3273097 baseEnd_3273097 := by
    simpa [prefixWord, tailWord_3273097, baseEnd_3273097] using wordTrace_append hprefix tailTrace_3273097
  have hstable : (prefixWord ++ tailWord_3273097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273097).length < 2 ^ (prefixWord ++ tailWord_3273097).sum := by decide
  have hdescent : baseEnd_3273097 < baseStart_3273097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273100 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_3273100 : Nat := 118140960795 + 3273100 * 2 ^ 59
def prefixEnd_3273100 : Nat := 4983230072969 + 3 ^ 40 * 3273100 * 2
def baseEnd_3273100 : Nat := 560224510077083071632431

theorem tailTrace_3273100 : CollatzResearch.WordTrace tailWord_3273100 prefixEnd_3273100 560224510077083071632431 := by
  unfold tailWord_3273100
  simp only [CollatzResearch.WordTrace]
  refine ⟨59689882221062587910384377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79586509628083450547179169 59689882221062587910384377)
  ·
    refine ⟨44767411665796940932788283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59689882221062587910384377 44767411665796940932788283)
    ·
      refine ⟨67151117498695411399182425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44767411665796940932788283 67151117498695411399182425)
      ·
        refine ⟨50363338124021558549386819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67151117498695411399182425 50363338124021558549386819)
        ·
          refine ⟨75545007186032337824080229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50363338124021558549386819 75545007186032337824080229)
          ·
            refine ⟨14164688847381063342015043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75545007186032337824080229 14164688847381063342015043)
            ·
              refine ⟨21247033271071595013022565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14164688847381063342015043 21247033271071595013022565)
              ·
                refine ⟨3983818738325924064941731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21247033271071595013022565 3983818738325924064941731)
                ·
                  refine ⟨5975728107488886097412597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983818738325924064941731 5975728107488886097412597)
                  ·
                    refine ⟨560224510077083071632431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5975728107488886097412597 560224510077083071632431)
                    ·
                      rfl

theorem cell23_3273100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_3273100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273100 prefixEnd_3273100 := by exact prefixLift 3273100
  have htrace : WordTrace (prefixWord ++ tailWord_3273100) baseStart_3273100 baseEnd_3273100 := by
    simpa [prefixWord, tailWord_3273100, baseEnd_3273100] using wordTrace_append hprefix tailTrace_3273100
  have hstable : (prefixWord ++ tailWord_3273100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273100).length < 2 ^ (prefixWord ++ tailWord_3273100).sum := by decide
  have hdescent : baseEnd_3273100 < baseStart_3273100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273108 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3273108 : Nat := 118140960795 + 3273108 * 2 ^ 59
def prefixEnd_3273108 : Nat := 4983230072969 + 3 ^ 40 * 3273108 * 2
def baseEnd_3273108 : Nat := 560225879358828394532419

theorem tailTrace_3273108 : CollatzResearch.WordTrace tailWord_3273108 prefixEnd_3273108 560225879358828394532419 := by
  unfold tailWord_3273108
  simp only [CollatzResearch.WordTrace]
  refine ⟨59690028113048096593529989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79586704150730795458039985 59690028113048096593529989)
  ·
    refine ⟨11191880271196518111286873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59690028113048096593529989 11191880271196518111286873)
    ·
      refine ⟨8393910203397388583465155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11191880271196518111286873 8393910203397388583465155)
      ·
        refine ⟨12590865305096082875197733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393910203397388583465155 12590865305096082875197733)
        ·
          refine ⟨2360787244705515539099575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12590865305096082875197733 2360787244705515539099575)
          ·
            refine ⟨3541180867058273308649363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360787244705515539099575 3541180867058273308649363)
            ·
              refine ⟨5311771300587409962974045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541180867058273308649363 5311771300587409962974045)
              ·
                refine ⟨1991914237720278736115267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5311771300587409962974045 1991914237720278736115267)
                ·
                  refine ⟨2987871356580418104172901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991914237720278736115267 2987871356580418104172901)
                  ·
                    refine ⟨560225879358828394532419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2987871356580418104172901 560225879358828394532419)
                    ·
                      rfl

theorem cell23_3273108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3273108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273108 prefixEnd_3273108 := by exact prefixLift 3273108
  have htrace : WordTrace (prefixWord ++ tailWord_3273108) baseStart_3273108 baseEnd_3273108 := by
    simpa [prefixWord, tailWord_3273108, baseEnd_3273108] using wordTrace_append hprefix tailTrace_3273108
  have hstable : (prefixWord ++ tailWord_3273108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273108).length < 2 ^ (prefixWord ++ tailWord_3273108).sum := by decide
  have hdescent : baseEnd_3273108 < baseStart_3273108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273113 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_3273113 : Nat := 118140960795 + 3273113 * 2 ^ 59
def prefixEnd_3273113 : Nat := 4983230072969 + 3 ^ 40 * 3273113 * 2
def baseEnd_3273113 : Nat := 560226735159919221344911

theorem tailTrace_3273113 : CollatzResearch.WordTrace tailWord_3273113 prefixEnd_3273113 560226735159919221344911 := by
  unfold tailWord_3273113
  simp only [CollatzResearch.WordTrace]
  refine ⟨119380238591078079040991993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79586825727385386027327995 119380238591078079040991993)
  ·
    refine ⟨89535178943308559280743995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119380238591078079040991993 89535178943308559280743995)
    ·
      refine ⟨134302768414962838921115993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89535178943308559280743995 134302768414962838921115993)
      ·
        refine ⟨100727076311222129190836995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134302768414962838921115993 100727076311222129190836995)
        ·
          refine ⟨151090614466833193786255493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100727076311222129190836995 151090614466833193786255493)
          ·
            refine ⟨28329490212531223834922905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151090614466833193786255493 28329490212531223834922905)
            ·
              refine ⟨21247117659398417876192179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28329490212531223834922905 21247117659398417876192179)
              ·
                refine ⟨31870676489097626814288269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21247117659398417876192179 31870676489097626814288269)
                ·
                  refine ⟨11951503683411610055358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31870676489097626814288269 11951503683411610055358101)
                  ·
                    refine ⟨560226735159919221344911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11951503683411610055358101 560226735159919221344911)
                    ·
                      rfl

theorem cell23_3273113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_3273113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273113 prefixEnd_3273113 := by exact prefixLift 3273113
  have htrace : WordTrace (prefixWord ++ tailWord_3273113) baseStart_3273113 baseEnd_3273113 := by
    simpa [prefixWord, tailWord_3273113, baseEnd_3273113] using wordTrace_append hprefix tailTrace_3273113
  have hstable : (prefixWord ++ tailWord_3273113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273113).length < 2 ^ (prefixWord ++ tailWord_3273113).sum := by decide
  have hdescent : baseEnd_3273113 < baseStart_3273113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273143 : List Nat := [1, 1, 3, 1, 3, 3, 1, 10]
def baseStart_3273143 : Nat := 118140960795 + 3273143 * 2 ^ 59
def prefixEnd_3273143 : Nat := 4983230072969 + 3 ^ 40 * 3273143 * 2
def baseEnd_3273143 : Nat := 62247985551829353579985

theorem tailTrace_3273143 : CollatzResearch.WordTrace tailWord_3273143 prefixEnd_3273143 62247985551829353579985 := by
  unfold tailWord_3273143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119381332780969394164584083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79587555187312929443056055 119381332780969394164584083)
  ·
    refine ⟨179071999171454091246876125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119381332780969394164584083 179071999171454091246876125)
    ·
      refine ⟨67151999689295284217578547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179071999171454091246876125 67151999689295284217578547)
      ·
        refine ⟨100727999533942926326367821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67151999689295284217578547 100727999533942926326367821)
        ·
          refine ⟨37772999825228597372387933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100727999533942926326367821 37772999825228597372387933)
          ·
            refine ⟨14164874934460724014645475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37772999825228597372387933 14164874934460724014645475)
            ·
              refine ⟨21247312401691086021968213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14164874934460724014645475 21247312401691086021968213)
              ·
                refine ⟨62247985551829353579985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21247312401691086021968213 62247985551829353579985)
                ·
                  rfl

theorem cell23_3273143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 10].length) (baseStart_3273143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273143 prefixEnd_3273143 := by exact prefixLift 3273143
  have htrace : WordTrace (prefixWord ++ tailWord_3273143) baseStart_3273143 baseEnd_3273143 := by
    simpa [prefixWord, tailWord_3273143, baseEnd_3273143] using wordTrace_append hprefix tailTrace_3273143
  have hstable : (prefixWord ++ tailWord_3273143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273143).length < 2 ^ (prefixWord ++ tailWord_3273143).sum := by decide
  have hdescent : baseEnd_3273143 < baseStart_3273143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273150 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3273150 : Nat := 118140960795 + 3273150 * 2 ^ 59
def prefixEnd_3273150 : Nat := 4983230072969 + 3 ^ 40 * 3273150 * 2
def baseEnd_3273150 : Nat := 1680699204263974019272063

theorem tailTrace_3273150 : CollatzResearch.WordTrace tailWord_3273150 prefixEnd_3273150 1680699204263974019272063 := by
  unfold tailWord_3273150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922698511493004295011113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79587725394629356240059269 14922698511493004295011113)
  ·
    refine ⟨11192023883619753221258335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14922698511493004295011113 11192023883619753221258335)
    ·
      refine ⟨16788035825429629831887503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11192023883619753221258335 16788035825429629831887503)
      ·
        refine ⟨25182053738144444747831255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16788035825429629831887503 25182053738144444747831255)
        ·
          refine ⟨37773080607216667121746883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25182053738144444747831255 37773080607216667121746883)
          ·
            refine ⟨56659620910825000682620325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37773080607216667121746883 56659620910825000682620325)
            ·
              refine ⟨10623678920779687627991311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56659620910825000682620325 10623678920779687627991311)
              ·
                refine ⟨15935518381169531441986967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10623678920779687627991311 15935518381169531441986967)
                ·
                  refine ⟨23903277571754297162980451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15935518381169531441986967 23903277571754297162980451)
                  ·
                    refine ⟨35854916357631445744470677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23903277571754297162980451 35854916357631445744470677)
                    ·
                      refine ⟨1680699204263974019272063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35854916357631445744470677 1680699204263974019272063)
                      ·
                        rfl

theorem cell23_3273150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3273150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273150 prefixEnd_3273150 := by exact prefixLift 3273150
  have htrace : WordTrace (prefixWord ++ tailWord_3273150) baseStart_3273150 baseEnd_3273150 := by
    simpa [prefixWord, tailWord_3273150, baseEnd_3273150] using wordTrace_append hprefix tailTrace_3273150
  have hstable : (prefixWord ++ tailWord_3273150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273150).length < 2 ^ (prefixWord ++ tailWord_3273150).sum := by decide
  have hdescent : baseEnd_3273150 < baseStart_3273150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273222 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3273222 : Nat := 118140960795 + 3273222 * 2 ^ 59
def prefixEnd_3273222 : Nat := 4983230072969 + 3 ^ 40 * 3273222 * 2
def baseEnd_3273222 : Nat := 1680736174871097737571733

theorem tailTrace_3273222 : CollatzResearch.WordTrace tailWord_3273222 prefixEnd_3273222 1680736174871097737571733 := by
  unfold tailWord_3273222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730756692115099708022185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79589476098455460437806613 3730756692115099708022185)
  ·
    refine ⟨2798067519086324781016639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3730756692115099708022185 2798067519086324781016639)
    ·
      refine ⟨4197101278629487171524959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798067519086324781016639 4197101278629487171524959)
      ·
        refine ⟨6295651917944230757287439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197101278629487171524959 6295651917944230757287439)
        ·
          refine ⟨9443477876916346135931159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6295651917944230757287439 9443477876916346135931159)
          ·
            refine ⟨14165216815374519203896739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9443477876916346135931159 14165216815374519203896739)
            ·
              refine ⟨21247825223061778805845109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14165216815374519203896739 21247825223061778805845109)
              ·
                refine ⟨1991983614662041763047979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21247825223061778805845109 1991983614662041763047979)
                ·
                  refine ⟨2987975421993062644571969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991983614662041763047979 2987975421993062644571969)
                  ·
                    refine ⟨2240981566494796983428977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2987975421993062644571969 2240981566494796983428977)
                    ·
                      refine ⟨1680736174871097737571733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2240981566494796983428977 1680736174871097737571733)
                      ·
                        rfl

theorem cell23_3273222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3273222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273222 prefixEnd_3273222 := by exact prefixLift 3273222
  have htrace : WordTrace (prefixWord ++ tailWord_3273222) baseStart_3273222 baseEnd_3273222 := by
    simpa [prefixWord, tailWord_3273222, baseEnd_3273222] using wordTrace_append hprefix tailTrace_3273222
  have hstable : (prefixWord ++ tailWord_3273222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273222).length < 2 ^ (prefixWord ++ tailWord_3273222).sum := by decide
  have hdescent : baseEnd_3273222 < baseStart_3273222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273255 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3273255 : Nat := 118140960795 + 3273255 * 2 ^ 59
def prefixEnd_3273255 : Nat := 4983230072969 + 3 ^ 40 * 3273255 * 2
def baseEnd_3273255 : Nat := 1680753119732696108459081

theorem tailTrace_3273255 : CollatzResearch.WordTrace tailWord_3273255 prefixEnd_3273255 1680753119732696108459081 := by
  unfold tailWord_3273255
  simp only [CollatzResearch.WordTrace]
  refine ⟨119385417756563637292661219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79590278504375758195107479 119385417756563637292661219)
  ·
    refine ⟨179078126634845455938991829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119385417756563637292661219 179078126634845455938991829)
    ·
      refine ⟨4197143593004190373570121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 179078126634845455938991829 4197143593004190373570121)
      ·
        refine ⟨3147857694753142780177591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4197143593004190373570121 3147857694753142780177591)
        ·
          refine ⟨4721786542129714170266387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147857694753142780177591 4721786542129714170266387)
          ·
            refine ⟨7082679813194571255399581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721786542129714170266387 7082679813194571255399581)
            ·
              refine ⟨2656004929947964220774843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7082679813194571255399581 2656004929947964220774843)
              ·
                refine ⟨3984007394921946331162265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656004929947964220774843 3984007394921946331162265)
                ·
                  refine ⟨2988005546191459748371699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3984007394921946331162265 2988005546191459748371699)
                  ·
                    refine ⟨4482008319287189622557549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988005546191459748371699 4482008319287189622557549)
                    ·
                      refine ⟨1680753119732696108459081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482008319287189622557549 1680753119732696108459081)
                      ·
                        rfl

theorem cell23_3273255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3273255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273255 prefixEnd_3273255 := by exact prefixLift 3273255
  have htrace : WordTrace (prefixWord ++ tailWord_3273255) baseStart_3273255 baseEnd_3273255 := by
    simpa [prefixWord, tailWord_3273255, baseEnd_3273255] using wordTrace_append hprefix tailTrace_3273255
  have hstable : (prefixWord ++ tailWord_3273255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273255).length < 2 ^ (prefixWord ++ tailWord_3273255).sum := by decide
  have hdescent : baseEnd_3273255 < baseStart_3273255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273280 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_3273280 : Nat := 118140960795 + 3273280 * 2 ^ 59
def prefixEnd_3273280 : Nat := 4983230072969 + 3 ^ 40 * 3273280 * 2
def baseEnd_3273280 : Nat := 560255318916352836882155

theorem tailTrace_3273280 : CollatzResearch.WordTrace tailWord_3273280 prefixEnd_3273280 560255318916352836882155 := by
  unfold tailWord_3273280
  simp only [CollatzResearch.WordTrace]
  refine ⟨59693164790736533281160647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79590886387648711041547529 59693164790736533281160647)
  ·
    refine ⟨89539747186104799921740971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59693164790736533281160647 89539747186104799921740971)
    ·
      refine ⟨134309620779157199882611457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89539747186104799921740971 134309620779157199882611457)
      ·
        refine ⟨100732215584367899911958593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134309620779157199882611457 100732215584367899911958593)
        ·
          refine ⟨75549161688275924933968945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100732215584367899911958593 75549161688275924933968945)
          ·
            refine ⟨56661871266206943700476709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75549161688275924933968945 56661871266206943700476709)
            ·
              refine ⟨10624100862413801943839383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56661871266206943700476709 10624100862413801943839383)
              ·
                refine ⟨15936151293620702915759075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624100862413801943839383 15936151293620702915759075)
                ·
                  refine ⟨23904226940431054373638613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15936151293620702915759075 23904226940431054373638613)
                  ·
                    refine ⟨560255318916352836882155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23904226940431054373638613 560255318916352836882155)
                    ·
                      rfl

theorem cell23_3273280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_3273280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273280 prefixEnd_3273280 := by exact prefixLift 3273280
  have htrace : WordTrace (prefixWord ++ tailWord_3273280) baseStart_3273280 baseEnd_3273280 := by
    simpa [prefixWord, tailWord_3273280, baseEnd_3273280] using wordTrace_append hprefix tailTrace_3273280
  have hstable : (prefixWord ++ tailWord_3273280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273280).length < 2 ^ (prefixWord ++ tailWord_3273280).sum := by decide
  have hdescent : baseEnd_3273280 < baseStart_3273280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273297 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_3273297 : Nat := 118140960795 + 3273297 * 2 ^ 59
def prefixEnd_3273297 : Nat := 4983230072969 + 3 ^ 40 * 3273297 * 2
def baseEnd_3273297 : Nat := 560258228640061648044629

theorem tailTrace_3273297 : CollatzResearch.WordTrace tailWord_3273297 prefixEnd_3273297 560258228640061648044629 := by
  unfold tailWord_3273297
  simp only [CollatzResearch.WordTrace]
  refine ⟨119386949622411478465690145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79591299748274318977126763 119386949622411478465690145)
  ·
    refine ⟨89540212216808608849267609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119386949622411478465690145 89540212216808608849267609)
    ·
      refine ⟨67155159162606456636950707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89540212216808608849267609 67155159162606456636950707)
      ·
        refine ⟨100732738743909684955426061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67155159162606456636950707 100732738743909684955426061)
        ·
          refine ⟨37774777028966131858284773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100732738743909684955426061 37774777028966131858284773)
          ·
            refine ⟨7082770692931149723428395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37774777028966131858284773 7082770692931149723428395)
            ·
              refine ⟨10624156039396724585142593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7082770692931149723428395 10624156039396724585142593)
              ·
                refine ⟨7968117029547543438856945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624156039396724585142593 7968117029547543438856945)
                ·
                  refine ⟨5976087772160657579142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968117029547543438856945 5976087772160657579142709)
                  ·
                    refine ⟨560258228640061648044629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5976087772160657579142709 560258228640061648044629)
                    ·
                      rfl

theorem cell23_3273297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_3273297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273297 prefixEnd_3273297 := by exact prefixLift 3273297
  have htrace : WordTrace (prefixWord ++ tailWord_3273297) baseStart_3273297 baseEnd_3273297 := by
    simpa [prefixWord, tailWord_3273297, baseEnd_3273297] using wordTrace_append hprefix tailTrace_3273297
  have hstable : (prefixWord ++ tailWord_3273297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273297).length < 2 ^ (prefixWord ++ tailWord_3273297).sum := by decide
  have hdescent : baseEnd_3273297 < baseStart_3273297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273327 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 3, 4]
def baseStart_3273327 : Nat := 118140960795 + 3273327 * 2 ^ 59
def prefixEnd_3273327 : Nat := 4983230072969 + 3 ^ 40 * 3273327 * 2
def baseEnd_3273327 : Nat := 560263363446606608919583

theorem tailTrace_3273327 : CollatzResearch.WordTrace tailWord_3273327 prefixEnd_3273327 560263363446606608919583 := by
  unfold tailWord_3273327
  simp only [CollatzResearch.WordTrace]
  refine ⟨119388043812302793589282235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79592029208201862392854823 119388043812302793589282235)
  ·
    refine ⟨179082065718454190383923353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119388043812302793589282235 179082065718454190383923353)
    ·
      refine ⟨134311549288840642787942515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179082065718454190383923353 134311549288840642787942515)
      ·
        refine ⟨201467323933260964181913773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134311549288840642787942515 201467323933260964181913773)
        ·
          refine ⟨75550246474972861568217665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201467323933260964181913773 75550246474972861568217665)
          ·
            refine ⟨56662684856229646176163249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75550246474972861568217665 56662684856229646176163249)
            ·
              refine ⟨42497013642172234632122437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56662684856229646176163249 42497013642172234632122437)
              ·
                refine ⟨7968190057907293993522957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42497013642172234632122437 7968190057907293993522957)
                ·
                  refine ⟨2988071271715235247571109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7968190057907293993522957 2988071271715235247571109)
                  ·
                    refine ⟨560263363446606608919583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2988071271715235247571109 560263363446606608919583)
                    ·
                      rfl

theorem cell23_3273327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_3273327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273327 prefixEnd_3273327 := by exact prefixLift 3273327
  have htrace : WordTrace (prefixWord ++ tailWord_3273327) baseStart_3273327 baseEnd_3273327 := by
    simpa [prefixWord, tailWord_3273327, baseEnd_3273327] using wordTrace_append hprefix tailTrace_3273327
  have hstable : (prefixWord ++ tailWord_3273327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273327).length < 2 ^ (prefixWord ++ tailWord_3273327).sum := by decide
  have hdescent : baseEnd_3273327 < baseStart_3273327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273340 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 10]
def baseStart_3273340 : Nat := 118140960795 + 3273340 * 2 ^ 59
def prefixEnd_3273340 : Nat := 4983230072969 + 3 ^ 40 * 3273340 * 2
def baseEnd_3273340 : Nat := 186755196176480919544021

theorem tailTrace_3273340 : CollatzResearch.WordTrace tailWord_3273340 prefixEnd_3273340 186755196176480919544021 := by
  unfold tailWord_3273340
  simp only [CollatzResearch.WordTrace]
  refine ⟨59694258980627848404752737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79592345307503797873003649 59694258980627848404752737)
  ·
    refine ⟨44770694235470886303564553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59694258980627848404752737 44770694235470886303564553)
    ·
      refine ⟨33578020676603164727673415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44770694235470886303564553 33578020676603164727673415)
      ·
        refine ⟨50367031014904747091510123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33578020676603164727673415 50367031014904747091510123)
        ·
          refine ⟨75550546522357120637265185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50367031014904747091510123 75550546522357120637265185)
          ·
            refine ⟨56662909891767840477948889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75550546522357120637265185 56662909891767840477948889)
            ·
              refine ⟨42497182418825880358461667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56662909891767840477948889 42497182418825880358461667)
              ·
                refine ⟨63745773628238820537692501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42497182418825880358461667 63745773628238820537692501)
                ·
                  refine ⟨186755196176480919544021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63745773628238820537692501 186755196176480919544021)
                  ·
                    rfl

theorem cell23_3273340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_3273340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273340 prefixEnd_3273340 := by exact prefixLift 3273340
  have htrace : WordTrace (prefixWord ++ tailWord_3273340) baseStart_3273340 baseEnd_3273340 := by
    simpa [prefixWord, tailWord_3273340, baseEnd_3273340] using wordTrace_append hprefix tailTrace_3273340
  have hstable : (prefixWord ++ tailWord_3273340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273340).length < 2 ^ (prefixWord ++ tailWord_3273340).sum := by decide
  have hdescent : baseEnd_3273340 < baseStart_3273340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273374 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3273374 : Nat := 118140960795 + 3273374 * 2 ^ 59
def prefixEnd_3273374 : Nat := 4983230072969 + 3 ^ 40 * 3273374 * 2
def baseEnd_3273374 : Nat := 186757135992286793652337

theorem tailTrace_3273374 : CollatzResearch.WordTrace tailWord_3273374 prefixEnd_3273374 186757135992286793652337 := by
  unfold tailWord_3273374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14923719755391565077030397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79593172028755013744162117 14923719755391565077030397)
  ·
    refine ⟨5596394908271836903886399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14923719755391565077030397 5596394908271836903886399)
    ·
      refine ⟨8394592362407755355829599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5596394908271836903886399 8394592362407755355829599)
      ·
        refine ⟨12591888543611633033744399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394592362407755355829599 12591888543611633033744399)
        ·
          refine ⟨18887832815417449550616599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12591888543611633033744399 18887832815417449550616599)
          ·
            refine ⟨28331749223126174325924899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18887832815417449550616599 28331749223126174325924899)
            ·
              refine ⟨42497623834689261488887349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28331749223126174325924899 42497623834689261488887349)
              ·
                refine ⟨3984152234502118264583189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42497623834689261488887349 3984152234502118264583189)
                ·
                  refine ⟨186757135992286793652337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3984152234502118264583189 186757135992286793652337)
                  ·
                    rfl

theorem cell23_3273374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3273374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273374 prefixEnd_3273374 := by exact prefixLift 3273374
  have htrace : WordTrace (prefixWord ++ tailWord_3273374) baseStart_3273374 baseEnd_3273374 := by
    simpa [prefixWord, tailWord_3273374, baseEnd_3273374] using wordTrace_append hprefix tailTrace_3273374
  have hstable : (prefixWord ++ tailWord_3273374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273374).length < 2 ^ (prefixWord ++ tailWord_3273374).sum := by decide
  have hdescent : baseEnd_3273374 < baseStart_3273374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273404 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3273404 : Nat := 118140960795 + 3273404 * 2 ^ 59
def prefixEnd_3273404 : Nat := 4983230072969 + 3 ^ 40 * 3273404 * 2
def baseEnd_3273404 : Nat := 560276542783405341831965

theorem tailTrace_3273404 : CollatzResearch.WordTrace tailWord_3273404 prefixEnd_3273404 560276542783405341831965 := by
  unfold tailWord_3273404
  simp only [CollatzResearch.WordTrace]
  refine ⟨59695426116511917869917633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79593901488682557159890177 59695426116511917869917633)
  ·
    refine ⟨44771569587383938402438225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59695426116511917869917633 44771569587383938402438225)
    ·
      refine ⟨33578677190537953801828669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44771569587383938402438225 33578677190537953801828669)
      ·
        refine ⟨12592003946451732675685751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33578677190537953801828669 12592003946451732675685751)
        ·
          refine ⟨18888005919677599013528627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12592003946451732675685751 18888005919677599013528627)
          ·
            refine ⟨28332008879516398520292941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18888005919677599013528627 28332008879516398520292941)
            ·
              refine ⟨10624503329818649445109853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28332008879516398520292941 10624503329818649445109853)
              ·
                refine ⟨3984188748681993541916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10624503329818649445109853 3984188748681993541916195)
                ·
                  refine ⟨5976283123022990312874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984188748681993541916195 5976283123022990312874293)
                  ·
                    refine ⟨560276542783405341831965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5976283123022990312874293 560276542783405341831965)
                    ·
                      rfl

theorem cell23_3273404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3273404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273404 prefixEnd_3273404 := by exact prefixLift 3273404
  have htrace : WordTrace (prefixWord ++ tailWord_3273404) baseStart_3273404 baseEnd_3273404 := by
    simpa [prefixWord, tailWord_3273404, baseEnd_3273404] using wordTrace_append hprefix tailTrace_3273404
  have hstable : (prefixWord ++ tailWord_3273404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273404).length < 2 ^ (prefixWord ++ tailWord_3273404).sum := by decide
  have hdescent : baseEnd_3273404 < baseStart_3273404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273418 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_3273418 : Nat := 118140960795 + 3273418 * 2 ^ 59
def prefixEnd_3273418 : Nat := 4983230072969 + 3 ^ 40 * 3273418 * 2
def baseEnd_3273418 : Nat := 1680836817079378970720831

theorem tailTrace_3273418 : CollatzResearch.WordTrace tailWord_3273418 prefixEnd_3273418 1680836817079378970720831 := by
  unfold tailWord_3273418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29847840713743279032711227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79594241903315410753896605 29847840713743279032711227)
  ·
    refine ⟨44771761070614918549066841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29847840713743279032711227 44771761070614918549066841)
    ·
      refine ⟨33578820802961188911800131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44771761070614918549066841 33578820802961188911800131)
      ·
        refine ⟨50368231204441783367700197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33578820802961188911800131 50368231204441783367700197)
        ·
          refine ⟨9444043350832834381443787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50368231204441783367700197 9444043350832834381443787)
          ·
            refine ⟨14166065026249251572165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444043350832834381443787 14166065026249251572165681)
            ·
              refine ⟨10624548769686938679124261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14166065026249251572165681 10624548769686938679124261)
              ·
                refine ⟨1992102894316301002335799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10624548769686938679124261 1992102894316301002335799)
                ·
                  refine ⟨2988154341474451503503699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992102894316301002335799 2988154341474451503503699)
                  ·
                    refine ⟨4482231512211677255255549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988154341474451503503699 4482231512211677255255549)
                    ·
                      refine ⟨1680836817079378970720831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482231512211677255255549 1680836817079378970720831)
                      ·
                        rfl

theorem cell23_3273418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_3273418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273418 prefixEnd_3273418 := by exact prefixLift 3273418
  have htrace : WordTrace (prefixWord ++ tailWord_3273418) baseStart_3273418 baseEnd_3273418 := by
    simpa [prefixWord, tailWord_3273418, baseEnd_3273418] using wordTrace_append hprefix tailTrace_3273418
  have hstable : (prefixWord ++ tailWord_3273418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273418).length < 2 ^ (prefixWord ++ tailWord_3273418).sum := by decide
  have hdescent : baseEnd_3273418 < baseStart_3273418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273441 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_3273441 : Nat := 118140960795 + 3273441 * 2 ^ 59
def prefixEnd_3273441 : Nat := 4983230072969 + 3 ^ 40 * 3273441 * 2
def baseEnd_3273441 : Nat := 1680848627134432380733225

theorem tailTrace_3273441 : CollatzResearch.WordTrace tailWord_3273441 prefixEnd_3273441 1680848627134432380733225 := by
  unfold tailWord_3273441
  simp only [CollatzResearch.WordTrace]
  refine ⟨119392201733889791058932177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79594801155926527372621451 119392201733889791058932177)
  ·
    refine ⟨89544151300417343294199133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119392201733889791058932177 89544151300417343294199133)
    ·
      refine ⟨33579056737656503735324675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89544151300417343294199133 33579056737656503735324675)
      ·
        refine ⟨50368585106484755602987013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33579056737656503735324675 50368585106484755602987013)
        ·
          refine ⟨9444109707465891675560065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50368585106484755602987013 9444109707465891675560065)
          ·
            refine ⟨7083082280599418756670049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9444109707465891675560065 7083082280599418756670049)
            ·
              refine ⟨5312311710449564067502537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083082280599418756670049 5312311710449564067502537)
              ·
                refine ⟨3984233782837173050626903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312311710449564067502537 3984233782837173050626903)
                ·
                  refine ⟨5976350674255759575940355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984233782837173050626903 5976350674255759575940355)
                  ·
                    refine ⟨8964526011383639363910533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5976350674255759575940355 8964526011383639363910533)
                    ·
                      refine ⟨1680848627134432380733225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8964526011383639363910533 1680848627134432380733225)
                      ·
                        rfl

theorem cell23_3273441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_3273441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273441 prefixEnd_3273441 := by exact prefixLift 3273441
  have htrace : WordTrace (prefixWord ++ tailWord_3273441) baseStart_3273441 baseEnd_3273441 := by
    simpa [prefixWord, tailWord_3273441, baseEnd_3273441] using wordTrace_append hprefix tailTrace_3273441
  have hstable : (prefixWord ++ tailWord_3273441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273441).length < 2 ^ (prefixWord ++ tailWord_3273441).sum := by decide
  have hdescent : baseEnd_3273441 < baseStart_3273441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273484 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 7, 2]
def baseStart_3273484 : Nat := 118140960795 + 3273484 * 2 ^ 59
def prefixEnd_3273484 : Nat := 4983230072969 + 3 ^ 40 * 3273484 * 2
def baseEnd_3273484 : Nat := 1680870706802575712495527

theorem tailTrace_3273484 : CollatzResearch.WordTrace tailWord_3273484 prefixEnd_3273484 1680870706802575712495527 := by
  unfold tailWord_3273484
  simp only [CollatzResearch.WordTrace]
  refine ⟨59696885036367004701373753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79595846715156006268498337 59696885036367004701373753)
  ·
    refine ⟨44772663777275253526030315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59696885036367004701373753 44772663777275253526030315)
    ·
      refine ⟨67158995665912880289045473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44772663777275253526030315 67158995665912880289045473)
      ·
        refine ⟨50369246749434660216784105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67158995665912880289045473 50369246749434660216784105)
        ·
          refine ⟨37776935062075995162588079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50369246749434660216784105 37776935062075995162588079)
          ·
            refine ⟨56665402593113992743882119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37776935062075995162588079 56665402593113992743882119)
            ·
              refine ⟨84998103889670989115823179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56665402593113992743882119 84998103889670989115823179)
              ·
                refine ⟨127497155834506483673734769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84998103889670989115823179 127497155834506483673734769)
                ·
                  refine ⟨95622866875879862755301077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127497155834506483673734769 95622866875879862755301077)
                  ·
                    refine ⟨2241160942403434283327369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95622866875879862755301077 2241160942403434283327369)
                    ·
                      refine ⟨1680870706802575712495527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241160942403434283327369 1680870706802575712495527)
                      ·
                        rfl

theorem cell23_3273484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_3273484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273484 prefixEnd_3273484 := by exact prefixLift 3273484
  have htrace : WordTrace (prefixWord ++ tailWord_3273484) baseStart_3273484 baseEnd_3273484 := by
    simpa [prefixWord, tailWord_3273484, baseEnd_3273484] using wordTrace_append hprefix tailTrace_3273484
  have hstable : (prefixWord ++ tailWord_3273484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273484).length < 2 ^ (prefixWord ++ tailWord_3273484).sum := by decide
  have hdescent : baseEnd_3273484 < baseStart_3273484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273491 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 3]
def baseStart_3273491 : Nat := 118140960795 + 3273491 * 2 ^ 59
def prefixEnd_3273491 : Nat := 4983230072969 + 3 ^ 40 * 3273491 * 2
def baseEnd_3273491 : Nat := 1680874301167157185107995

theorem tailTrace_3273491 : CollatzResearch.WordTrace tailWord_3273491 prefixEnd_3273491 1680874301167157185107995 := by
  unfold tailWord_3273491
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394025383708649598252327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596016922472433065501551 119394025383708649598252327)
  ·
    refine ⟨179091038075562974397378491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119394025383708649598252327 179091038075562974397378491)
    ·
      refine ⟨268636557113344461596067737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179091038075562974397378491 268636557113344461596067737)
      ·
        refine ⟨201477417835008346197050803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268636557113344461596067737 201477417835008346197050803)
        ·
          refine ⟨302216126752512519295576205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201477417835008346197050803 302216126752512519295576205)
          ·
            refine ⟨113331047532192194735841077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302216126752512519295576205 113331047532192194735841077)
            ·
              refine ⟨10624785706143018256485101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113331047532192194735841077 10624785706143018256485101)
              ·
                refine ⟨3984294639803631846181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10624785706143018256485101 3984294639803631846181913)
                ·
                  refine ⟨2988220979852723884636435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3984294639803631846181913 2988220979852723884636435)
                  ·
                    refine ⟨4482331469779085826954653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988220979852723884636435 4482331469779085826954653)
                    ·
                      refine ⟨1680874301167157185107995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482331469779085826954653 1680874301167157185107995)
                      ·
                        rfl

theorem cell23_3273491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_3273491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273491 prefixEnd_3273491 := by exact prefixLift 3273491
  have htrace : WordTrace (prefixWord ++ tailWord_3273491) baseStart_3273491 baseEnd_3273491 := by
    simpa [prefixWord, tailWord_3273491, baseEnd_3273491] using wordTrace_append hprefix tailTrace_3273491
  have hstable : (prefixWord ++ tailWord_3273491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273491).length < 2 ^ (prefixWord ++ tailWord_3273491).sum := by decide
  have hdescent : baseEnd_3273491 < baseStart_3273491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273495 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3273495 : Nat := 118140960795 + 3273495 * 2 ^ 59
def prefixEnd_3273495 : Nat := 4983230072969 + 3 ^ 40 * 3273495 * 2
def baseEnd_3273495 : Nat := 1680876355089775169457977

theorem tailTrace_3273495 : CollatzResearch.WordTrace tailWord_3273495 prefixEnd_3273495 1680876355089775169457977 := by
  unfold tailWord_3273495
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394171275694158281397939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596114183796105520931959 119394171275694158281397939)
  ·
    refine ⟨179091256913541237422096909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119394171275694158281397939 179091256913541237422096909)
    ·
      refine ⟨67159221342577964033286341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179091256913541237422096909 67159221342577964033286341)
      ·
        refine ⟨12592354001733368256241189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67159221342577964033286341 12592354001733368256241189)
        ·
          refine ⟨2361066375325006548045223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12592354001733368256241189 2361066375325006548045223)
          ·
            refine ⟨3541599562987509822067835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361066375325006548045223 3541599562987509822067835)
            ·
              refine ⟨5312399344481264733101753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541599562987509822067835 5312399344481264733101753)
              ·
                refine ⟨3984299508360948549826315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312399344481264733101753 3984299508360948549826315)
                ·
                  refine ⟨5976449262541422824739473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984299508360948549826315 5976449262541422824739473)
                  ·
                    refine ⟨4482336946906067118554605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976449262541422824739473 4482336946906067118554605)
                    ·
                      refine ⟨1680876355089775169457977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482336946906067118554605 1680876355089775169457977)
                      ·
                        rfl

theorem cell23_3273495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3273495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273495 prefixEnd_3273495 := by exact prefixLift 3273495
  have htrace : WordTrace (prefixWord ++ tailWord_3273495) baseStart_3273495 baseEnd_3273495 := by
    simpa [prefixWord, tailWord_3273495, baseEnd_3273495] using wordTrace_append hprefix tailTrace_3273495
  have hstable : (prefixWord ++ tailWord_3273495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273495).length < 2 ^ (prefixWord ++ tailWord_3273495).sum := by decide
  have hdescent : baseEnd_3273495 < baseStart_3273495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273497 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3273497 : Nat := 118140960795 + 3273497 * 2 ^ 59
def prefixEnd_3273497 : Nat := 4983230072969 + 3 ^ 40 * 3273497 * 2
def baseEnd_3273497 : Nat := 1680877382051084161632967

theorem tailTrace_3273497 : CollatzResearch.WordTrace tailWord_3273497 prefixEnd_3273497 1680877382051084161632967 := by
  unfold tailWord_3273497
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394244221686912622970745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596162814457941748647163 119394244221686912622970745)
  ·
    refine ⟨89545683166265184467228059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119394244221686912622970745 89545683166265184467228059)
    ·
      refine ⟨134318524749397776700842089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89545683166265184467228059 134318524749397776700842089)
      ·
        refine ⟨100738893562048332525631567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134318524749397776700842089 100738893562048332525631567)
        ·
          refine ⟨151108340343072498788447351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100738893562048332525631567 151108340343072498788447351)
          ·
            refine ⟨226662510514608748182671027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151108340343072498788447351 226662510514608748182671027)
            ·
              refine ⟨339993765771913122274006541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226662510514608748182671027 339993765771913122274006541)
              ·
                refine ⟨127497662164467420852752453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339993765771913122274006541 127497662164467420852752453)
                ·
                  refine ⟨23905811655837641409891085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127497662164467420852752453 23905811655837641409891085)
                  ·
                    refine ⟨8964679370939115528709157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23905811655837641409891085 8964679370939115528709157)
                    ·
                      refine ⟨1680877382051084161632967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8964679370939115528709157 1680877382051084161632967)
                      ·
                        rfl

theorem cell23_3273497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3273497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273497 prefixEnd_3273497 := by exact prefixLift 3273497
  have htrace : WordTrace (prefixWord ++ tailWord_3273497) baseStart_3273497 baseEnd_3273497 := by
    simpa [prefixWord, tailWord_3273497, baseEnd_3273497] using wordTrace_append hprefix tailTrace_3273497
  have hstable : (prefixWord ++ tailWord_3273497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273497).length < 2 ^ (prefixWord ++ tailWord_3273497).sum := by decide
  have hdescent : baseEnd_3273497 < baseStart_3273497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273507 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 6]
def baseStart_3273507 : Nat := 118140960795 + 3273507 * 2 ^ 59
def prefixEnd_3273507 : Nat := 4983230072969 + 3 ^ 40 * 3273507 * 2
def baseEnd_3273507 : Nat := 560294172285876374169307

theorem tailTrace_3273507 : CollatzResearch.WordTrace tailWord_3273507 prefixEnd_3273507 560294172285876374169307 := by
  unfold tailWord_3273507
  simp only [CollatzResearch.WordTrace]
  refine ⟨119394608951650684330834775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79596405967767122887223183 119394608951650684330834775)
  ·
    refine ⟨179091913427476026496252163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119394608951650684330834775 179091913427476026496252163)
    ·
      refine ⟨268637870141214039744378245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179091913427476026496252163 268637870141214039744378245)
      ·
        refine ⟨50369600651477632452070921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268637870141214039744378245 50369600651477632452070921)
        ·
          refine ⟨37777200488608224339053191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50369600651477632452070921 37777200488608224339053191)
          ·
            refine ⟨56665800732912336508579787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37777200488608224339053191 56665800732912336508579787)
            ·
              refine ⟨84998701099368504762869681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56665800732912336508579787 84998701099368504762869681)
              ·
                refine ⟨63749025824526378572152261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84998701099368504762869681 63749025824526378572152261)
                ·
                  refine ⟨11952942342098695982278549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63749025824526378572152261 11952942342098695982278549)
                  ·
                    refine ⟨560294172285876374169307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11952942342098695982278549 560294172285876374169307)
                    ·
                      rfl

theorem cell23_3273507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 6].length) (baseStart_3273507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273507 prefixEnd_3273507 := by exact prefixLift 3273507
  have htrace : WordTrace (prefixWord ++ tailWord_3273507) baseStart_3273507 baseEnd_3273507 := by
    simpa [prefixWord, tailWord_3273507, baseEnd_3273507] using wordTrace_append hprefix tailTrace_3273507
  have hstable : (prefixWord ++ tailWord_3273507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273507).length < 2 ^ (prefixWord ++ tailWord_3273507).sum := by decide
  have hdescent : baseEnd_3273507 < baseStart_3273507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273526 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3273526 : Nat := 118140960795 + 3273526 * 2 ^ 59
def prefixEnd_3273526 : Nat := 4983230072969 + 3 ^ 40 * 3273526 * 2
def baseEnd_3273526 : Nat := 1680892272990064548170335

theorem tailTrace_3273526 : CollatzResearch.WordTrace tailWord_3273526 prefixEnd_3273526 1680892272990064548170335 := by
  unfold tailWord_3273526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462206371161365660986027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79596867959054567050517621 7462206371161365660986027)
  ·
    refine ⟨11193309556742048491479041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7462206371161365660986027 11193309556742048491479041)
    ·
      refine ⟨8394982167556536368609281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11193309556742048491479041 8394982167556536368609281)
      ·
        refine ⟨6296236625667402276456961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8394982167556536368609281 6296236625667402276456961)
        ·
          refine ⟨4722177469250551707342721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296236625667402276456961 4722177469250551707342721)
          ·
            refine ⟨3541633101937913780507041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4722177469250551707342721 3541633101937913780507041)
            ·
              refine ⟨2656224826453435335380281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3541633101937913780507041 2656224826453435335380281)
              ·
                refine ⟨1992168619840076501535211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656224826453435335380281 1992168619840076501535211)
                ·
                  refine ⟨2988252929760114752302817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992168619840076501535211 2988252929760114752302817)
                  ·
                    refine ⟨2241189697320086064227113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2988252929760114752302817 2241189697320086064227113)
                    ·
                      refine ⟨1680892272990064548170335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241189697320086064227113 1680892272990064548170335)
                      ·
                        rfl

theorem cell23_3273526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3273526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273526 prefixEnd_3273526 := by exact prefixLift 3273526
  have htrace : WordTrace (prefixWord ++ tailWord_3273526) baseStart_3273526 baseEnd_3273526 := by
    simpa [prefixWord, tailWord_3273526, baseEnd_3273526] using wordTrace_append hprefix tailTrace_3273526
  have hstable : (prefixWord ++ tailWord_3273526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273526).length < 2 ^ (prefixWord ++ tailWord_3273526).sum := by decide
  have hdescent : baseEnd_3273526 < baseStart_3273526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273544 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3273544 : Nat := 118140960795 + 3273544 * 2 ^ 59
def prefixEnd_3273544 : Nat := 4983230072969 + 3 ^ 40 * 3273544 * 2
def baseEnd_3273544 : Nat := 1680901515641845477745251

theorem tailTrace_3273544 : CollatzResearch.WordTrace tailWord_3273544 prefixEnd_3273544 1680901515641845477745251 := by
  unfold tailWord_3273544
  simp only [CollatzResearch.WordTrace]
  refine ⟨59697979226258319824965843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79597305635011093099954457 59697979226258319824965843)
  ·
    refine ⟨89546968839387479737448765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59697979226258319824965843 89546968839387479737448765)
    ·
      refine ⟨33580113314770304901543287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89546968839387479737448765 33580113314770304901543287)
      ·
        refine ⟨50370169972155457352314931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33580113314770304901543287 50370169972155457352314931)
        ·
          refine ⟨75555254958233186028472397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50370169972155457352314931 75555254958233186028472397)
          ·
            refine ⟨28333220609337444760677149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75555254958233186028472397 28333220609337444760677149)
            ·
              refine ⟨10624957728501541785253931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28333220609337444760677149 10624957728501541785253931)
              ·
                refine ⟨15937436592752312677880897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10624957728501541785253931 15937436592752312677880897)
                ·
                  refine ⟨11953077444564234508410673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15937436592752312677880897 11953077444564234508410673)
                  ·
                    refine ⟨8964808083423175881308005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11953077444564234508410673 8964808083423175881308005)
                    ·
                      refine ⟨1680901515641845477745251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8964808083423175881308005 1680901515641845477745251)
                      ·
                        rfl

theorem cell23_3273544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3273544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273544 prefixEnd_3273544 := by exact prefixLift 3273544
  have htrace : WordTrace (prefixWord ++ tailWord_3273544) baseStart_3273544 baseEnd_3273544 := by
    simpa [prefixWord, tailWord_3273544, baseEnd_3273544] using wordTrace_append hprefix tailTrace_3273544
  have hstable : (prefixWord ++ tailWord_3273544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273544).length < 2 ^ (prefixWord ++ tailWord_3273544).sum := by decide
  have hdescent : baseEnd_3273544 < baseStart_3273544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273548 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3273548 : Nat := 118140960795 + 3273548 * 2 ^ 59
def prefixEnd_3273548 : Nat := 4983230072969 + 3 ^ 40 * 3273548 * 2
def baseEnd_3273548 : Nat := 1680903569564463462095233

theorem tailTrace_3273548 : CollatzResearch.WordTrace tailWord_3273548 prefixEnd_3273548 1680903569564463462095233 := by
  unfold tailWord_3273548
  simp only [CollatzResearch.WordTrace]
  refine ⟨59698052172251074166538649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79597402896334765555384865 59698052172251074166538649)
  ·
    refine ⟨44773539129188305624903987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59698052172251074166538649 44773539129188305624903987)
    ·
      refine ⟨67160308693782458437355981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44773539129188305624903987 67160308693782458437355981)
      ·
        refine ⟨25185115760168421914008493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67160308693782458437355981 25185115760168421914008493)
        ·
          refine ⟨9444418410063158217753185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25185115760168421914008493 9444418410063158217753185)
          ·
            refine ⟨7083313807547368663314889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9444418410063158217753185 7083313807547368663314889)
            ·
              refine ⟨5312485355660526497486167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083313807547368663314889 5312485355660526497486167)
              ·
                refine ⟨7968728033490789746229251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312485355660526497486167 7968728033490789746229251)
                ·
                  refine ⟨11953092050236184619343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7968728033490789746229251 11953092050236184619343877)
                  ·
                    refine ⟨2241204759419284616126977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11953092050236184619343877 2241204759419284616126977)
                    ·
                      refine ⟨1680903569564463462095233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241204759419284616126977 1680903569564463462095233)
                      ·
                        rfl

theorem cell23_3273548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3273548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273548 prefixEnd_3273548 := by exact prefixLift 3273548
  have htrace : WordTrace (prefixWord ++ tailWord_3273548) baseStart_3273548 baseEnd_3273548 := by
    simpa [prefixWord, tailWord_3273548, baseEnd_3273548] using wordTrace_append hprefix tailTrace_3273548
  have hstable : (prefixWord ++ tailWord_3273548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273548).length < 2 ^ (prefixWord ++ tailWord_3273548).sum := by decide
  have hdescent : baseEnd_3273548 < baseStart_3273548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273554 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_3273554 : Nat := 118140960795 + 3273554 * 2 ^ 59
def prefixEnd_3273554 : Nat := 4983230072969 + 3 ^ 40 * 3273554 * 2
def baseEnd_3273554 : Nat := 186767405605376715402245

theorem tailTrace_3273554 : CollatzResearch.WordTrace tailWord_3273554 prefixEnd_3273554 186767405605376715402245 := by
  unfold tailWord_3273554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29849080795620102839448929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79597548788320274238530477 29849080795620102839448929)
  ·
    refine ⟨22386810596715077129586697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29849080795620102839448929 22386810596715077129586697)
    ·
      refine ⟨16790107947536307847190023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22386810596715077129586697 16790107947536307847190023)
      ·
        refine ⟨25185161921304461770785035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16790107947536307847190023 25185161921304461770785035)
        ·
          refine ⟨37777742881956692656177553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25185161921304461770785035 37777742881956692656177553)
          ·
            refine ⟨28333307161467519492133165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37777742881956692656177553 28333307161467519492133165)
            ·
              refine ⟨10624990185550319809549937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28333307161467519492133165 10624990185550319809549937)
              ·
                refine ⟨7968742639162739857162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10624990185550319809549937 7968742639162739857162453)
                ·
                  refine ⟨186767405605376715402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7968742639162739857162453 186767405605376715402245)
                  ·
                    rfl

theorem cell23_3273554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_3273554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273554 prefixEnd_3273554 := by exact prefixLift 3273554
  have htrace : WordTrace (prefixWord ++ tailWord_3273554) baseStart_3273554 baseEnd_3273554 := by
    simpa [prefixWord, tailWord_3273554, baseEnd_3273554] using wordTrace_append hprefix tailTrace_3273554
  have hstable : (prefixWord ++ tailWord_3273554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273554).length < 2 ^ (prefixWord ++ tailWord_3273554).sum := by decide
  have hdescent : baseEnd_3273554 < baseStart_3273554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273571 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 5]
def baseStart_3273571 : Nat := 118140960795 + 3273571 * 2 ^ 59
def prefixEnd_3273571 : Nat := 4983230072969 + 3 ^ 40 * 3273571 * 2
def baseEnd_3273571 : Nat := 186768375513279652456403

theorem tailTrace_3273571 : CollatzResearch.WordTrace tailWord_3273571 prefixEnd_3273571 186768375513279652456403 := by
  unfold tailWord_3273571
  simp only [CollatzResearch.WordTrace]
  refine ⟨119396943223418823261164567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79597962148945882174109711 119396943223418823261164567)
  ·
    refine ⟨179095414835128234891746851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119396943223418823261164567 179095414835128234891746851)
    ·
      refine ⟨268643122252692352337620277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179095414835128234891746851 268643122252692352337620277)
      ·
        refine ⟨25185292711189908031651901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268643122252692352337620277 25185292711189908031651901)
        ·
          refine ⟨9444484766696215511869463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25185292711189908031651901 9444484766696215511869463)
          ·
            refine ⟨14166727150044323267804195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444484766696215511869463 14166727150044323267804195)
            ·
              refine ⟨21250090725066484901706293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14166727150044323267804195 21250090725066484901706293)
              ·
                refine ⟨1992196005474982959534965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21250090725066484901706293 1992196005474982959534965)
                ·
                  refine ⟨186768375513279652456403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992196005474982959534965 186768375513279652456403)
                  ·
                    rfl

theorem cell23_3273571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 5].length) (baseStart_3273571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273571 prefixEnd_3273571 := by exact prefixLift 3273571
  have htrace : WordTrace (prefixWord ++ tailWord_3273571) baseStart_3273571 baseEnd_3273571 := by
    simpa [prefixWord, tailWord_3273571, baseEnd_3273571] using wordTrace_append hprefix tailTrace_3273571
  have hstable : (prefixWord ++ tailWord_3273571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273571).length < 2 ^ (prefixWord ++ tailWord_3273571).sum := by decide
  have hdescent : baseEnd_3273571 < baseStart_3273571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273584 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_3273584 : Nat := 118140960795 + 3273584 * 2 ^ 59
def prefixEnd_3273584 : Nat := 4983230072969 + 3 ^ 40 * 3273584 * 2
def baseEnd_3273584 : Nat := 560307351622675107081689

theorem tailTrace_3273584 : CollatzResearch.WordTrace tailWord_3273584 prefixEnd_3273584 560307351622675107081689 := by
  unfold tailWord_3273584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59698708686185863240693903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79598278248247817654258537 59698708686185863240693903)
  ·
    refine ⟨89548063029278794861040855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59698708686185863240693903 89548063029278794861040855)
    ·
      refine ⟨134322094543918192291561283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89548063029278794861040855 134322094543918192291561283)
      ·
        refine ⟨201483141815877288437341925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134322094543918192291561283 201483141815877288437341925)
        ·
          refine ⟨37778089090476991582001611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201483141815877288437341925 37778089090476991582001611)
          ·
            refine ⟨56667133635715487373002417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37778089090476991582001611 56667133635715487373002417)
            ·
              refine ⟨42500350226786615529751813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56667133635715487373002417 42500350226786615529751813)
              ·
                refine ⟨7968815667522490411828465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42500350226786615529751813 7968815667522490411828465)
                ·
                  refine ⟨5976611750641867808871349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968815667522490411828465 5976611750641867808871349)
                  ·
                    refine ⟨560307351622675107081689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5976611750641867808871349 560307351622675107081689)
                    ·
                      rfl

theorem cell23_3273584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_3273584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273584 prefixEnd_3273584 := by exact prefixLift 3273584
  have htrace : WordTrace (prefixWord ++ tailWord_3273584) baseStart_3273584 baseEnd_3273584 := by
    simpa [prefixWord, tailWord_3273584, baseEnd_3273584] using wordTrace_append hprefix tailTrace_3273584
  have hstable : (prefixWord ++ tailWord_3273584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273584).length < 2 ^ (prefixWord ++ tailWord_3273584).sum := by decide
  have hdescent : baseEnd_3273584 < baseStart_3273584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273622 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3273622 : Nat := 118140960795 + 3273622 * 2 ^ 59
def prefixEnd_3273622 : Nat := 4983230072969 + 3 ^ 40 * 3273622 * 2
def baseEnd_3273622 : Nat := 186771285236988463618877

theorem tailTrace_3273622 : CollatzResearch.WordTrace tailWord_3273622 prefixEnd_3273622 186771285236988463618877 := by
  unfold tailWord_3273622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462425209139628685704445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79599202230822705980847413 7462425209139628685704445)
  ·
    refine ⟨2798409453427360757139167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7462425209139628685704445 2798409453427360757139167)
    ·
      refine ⟨4197614180141041135708751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798409453427360757139167 4197614180141041135708751)
      ·
        refine ⟨6296421270211561703563127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197614180141041135708751 6296421270211561703563127)
        ·
          refine ⟨9444631905317342555344691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296421270211561703563127 9444631905317342555344691)
          ·
            refine ⟨14166947857976013833017037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9444631905317342555344691 14166947857976013833017037)
            ·
              refine ⟨5312605446741005187381389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14166947857976013833017037 5312605446741005187381389)
              ·
                refine ⟨1992227042527876945268021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5312605446741005187381389 1992227042527876945268021)
                ·
                  refine ⟨186771285236988463618877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992227042527876945268021 186771285236988463618877)
                  ·
                    rfl

theorem cell23_3273622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3273622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273622 prefixEnd_3273622 := by exact prefixLift 3273622
  have htrace : WordTrace (prefixWord ++ tailWord_3273622) baseStart_3273622 baseEnd_3273622 := by
    simpa [prefixWord, tailWord_3273622, baseEnd_3273622] using wordTrace_append hprefix tailTrace_3273622
  have hstable : (prefixWord ++ tailWord_3273622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273622).length < 2 ^ (prefixWord ++ tailWord_3273622).sum := by decide
  have hdescent : baseEnd_3273622 < baseStart_3273622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273641 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_3273641 : Nat := 118140960795 + 3273641 * 2 ^ 59
def prefixEnd_3273641 : Nat := 4983230072969 + 3 ^ 40 * 3273641 * 2
def baseEnd_3273641 : Nat := 1680951323265331598232305

theorem tailTrace_3273641 : CollatzResearch.WordTrace tailWord_3273641 prefixEnd_3273641 1680951323265331598232305 := by
  unfold tailWord_3273641
  simp only [CollatzResearch.WordTrace]
  refine ⟨119399496333165225216212777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79599664222110150144141851 119399496333165225216212777)
  ·
    refine ⟨89549622249873918912159583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119399496333165225216212777 89549622249873918912159583)
    ·
      refine ⟨134324433374810878368239375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89549622249873918912159583 134324433374810878368239375)
      ·
        refine ⟨201486650062216317552359063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134324433374810878368239375 201486650062216317552359063)
        ·
          refine ⟨302229975093324476328538595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201486650062216317552359063 302229975093324476328538595)
          ·
            refine ⟨453344962639986714492807893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302229975093324476328538595 453344962639986714492807893)
            ·
              refine ⟨10625272561874688620925185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 453344962639986714492807893 10625272561874688620925185)
              ·
                refine ⟨7968954421406016465693889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10625272561874688620925185 7968954421406016465693889)
                ·
                  refine ⟨5976715816054512349270417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7968954421406016465693889 5976715816054512349270417)
                  ·
                    refine ⟨4482536862040884261952813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976715816054512349270417 4482536862040884261952813)
                    ·
                      refine ⟨1680951323265331598232305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482536862040884261952813 1680951323265331598232305)
                      ·
                        rfl

theorem cell23_3273641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_3273641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273641 prefixEnd_3273641 := by exact prefixLift 3273641
  have htrace : WordTrace (prefixWord ++ tailWord_3273641) baseStart_3273641 baseEnd_3273641 := by
    simpa [prefixWord, tailWord_3273641, baseEnd_3273641] using wordTrace_append hprefix tailTrace_3273641
  have hstable : (prefixWord ++ tailWord_3273641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273641).length < 2 ^ (prefixWord ++ tailWord_3273641).sum := by decide
  have hdescent : baseEnd_3273641 < baseStart_3273641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273711 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_3273711 : Nat := 118140960795 + 3273711 * 2 ^ 59
def prefixEnd_3273711 : Nat := 4983230072969 + 3 ^ 40 * 3273711 * 2
def baseEnd_3273711 : Nat := 1680987266911146324356983

theorem tailTrace_3273711 : CollatzResearch.WordTrace tailWord_3273711 prefixEnd_3273711 1680987266911146324356983 := by
  unfold tailWord_3273711
  simp only [CollatzResearch.WordTrace]
  refine ⟨119402049442911627171260987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79601366295274418114173991 119402049442911627171260987)
  ·
    refine ⟨179103074164367440756891481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119402049442911627171260987 179103074164367440756891481)
    ·
      refine ⟨134327305623275580567668611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179103074164367440756891481 134327305623275580567668611)
      ·
        refine ⟨201490958434913370851502917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134327305623275580567668611 201490958434913370851502917)
        ·
          refine ⟨37779554706546257034656797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201490958434913370851502917 37779554706546257034656797)
          ·
            refine ⟨14167333014954846387996299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37779554706546257034656797 14167333014954846387996299)
            ·
              refine ⟨21250999522432269581994449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167333014954846387996299 21250999522432269581994449)
              ·
                refine ⟨15938249641824202186495837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21250999522432269581994449 15938249641824202186495837)
                ·
                  refine ⟨5976843615684075819935939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15938249641824202186495837 5976843615684075819935939)
                  ·
                    refine ⟨8965265423526113729903909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5976843615684075819935939 8965265423526113729903909)
                    ·
                      refine ⟨1680987266911146324356983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8965265423526113729903909 1680987266911146324356983)
                      ·
                        rfl

theorem cell23_3273711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_3273711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273711 prefixEnd_3273711 := by exact prefixLift 3273711
  have htrace : WordTrace (prefixWord ++ tailWord_3273711) baseStart_3273711 baseEnd_3273711 := by
    simpa [prefixWord, tailWord_3273711, baseEnd_3273711] using wordTrace_append hprefix tailTrace_3273711
  have hstable : (prefixWord ++ tailWord_3273711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273711).length < 2 ^ (prefixWord ++ tailWord_3273711).sum := by decide
  have hdescent : baseEnd_3273711 < baseStart_3273711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273721 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_3273721 : Nat := 118140960795 + 3273721 * 2 ^ 59
def prefixEnd_3273721 : Nat := 4983230072969 + 3 ^ 40 * 3273721 * 2
def baseEnd_3273721 : Nat := 560330800572563761743979

theorem tailTrace_3273721 : CollatzResearch.WordTrace tailWord_3273721 prefixEnd_3273721 560330800572563761743979 := by
  unfold tailWord_3273721
  simp only [CollatzResearch.WordTrace]
  refine ⟨119402414172875398879125017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79601609448583599252750011 119402414172875398879125017)
  ·
    refine ⟨89551810629656549159343763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119402414172875398879125017 89551810629656549159343763)
    ·
      refine ⟨134327715944484823739015645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89551810629656549159343763 134327715944484823739015645)
      ·
        refine ⟨50372893479181808902130867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134327715944484823739015645 50372893479181808902130867)
        ·
          refine ⟨75559340218772713353196301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50372893479181808902130867 75559340218772713353196301)
          ·
            refine ⟨28334752582039767507448613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75559340218772713353196301 28334752582039767507448613)
            ·
              refine ⟨5312766109132456407646615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28334752582039767507448613 5312766109132456407646615)
              ·
                refine ⟨7969149163698684611469923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312766109132456407646615 7969149163698684611469923)
                ·
                  refine ⟨11953723745548026917204885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7969149163698684611469923 11953723745548026917204885)
                  ·
                    refine ⟨560330800572563761743979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11953723745548026917204885 560330800572563761743979)
                    ·
                      rfl

theorem cell23_3273721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_3273721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273721 prefixEnd_3273721 := by exact prefixLift 3273721
  have htrace : WordTrace (prefixWord ++ tailWord_3273721) baseStart_3273721 baseEnd_3273721 := by
    simpa [prefixWord, tailWord_3273721, baseEnd_3273721] using wordTrace_append hprefix tailTrace_3273721
  have hstable : (prefixWord ++ tailWord_3273721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273721).length < 2 ^ (prefixWord ++ tailWord_3273721).sum := by decide
  have hdescent : baseEnd_3273721 < baseStart_3273721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273751 : List Nat := [1, 1, 3, 5, 1, 2, 10]
def baseStart_3273751 : Nat := 118140960795 + 3273751 * 2 ^ 59
def prefixEnd_3273751 : Nat := 4983230072969 + 3 ^ 40 * 3273751 * 2
def baseEnd_3273751 : Nat := 20753182791818841578479

theorem tailTrace_3273751 : CollatzResearch.WordTrace tailWord_3273751 prefixEnd_3273751 20753182791818841578479 := by
  unfold tailWord_3273751
  simp only [CollatzResearch.WordTrace]
  refine ⟨119403508362766714002717107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79602338908511142668478071 119403508362766714002717107)
  ·
    refine ⟨179105262544150071004075661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119403508362766714002717107 179105262544150071004075661)
    ·
      refine ⟨67164473454056276626528373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179105262544150071004075661 67164473454056276626528373)
      ·
        refine ⟨6296669386317775933737035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67164473454056276626528373 6296669386317775933737035)
        ·
          refine ⟨9445004079476663900605553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296669386317775933737035 9445004079476663900605553)
          ·
            refine ⟨7083753059607497925454165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9445004079476663900605553 7083753059607497925454165)
            ·
              refine ⟨20753182791818841578479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7083753059607497925454165 20753182791818841578479)
              ·
                rfl

theorem cell23_3273751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 10].length) (baseStart_3273751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273751 prefixEnd_3273751 := by exact prefixLift 3273751
  have htrace : WordTrace (prefixWord ++ tailWord_3273751) baseStart_3273751 baseEnd_3273751 := by
    simpa [prefixWord, tailWord_3273751, baseEnd_3273751] using wordTrace_append hprefix tailTrace_3273751
  have hstable : (prefixWord ++ tailWord_3273751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273751).length < 2 ^ (prefixWord ++ tailWord_3273751).sum := by decide
  have hdescent : baseEnd_3273751 < baseStart_3273751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273762 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_3273762 : Nat := 118140960795 + 3273762 * 2 ^ 59
def prefixEnd_3273762 : Nat := 4983230072969 + 3 ^ 40 * 3273762 * 2
def baseEnd_3273762 : Nat := 1681013454424525624819249

theorem tailTrace_3273762 : CollatzResearch.WordTrace tailWord_3273762 prefixEnd_3273762 1681013454424525624819249 := by
  unfold tailWord_3273762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29850977391431715720341885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79602606377151241920911693 29850977391431715720341885)
  ·
    refine ⟨11194116521786893395128207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29850977391431715720341885 11194116521786893395128207)
    ·
      refine ⟨16791174782680340092692311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11194116521786893395128207 16791174782680340092692311)
      ·
        refine ⟨25186762174020510139038467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16791174782680340092692311 25186762174020510139038467)
        ·
          refine ⟨37780143261030765208557701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25186762174020510139038467 37780143261030765208557701)
          ·
            refine ⟨7083776861443268476604569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37780143261030765208557701 7083776861443268476604569)
            ·
              refine ⟨5312832646082451357453427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083776861443268476604569 5312832646082451357453427)
              ·
                refine ⟨7969248969123677036180141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5312832646082451357453427 7969248969123677036180141)
                ·
                  refine ⟨2988468363421378888567553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7969248969123677036180141 2988468363421378888567553)
                  ·
                    refine ⟨2241351272566034166425665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2988468363421378888567553 2241351272566034166425665)
                    ·
                      refine ⟨1681013454424525624819249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241351272566034166425665 1681013454424525624819249)
                      ·
                        rfl

theorem cell23_3273762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_3273762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273762 prefixEnd_3273762 := by exact prefixLift 3273762
  have htrace : WordTrace (prefixWord ++ tailWord_3273762) baseStart_3273762 baseEnd_3273762 := by
    simpa [prefixWord, tailWord_3273762, baseEnd_3273762] using wordTrace_append hprefix tailTrace_3273762
  have hstable : (prefixWord ++ tailWord_3273762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273762).length < 2 ^ (prefixWord ++ tailWord_3273762).sum := by decide
  have hdescent : baseEnd_3273762 < baseStart_3273762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273782 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3273782 : Nat := 118140960795 + 3273782 * 2 ^ 59
def prefixEnd_3273782 : Nat := 4983230072969 + 3 ^ 40 * 3273782 * 2
def baseEnd_3273782 : Nat := 1681023724037615546569157

theorem tailTrace_3273782 : CollatzResearch.WordTrace tailWord_3273782 prefixEnd_3273782 1681023724037615546569157 := by
  unfold tailWord_3273782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462789939103400393568475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79603092683769604198063733 7462789939103400393568475)
  ·
    refine ⟨11194184908655100590352713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7462789939103400393568475 11194184908655100590352713)
    ·
      refine ⟨8395638681491325442764535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11194184908655100590352713 8395638681491325442764535)
      ·
        refine ⟨12593458022236988164146803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395638681491325442764535 12593458022236988164146803)
        ·
          refine ⟨18890187033355482246220205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593458022236988164146803 18890187033355482246220205)
          ·
            refine ⟨7083820137508305842332577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18890187033355482246220205 7083820137508305842332577)
            ·
              refine ⟨5312865103131229381749433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7083820137508305842332577 5312865103131229381749433)
              ·
                refine ⟨3984648827348422036312075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5312865103131229381749433 3984648827348422036312075)
                ·
                  refine ⟨5976973241022633054468113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984648827348422036312075 5976973241022633054468113)
                  ·
                    refine ⟨4482729930766974790851085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5976973241022633054468113 4482729930766974790851085)
                    ·
                      refine ⟨1681023724037615546569157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4482729930766974790851085 1681023724037615546569157)
                      ·
                        rfl

theorem cell23_3273782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3273782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273782 prefixEnd_3273782 := by exact prefixLift 3273782
  have htrace : WordTrace (prefixWord ++ tailWord_3273782) baseStart_3273782 baseEnd_3273782 := by
    simpa [prefixWord, tailWord_3273782, baseEnd_3273782] using wordTrace_append hprefix tailTrace_3273782
  have hstable : (prefixWord ++ tailWord_3273782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273782).length < 2 ^ (prefixWord ++ tailWord_3273782).sum := by decide
  have hdescent : baseEnd_3273782 < baseStart_3273782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273818 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2]
def baseStart_3273818 : Nat := 118140960795 + 3273818 * 2 ^ 59
def prefixEnd_3273818 : Nat := 4983230072969 + 3 ^ 40 * 3273818 * 2
def baseEnd_3273818 : Nat := 1681042209341177405718991

theorem tailTrace_3273818 : CollatzResearch.WordTrace tailWord_3273818 prefixEnd_3273818 1681042209341177405718991 := by
  unfold tailWord_3273818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29851488013380996111351527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79603968035682656296937405 29851488013380996111351527)
  ·
    refine ⟨44777232020071494167027291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29851488013380996111351527 44777232020071494167027291)
    ·
      refine ⟨67165848030107241250540937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44777232020071494167027291 67165848030107241250540937)
      ·
        refine ⟨50374386022580430937905703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67165848030107241250540937 50374386022580430937905703)
        ·
          refine ⟨75561579033870646406858555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50374386022580430937905703 75561579033870646406858555)
          ·
            refine ⟨113342368550805969610287833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75561579033870646406858555 113342368550805969610287833)
            ·
              refine ⟨85006776413104477207715875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113342368550805969610287833 85006776413104477207715875)
              ·
                refine ⟨127510164619656715811573813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85006776413104477207715875 127510164619656715811573813)
                ·
                  refine ⟨11954077933092817107335045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127510164619656715811573813 11954077933092817107335045)
                  ·
                    refine ⟨2241389612454903207625321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11954077933092817107335045 2241389612454903207625321)
                    ·
                      refine ⟨1681042209341177405718991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241389612454903207625321 1681042209341177405718991)
                      ·
                        rfl

theorem cell23_3273818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_3273818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273818 prefixEnd_3273818 := by exact prefixLift 3273818
  have htrace : WordTrace (prefixWord ++ tailWord_3273818) baseStart_3273818 baseEnd_3273818 := by
    simpa [prefixWord, tailWord_3273818, baseEnd_3273818] using wordTrace_append hprefix tailTrace_3273818
  have hstable : (prefixWord ++ tailWord_3273818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273818).length < 2 ^ (prefixWord ++ tailWord_3273818).sum := by decide
  have hdescent : baseEnd_3273818 < baseStart_3273818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273838 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3273838 : Nat := 118140960795 + 3273838 * 2 ^ 59
def prefixEnd_3273838 : Nat := 4983230072969 + 3 ^ 40 * 3273838 * 2
def baseEnd_3273838 : Nat := 1681052478954267327468899

theorem tailTrace_3273838 : CollatzResearch.WordTrace tailWord_3273838 prefixEnd_3273838 1681052478954267327468899 := by
  unfold tailWord_3273838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925835189181440982641771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79604454342301018574089445 14925835189181440982641771)
  ·
    refine ⟨22388752783772161473962657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925835189181440982641771 22388752783772161473962657)
    ·
      refine ⟨16791564587829121105471993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22388752783772161473962657 16791564587829121105471993)
      ·
        refine ⟨12593673440871840829103995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16791564587829121105471993 12593673440871840829103995)
        ·
          refine ⟨18890510161307761243655993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12593673440871840829103995 18890510161307761243655993)
          ·
            refine ⟨14167882620980820932741995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18890510161307761243655993 14167882620980820932741995)
            ·
              refine ⟨21251823931471231399112993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14167882620980820932741995 21251823931471231399112993)
              ·
                refine ⟨15938867948603423549334745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21251823931471231399112993 15938867948603423549334745)
                ·
                  refine ⟨11954150961452567662001059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15938867948603423549334745 11954150961452567662001059)
                  ·
                    refine ⟨17931226442178851493001589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11954150961452567662001059 17931226442178851493001589)
                    ·
                      refine ⟨1681052478954267327468899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17931226442178851493001589 1681052478954267327468899)
                      ·
                        rfl

theorem cell23_3273838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3273838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273838 prefixEnd_3273838 := by exact prefixLift 3273838
  have htrace : WordTrace (prefixWord ++ tailWord_3273838) baseStart_3273838 baseEnd_3273838 := by
    simpa [prefixWord, tailWord_3273838, baseEnd_3273838] using wordTrace_append hprefix tailTrace_3273838
  have hstable : (prefixWord ++ tailWord_3273838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273838).length < 2 ^ (prefixWord ++ tailWord_3273838).sum := by decide
  have hdescent : baseEnd_3273838 < baseStart_3273838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 8, 5]
def baseStart_3273871 : Nat := 118140960795 + 3273871 * 2 ^ 59
def prefixEnd_3273871 : Nat := 4983230072969 + 3 ^ 40 * 3273871 * 2
def baseEnd_3273871 : Nat := 560356474605288566118749

theorem tailTrace_3273871 : CollatzResearch.WordTrace tailWord_3273871 prefixEnd_3273871 560356474605288566118749 := by
  unfold tailWord_3273871
  simp only [CollatzResearch.WordTrace]
  refine ⟨119407885122331974497085467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79605256748221316331390311 119407885122331974497085467)
  ·
    refine ⟨179111827683497961745628201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119407885122331974497085467 179111827683497961745628201)
    ·
      refine ⟨134333870762623471309221151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179111827683497961745628201 134333870762623471309221151)
      ·
        refine ⟨201500806143935206963831727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134333870762623471309221151 201500806143935206963831727)
        ·
          refine ⟨302251209215902810445747591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201500806143935206963831727 302251209215902810445747591)
          ·
            refine ⟨453376813823854215668621387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302251209215902810445747591 453376813823854215668621387)
            ·
              refine ⟨680065220735781323502932081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453376813823854215668621387 680065220735781323502932081)
              ·
                refine ⟨510048915551835992627199061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680065220735781323502932081 510048915551835992627199061)
                ·
                  refine ⟨5977135729123078038599989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 510048915551835992627199061 5977135729123078038599989)
                  ·
                    refine ⟨560356474605288566118749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5977135729123078038599989 560356474605288566118749)
                    ·
                      rfl

theorem cell23_3273871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_3273871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273871 prefixEnd_3273871 := by exact prefixLift 3273871
  have htrace : WordTrace (prefixWord ++ tailWord_3273871) baseStart_3273871 baseEnd_3273871 := by
    simpa [prefixWord, tailWord_3273871, baseEnd_3273871] using wordTrace_append hprefix tailTrace_3273871
  have hstable : (prefixWord ++ tailWord_3273871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273871).length < 2 ^ (prefixWord ++ tailWord_3273871).sum := by decide
  have hdescent : baseEnd_3273871 < baseStart_3273871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273875 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 5]
def baseStart_3273875 : Nat := 118140960795 + 3273875 * 2 ^ 59
def prefixEnd_3273875 : Nat := 4983230072969 + 3 ^ 40 * 3273875 * 2
def baseEnd_3273875 : Nat := 186785719748720409189581

theorem tailTrace_3273875 : CollatzResearch.WordTrace tailWord_3273875 prefixEnd_3273875 186785719748720409189581 := by
  unfold tailWord_3273875
  simp only [CollatzResearch.WordTrace]
  refine ⟨119408031014317483180231079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79605354009544988786820719 119408031014317483180231079)
  ·
    refine ⟨179112046521476224770346619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119408031014317483180231079 179112046521476224770346619)
    ·
      refine ⟨268668069782214337155519929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179112046521476224770346619 268668069782214337155519929)
      ·
        refine ⟨201501052336660752866639947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268668069782214337155519929 201501052336660752866639947)
        ·
          refine ⟨302251578504991129299959921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201501052336660752866639947 302251578504991129299959921)
          ·
            refine ⟨226688683878743346974969941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302251578504991129299959921 226688683878743346974969941)
            ·
              refine ⟨2656508014204023597362929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 226688683878743346974969941 2656508014204023597362929)
              ·
                refine ⟨1992381010653017698022197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2656508014204023597362929 1992381010653017698022197)
                ·
                  refine ⟨186785719748720409189581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992381010653017698022197 186785719748720409189581)
                  ·
                    rfl

theorem cell23_3273875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 5].length) (baseStart_3273875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273875 prefixEnd_3273875 := by exact prefixLift 3273875
  have htrace : WordTrace (prefixWord ++ tailWord_3273875) baseStart_3273875 baseEnd_3273875 := by
    simpa [prefixWord, tailWord_3273875, baseEnd_3273875] using wordTrace_append hprefix tailTrace_3273875
  have hstable : (prefixWord ++ tailWord_3273875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273875).length < 2 ^ (prefixWord ++ tailWord_3273875).sum := by decide
  have hdescent : baseEnd_3273875 < baseStart_3273875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273905 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_3273905 : Nat := 118140960795 + 3273905 * 2 ^ 59
def prefixEnd_3273905 : Nat := 4983230072969 + 3 ^ 40 * 3273905 * 2
def baseEnd_3273905 : Nat := 560362294052706188443697

theorem tailTrace_3273905 : CollatzResearch.WordTrace tailWord_3273905 prefixEnd_3273905 560362294052706188443697 := by
  unfold tailWord_3273905
  simp only [CollatzResearch.WordTrace]
  refine ⟨119409125204208798303823169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79606083469472532202548779 119409125204208798303823169)
  ·
    refine ⟨89556843903156598727867377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119409125204208798303823169 89556843903156598727867377)
    ·
      refine ⟨67167632927367449045900533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89556843903156598727867377 67167632927367449045900533)
      ·
        refine ⟨6296965586940698348053175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67167632927367449045900533 6296965586940698348053175)
        ·
          refine ⟨9445448380411047522079763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6296965586940698348053175 9445448380411047522079763)
          ·
            refine ⟨14168172570616571283119645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445448380411047522079763 14168172570616571283119645)
            ·
              refine ⟨5313064713981214231169867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14168172570616571283119645 5313064713981214231169867)
              ·
                refine ⟨7969597070971821346754801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313064713981214231169867 7969597070971821346754801)
                ·
                  refine ⟨5977197803228866010066101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7969597070971821346754801 5977197803228866010066101)
                  ·
                    refine ⟨560362294052706188443697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5977197803228866010066101 560362294052706188443697)
                    ·
                      rfl

theorem cell23_3273905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_3273905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273905 prefixEnd_3273905 := by exact prefixLift 3273905
  have htrace : WordTrace (prefixWord ++ tailWord_3273905) baseStart_3273905 baseEnd_3273905 := by
    simpa [prefixWord, tailWord_3273905, baseEnd_3273905] using wordTrace_append hprefix tailTrace_3273905
  have hstable : (prefixWord ++ tailWord_3273905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273905).length < 2 ^ (prefixWord ++ tailWord_3273905).sum := by decide
  have hdescent : baseEnd_3273905 < baseStart_3273905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273938 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3273938 : Nat := 118140960795 + 3273938 * 2 ^ 59
def prefixEnd_3273938 : Nat := 4983230072969 + 3 ^ 40 * 3273938 * 2
def baseEnd_3273938 : Nat := 1681103827019716936218439

theorem tailTrace_3273938 : CollatzResearch.WordTrace tailWord_3273938 prefixEnd_3273938 1681103827019716936218439 := by
  unfold tailWord_3273938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29852582203272311234943617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79606885875392829959849645 29852582203272311234943617)
  ·
    refine ⟨22389436652454233426207713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29852582203272311234943617 22389436652454233426207713)
    ·
      refine ⟨16792077489340675069655785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22389436652454233426207713 16792077489340675069655785)
      ·
        refine ⟨12594058117005506302241839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16792077489340675069655785 12594058117005506302241839)
        ·
          refine ⟨18891087175508259453362759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12594058117005506302241839 18891087175508259453362759)
          ·
            refine ⟨28336630763262389180044139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18891087175508259453362759 28336630763262389180044139)
            ·
              refine ⟨42504946144893583770066209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28336630763262389180044139 42504946144893583770066209)
              ·
                refine ⟨31878709608670187827549657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42504946144893583770066209 31878709608670187827549657)
                ·
                  refine ⟨23909032206502640870662243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31878709608670187827549657 23909032206502640870662243)
                  ·
                    refine ⟨35863548309753961305993365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23909032206502640870662243 35863548309753961305993365)
                    ·
                      refine ⟨1681103827019716936218439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35863548309753961305993365 1681103827019716936218439)
                      ·
                        rfl

theorem cell23_3273938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3273938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273938 prefixEnd_3273938 := by exact prefixLift 3273938
  have htrace : WordTrace (prefixWord ++ tailWord_3273938) baseStart_3273938 baseEnd_3273938 := by
    simpa [prefixWord, tailWord_3273938, baseEnd_3273938] using wordTrace_append hprefix tailTrace_3273938
  have hstable : (prefixWord ++ tailWord_3273938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273938).length < 2 ^ (prefixWord ++ tailWord_3273938).sum := by decide
  have hdescent : baseEnd_3273938 < baseStart_3273938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273986 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3273986 : Nat := 118140960795 + 3273986 * 2 ^ 59
def prefixEnd_3273986 : Nat := 4983230072969 + 3 ^ 40 * 3273986 * 2
def baseEnd_3273986 : Nat := 560376158030377582806073

theorem tailTrace_3273986 : CollatzResearch.WordTrace tailWord_3273986 prefixEnd_3273986 560376158030377582806073 := by
  unfold tailWord_3273986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853019879228837284380453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79608053011276899425014541 29853019879228837284380453)
  ·
    refine ⟨5597441227355406990821335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29853019879228837284380453 5597441227355406990821335)
    ·
      refine ⟨8396161841033110486232003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597441227355406990821335 8396161841033110486232003)
      ·
        refine ⟨12594242761549665729348005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396161841033110486232003 12594242761549665729348005)
        ·
          refine ⟨2361420517790562324252751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12594242761549665729348005 2361420517790562324252751)
          ·
            refine ⟨3542130776685843486379127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361420517790562324252751 3542130776685843486379127)
            ·
              refine ⟨5313196165028765229568691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542130776685843486379127 5313196165028765229568691)
              ·
                refine ⟨7969794247543147844353037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313196165028765229568691 7969794247543147844353037)
                ·
                  refine ⟨2988672842828680441632389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7969794247543147844353037 2988672842828680441632389)
                  ·
                    refine ⟨560376158030377582806073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2988672842828680441632389 560376158030377582806073)
                    ·
                      rfl

theorem cell23_3273986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3273986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3273986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3273986 prefixEnd_3273986 := by exact prefixLift 3273986
  have htrace : WordTrace (prefixWord ++ tailWord_3273986) baseStart_3273986 baseEnd_3273986 := by
    simpa [prefixWord, tailWord_3273986, baseEnd_3273986] using wordTrace_append hprefix tailTrace_3273986
  have hstable : (prefixWord ++ tailWord_3273986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273986).length < 2 ^ (prefixWord ++ tailWord_3273986).sum := by decide
  have hdescent : baseEnd_3273986 < baseStart_3273986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274032 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4]
def baseStart_3274032 : Nat := 118140960795 + 3274032 * 2 ^ 59
def prefixEnd_3274032 : Nat := 4983230072969 + 3 ^ 40 * 3274032 * 2
def baseEnd_3274032 : Nat := 1681152094201239568443007

theorem tailTrace_3274032 : CollatzResearch.WordTrace tailWord_3274032 prefixEnd_3274032 1681152094201239568443007 := by
  unfold tailWord_3274032
  simp only [CollatzResearch.WordTrace]
  refine ⟨59706878637374349496848175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79609171516499132662464233 59706878637374349496848175)
  ·
    refine ⟨89560317956061524245272263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59706878637374349496848175 89560317956061524245272263)
    ·
      refine ⟨134340476934092286367908395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89560317956061524245272263 134340476934092286367908395)
      ·
        refine ⟨201510715401138429551862593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134340476934092286367908395 201510715401138429551862593)
        ·
          refine ⟨151133036550853822163896945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201510715401138429551862593 151133036550853822163896945)
          ·
            refine ⟨113349777413140366622922709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151133036550853822163896945 113349777413140366622922709)
            ·
              refine ⟨2656635408120477342724751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113349777413140366622922709 2656635408120477342724751)
              ·
                refine ⟨3984953112180716014087127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656635408120477342724751 3984953112180716014087127)
                ·
                  refine ⟨5977429668271074021130691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3984953112180716014087127 5977429668271074021130691)
                  ·
                    refine ⟨8966144502406611031696037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5977429668271074021130691 8966144502406611031696037)
                    ·
                      refine ⟨1681152094201239568443007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8966144502406611031696037 1681152094201239568443007)
                      ·
                        rfl

theorem cell23_3274032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4].length) (baseStart_3274032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274032 prefixEnd_3274032 := by exact prefixLift 3274032
  have htrace : WordTrace (prefixWord ++ tailWord_3274032) baseStart_3274032 baseEnd_3274032 := by
    simpa [prefixWord, tailWord_3274032, baseEnd_3274032] using wordTrace_append hprefix tailTrace_3274032
  have hstable : (prefixWord ++ tailWord_3274032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274032).length < 2 ^ (prefixWord ++ tailWord_3274032).sum := by decide
  have hdescent : baseEnd_3274032 < baseStart_3274032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274035 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5]
def baseStart_3274035 : Nat := 118140960795 + 3274035 * 2 ^ 59
def prefixEnd_3274035 : Nat := 4983230072969 + 3 ^ 40 * 3274035 * 2
def baseEnd_3274035 : Nat := 1681153634643203056705493

theorem tailTrace_3274035 : CollatzResearch.WordTrace tailWord_3274035 prefixEnd_3274035 1681153634643203056705493 := by
  unfold tailWord_3274035
  simp only [CollatzResearch.WordTrace]
  refine ⟨119413866693737830506055559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79609244462491887004037039 119413866693737830506055559)
  ·
    refine ⟨179120800040606745759083339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119413866693737830506055559 179120800040606745759083339)
    ·
      refine ⟨268681200060910118638625009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179120800040606745759083339 268681200060910118638625009)
      ·
        refine ⟨201510900045682588978968757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268681200060910118638625009 201510900045682588978968757)
        ·
          refine ⟨18891646879282742716778321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201510900045682588978968757 18891646879282742716778321)
          ·
            refine ⟨14168735159462057037583741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18891646879282742716778321 14168735159462057037583741)
            ·
              refine ⟨5313275684798271389093903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14168735159462057037583741 5313275684798271389093903)
              ·
                refine ⟨7969913527197407083640855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313275684798271389093903 7969913527197407083640855)
                ·
                  refine ⟨11954870290796110625461283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7969913527197407083640855 11954870290796110625461283)
                  ·
                    refine ⟨17932305436194165938191925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11954870290796110625461283 17932305436194165938191925)
                    ·
                      refine ⟨1681153634643203056705493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17932305436194165938191925 1681153634643203056705493)
                      ·
                        rfl

theorem cell23_3274035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_3274035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274035 prefixEnd_3274035 := by exact prefixLift 3274035
  have htrace : WordTrace (prefixWord ++ tailWord_3274035) baseStart_3274035 baseEnd_3274035 := by
    simpa [prefixWord, tailWord_3274035, baseEnd_3274035] using wordTrace_append hprefix tailTrace_3274035
  have hstable : (prefixWord ++ tailWord_3274035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274035).length < 2 ^ (prefixWord ++ tailWord_3274035).sum := by decide
  have hdescent : baseEnd_3274035 < baseStart_3274035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274042 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3274042 : Nat := 118140960795 + 3274042 * 2 ^ 59
def prefixEnd_3274042 : Nat := 4983230072969 + 3 ^ 40 * 3274042 * 2
def baseEnd_3274042 : Nat := 560385743002594843105987

theorem tailTrace_3274042 : CollatzResearch.WordTrace tailWord_3274042 prefixEnd_3274042 560385743002594843105987 := by
  unfold tailWord_3274042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853530501178117675390095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79609414669808313801040253 29853530501178117675390095)
  ·
    refine ⟨44780295751767176513085143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29853530501178117675390095 44780295751767176513085143)
    ·
      refine ⟨67170443627650764769627715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44780295751767176513085143 67170443627650764769627715)
      ·
        refine ⟨100755665441476147154441573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67170443627650764769627715 100755665441476147154441573)
        ·
          refine ⟨18891687270276777591457795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100755665441476147154441573 18891687270276777591457795)
          ·
            refine ⟨28337530905415166387186693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18891687270276777591457795 28337530905415166387186693)
            ·
              refine ⟨5313287044765343697597505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28337530905415166387186693 5313287044765343697597505)
              ·
                refine ⟨3984965283574007773198129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5313287044765343697597505 3984965283574007773198129)
                ·
                  refine ⟨2988723962680505829898597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3984965283574007773198129 2988723962680505829898597)
                  ·
                    refine ⟨560385743002594843105987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2988723962680505829898597 560385743002594843105987)
                    ·
                      rfl

theorem cell23_3274042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3274042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274042 prefixEnd_3274042 := by exact prefixLift 3274042
  have htrace : WordTrace (prefixWord ++ tailWord_3274042) baseStart_3274042 baseEnd_3274042 := by
    simpa [prefixWord, tailWord_3274042, baseEnd_3274042] using wordTrace_append hprefix tailTrace_3274042
  have hstable : (prefixWord ++ tailWord_3274042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274042).length < 2 ^ (prefixWord ++ tailWord_3274042).sum := by decide
  have hdescent : baseEnd_3274042 < baseStart_3274042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
